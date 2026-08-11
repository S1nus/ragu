//! Shared substrate for randomly generated gadget programs.
//!
//! Six fuzz targets in `qa/fuzz` independently grew the same idea: decode a
//! byte stream into a program over a stack of [`Element`]s (and [`Boolean`]s),
//! synthesize it through a [`Driver`], and check an invariant — robustness,
//! driver-vs-driver agreement, witness cheating, constraint-identity
//! acceptance, or patcher-style under-constraint hunting. Four of them carried
//! byte-identical copies of the op vocabulary; the other two carried subsets
//! plus a pinning op. This module is the single home for that machinery.
//!
//! # Layers
//!
//! Consumers pick the layers they need; nothing forces the full stack:
//!
//! 1. **AST** ([`Op`], [`OpKind`], [`Capabilities`], [`OpSet`], [`Preamble`]):
//!    a field-agnostic program representation with per-op capability metadata
//!    and per-consumer capability masks.
//! 2. **Decoding / generation**: a byte-stream decoder with *decode-time
//!    clamping* — ops outside the consumer's [`OpSet`] are remapped onto
//!    allowed ones, so any byte stream is a valid program for any consumer and
//!    corpora can cross-pollinate between fuzz targets — plus `proptest`
//!    strategies over the same AST for deterministic in-tree properties.
//! 3. **Synthesis**: one driver-generic interpreter emitting real gadget
//!    calls, with consumer-owned policy for fallible ops.
//! 4. **Native shadow**: an `F`-level evaluator mirroring each op's true
//!    semantics, for differential oracles.
//! 5. **Circuit wrapper**: a generated program as a registerable
//!    `Circuit`, with a satisfying-witness mode for constraint-level oracles.
//!
//! Layers 3–5 are introduced by their respective consumers' migrations; this
//! file currently provides layers 1 and 2.
//!
//! # Oracle policy is not generator policy
//!
//! The same op means different things to different harnesses: a robustness
//! target *wants* [`Op::Invert`] to receive zero and assert `Err`-not-panic; a
//! satisfying-witness consumer needs it steered to succeed; a metamorphic
//! target needs two drivers to fail identically. The substrate exposes raw
//! ops and capability metadata; what "expected" means stays in each harness.
//!
//! [`Element`]: ragu_primitives::Element
//! [`Boolean`]: ragu_primitives::Boolean
//! [`Driver`]: ragu_core::drivers::Driver

use ff::PrimeField;
use proptest::{prelude::*, sample::select, strategy::BoxedStrategy};

mod circuit;
#[cfg(test)]
mod integration_tests;
mod shadow;
mod synth;

pub use circuit::{ProgramCircuit, anchor_tail, steer};
pub use shadow::{AdviceSlot, Overrides, ShadowStacks, native_satisfied, shadow_eval};
pub use synth::{
    BOOL_STACK_CAP, BOOL_TRUNCATE_TO, ELEM_STACK_CAP, ELEM_TRUNCATE_TO, Stacks, synthesize,
    synthesize_with_hook, synthesize_with_witness,
};

/// One instruction of a generated gadget program.
///
/// Operand fields index the element stack (or, for boolean-typed operands,
/// the boolean stack) and are reduced modulo the live stack length at
/// execution time, so any payload is well-formed. Value payloads are
/// field-agnostic seeds (`u64`, special-value indices, or raw canonical
/// bytes) interpreted by the synthesis and shadow layers.
///
/// The vocabulary is the union of every `qa/fuzz` op-stream target:
/// the 19 ops shared by `fuzz_element_ops` / `fuzz_witness_cheat` /
/// `fuzz_driver_metamorphic` / `fuzz_witness_coverage`, plus [`Op::Anchor`]
/// from the patcher family (`fuzz_circuit_cheat` / `fuzz_advice_patcher`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// Push `elems[a] + elems[b]`.
    Add(u8, u8),
    /// Push `elems[a] - elems[b]`.
    Sub(u8, u8),
    /// Push `elems[a] * elems[b]` (one gate, two copy constraints).
    Mul(u8, u8),
    /// Push `elems[a]^2`.
    Square(u8),
    /// Push `2 * elems[a]`.
    Double(u8),
    /// Push `-elems[a]`.
    Negate(u8),
    /// Push `elems[a]^{-1}`; fails on zero.
    Invert(u8),
    /// Push a [`Boolean`](ragu_primitives::Boolean) indicating
    /// `elems[a] == 0` onto the boolean stack.
    IsZero(u8),
    /// Push `elems[a] / elems[b]`; fails when `elems[b]` is zero.
    Divide(u8, u8),
    /// Push `elems[a] * c` for the constant `c` (a virtual wire; no gate).
    Scale(u8, u64),
    /// Push `elems[a] * s + elems[b]` via Horner folding, where `s` is a
    /// freshly allocated scale element seeded from the `u64`.
    Fold(u8, u8, u64),
    /// Push the constant `v` (a virtual wire; no allocation).
    AllocConst(u64),
    /// Allocate an element holding [`special_value`] of the index.
    AllocSpecial(u8),
    /// Allocate `(root, root^2)` in a single gate via `Element::alloc_square`,
    /// with the root seeded from the `u64`. Pushes both.
    AllocSquare(u64),
    /// Allocate an element whose value is the 32-byte chunk interpreted as a
    /// canonical field element; skipped when non-canonical. Lets fuzzer
    /// dictionary entries land directly in the witness.
    AllocRaw([u8; 32]),
    /// Allocate a boolean with the given value onto the boolean stack.
    BoolAlloc(bool),
    /// Push `!bools[a]` onto the boolean stack.
    BoolNot(u8),
    /// Push `bools[a] & bools[b]` onto the boolean stack.
    BoolAnd(u8, u8),
    /// Push `bools[cond] ? elems[a] : elems[b]`.
    ConditionalSelect(u8, u8, u8),
    /// Pin `elems[a]` to its honest value via `enforce_zero(elem - const)`.
    ///
    /// The pinned constant is captured from an honest evaluation by the
    /// consumer (see the synthesis layer); anchors are what give the
    /// constraint-level oracles their rejection power.
    Anchor(u8),
}

/// Fieldless discriminant of [`Op`], used for capability lookups and
/// [`OpSet`] membership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum OpKind {
    /// See [`Op::Add`].
    Add,
    /// See [`Op::Sub`].
    Sub,
    /// See [`Op::Mul`].
    Mul,
    /// See [`Op::Square`].
    Square,
    /// See [`Op::Double`].
    Double,
    /// See [`Op::Negate`].
    Negate,
    /// See [`Op::Invert`].
    Invert,
    /// See [`Op::IsZero`].
    IsZero,
    /// See [`Op::Divide`].
    Divide,
    /// See [`Op::Scale`].
    Scale,
    /// See [`Op::Fold`].
    Fold,
    /// See [`Op::AllocConst`].
    AllocConst,
    /// See [`Op::AllocSpecial`].
    AllocSpecial,
    /// See [`Op::AllocSquare`].
    AllocSquare,
    /// See [`Op::AllocRaw`].
    AllocRaw,
    /// See [`Op::BoolAlloc`].
    BoolAlloc,
    /// See [`Op::BoolNot`].
    BoolNot,
    /// See [`Op::BoolAnd`].
    BoolAnd,
    /// See [`Op::ConditionalSelect`].
    ConditionalSelect,
    /// See [`Op::Anchor`].
    Anchor,
}

impl OpKind {
    /// Every kind, in stable encoding order. The position of a kind in this
    /// array is its wire-format discriminant (see the decoding layer), so
    /// **append new kinds at the end** — reordering breaks corpus encodings.
    pub const ALL: [OpKind; 20] = [
        OpKind::Add,
        OpKind::Sub,
        OpKind::Mul,
        OpKind::Square,
        OpKind::Double,
        OpKind::Negate,
        OpKind::Invert,
        OpKind::IsZero,
        OpKind::Divide,
        OpKind::Scale,
        OpKind::Fold,
        OpKind::AllocConst,
        OpKind::AllocSpecial,
        OpKind::AllocSquare,
        OpKind::AllocRaw,
        OpKind::BoolAlloc,
        OpKind::BoolNot,
        OpKind::BoolAnd,
        OpKind::ConditionalSelect,
        OpKind::Anchor,
    ];

    /// Capability metadata for this kind.
    pub const fn capabilities(self) -> Capabilities {
        match self {
            OpKind::Add | OpKind::Sub | OpKind::Double | OpKind::Negate | OpKind::Scale => {
                Capabilities::SHADOWED
            }
            OpKind::Mul | OpKind::Square => Capabilities::SHADOWED.union(Capabilities::GATES),
            OpKind::Invert => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::Divide => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::IsZero => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::BOOLEAN),
            OpKind::Fold => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocConst => Capabilities::SHADOWED,
            OpKind::AllocSpecial => Capabilities::SHADOWED.union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocSquare => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocRaw => Capabilities::SHADOWED
                .union(Capabilities::ALLOCATES_ADVICE)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::BoolAlloc => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::BoolNot => Capabilities::SHADOWED.union(Capabilities::BOOLEAN),
            OpKind::BoolAnd => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES),
            OpKind::ConditionalSelect => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES),
            OpKind::Anchor => Capabilities::SHADOWED.union(Capabilities::ANCHORS),
        }
    }
}

impl Op {
    /// The fieldless discriminant of this op.
    pub const fn kind(self) -> OpKind {
        match self {
            Op::Add(..) => OpKind::Add,
            Op::Sub(..) => OpKind::Sub,
            Op::Mul(..) => OpKind::Mul,
            Op::Square(..) => OpKind::Square,
            Op::Double(..) => OpKind::Double,
            Op::Negate(..) => OpKind::Negate,
            Op::Invert(..) => OpKind::Invert,
            Op::IsZero(..) => OpKind::IsZero,
            Op::Divide(..) => OpKind::Divide,
            Op::Scale(..) => OpKind::Scale,
            Op::Fold(..) => OpKind::Fold,
            Op::AllocConst(..) => OpKind::AllocConst,
            Op::AllocSpecial(..) => OpKind::AllocSpecial,
            Op::AllocSquare(..) => OpKind::AllocSquare,
            Op::AllocRaw(..) => OpKind::AllocRaw,
            Op::BoolAlloc(..) => OpKind::BoolAlloc,
            Op::BoolNot(..) => OpKind::BoolNot,
            Op::BoolAnd(..) => OpKind::BoolAnd,
            Op::ConditionalSelect(..) => OpKind::ConditionalSelect,
            Op::Anchor(..) => OpKind::Anchor,
        }
    }
}

/// Per-op capability flags consulted when intersecting an op vocabulary with
/// a consumer's requirements.
///
/// Flags describe what an op *does or needs*, not whether a consumer wants
/// it; consumers express wants via [`OpSet`] masks built from these flags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capabilities(u16);

impl Capabilities {
    /// The op has a faithful native (out-of-circuit) mirror in the shadow
    /// evaluator. Differential oracles require this; the invariant-based
    /// oracle does not. Every current op is shadowed; the flag exists so
    /// future routine-backed ops can opt out without API change.
    pub const SHADOWED: Capabilities = Capabilities(1 << 0);

    /// The op can fail for *value* reasons (inverting zero, dividing by
    /// zero, non-canonical raw bytes) — as opposed to the API-level
    /// fallibility of gate allocation, which never fires under honest
    /// witnesses. Satisfying-witness consumers must steer or exclude these.
    pub const VALUE_FALLIBLE: Capabilities = Capabilities(1 << 1);

    /// The op allocates fresh *advice* — wires a malicious prover chooses
    /// freely. These are the patcher family's mutation targets.
    pub const ALLOCATES_ADVICE: Capabilities = Capabilities(1 << 2);

    /// The op reads or writes the boolean stack.
    pub const BOOLEAN: Capabilities = Capabilities(1 << 3);

    /// The op emits at least one multiplication gate.
    pub const GATES: Capabilities = Capabilities(1 << 4);

    /// The op emits a pinning constraint against an honest constant
    /// ([`Op::Anchor`]). Only meaningful to consumers that compute honest
    /// evaluations first.
    pub const ANCHORS: Capabilities = Capabilities(1 << 5);

    /// The op synthesizes through a [`Routine`](ragu_core::routines::Routine).
    /// No current op does; reserved for Poseidon-style grammar growth, where
    /// drivers without routine support must exclude it.
    pub const ROUTINES: Capabilities = Capabilities(1 << 6);

    /// The empty capability set.
    pub const fn empty() -> Capabilities {
        Capabilities(0)
    }

    /// The union of two capability sets.
    pub const fn union(self, other: Capabilities) -> Capabilities {
        Capabilities(self.0 | other.0)
    }

    /// Whether every flag in `other` is present in `self`.
    pub const fn contains(self, other: Capabilities) -> bool {
        self.0 & other.0 == other.0
    }

    /// Whether any flag in `other` is present in `self`.
    pub const fn intersects(self, other: Capabilities) -> bool {
        self.0 & other.0 != 0
    }
}

/// A consumer's allowed-op mask: which [`OpKind`]s the decoder may emit.
///
/// Masks are how "one rich union grammar, callers choose" works in practice:
/// the decoder clamps disallowed kinds onto allowed ones at decode time, so
/// the byte encoding — and therefore the corpus — stays shared across
/// consumers with different masks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpSet(u32);

impl OpSet {
    /// Every op in the vocabulary. The robustness targets' mask.
    pub const ALL: OpSet = OpSet((1 << OpKind::ALL.len()) - 1);

    /// Builds a set from a predicate over kinds.
    pub fn filtered(allow: impl Fn(OpKind) -> bool) -> OpSet {
        let mut bits = 0u32;
        for (i, kind) in OpKind::ALL.iter().enumerate() {
            if allow(*kind) {
                bits |= 1 << i;
            }
        }
        OpSet(bits)
    }

    /// Ops excluded: removes every kind whose capabilities intersect `caps`.
    pub fn without(self, caps: Capabilities) -> OpSet {
        let mut bits = self.0;
        for (i, kind) in OpKind::ALL.iter().enumerate() {
            if kind.capabilities().intersects(caps) {
                bits &= !(1 << i);
            }
        }
        OpSet(bits)
    }

    /// Whether `kind` is allowed by this set.
    pub fn allows(self, kind: OpKind) -> bool {
        let idx = OpKind::ALL
            .iter()
            .position(|k| *k == kind)
            .expect("OpKind::ALL is exhaustive over the enum, so every kind has a position");
        self.0 & (1 << idx) != 0
    }

    /// The allowed kinds, in stable encoding order. Decoders index into this
    /// to clamp a raw discriminant onto an allowed kind.
    pub fn allowed_kinds(self) -> impl Iterator<Item = OpKind> {
        OpKind::ALL
            .into_iter()
            .enumerate()
            .filter(move |(i, _)| self.0 & (1 << i) != 0)
            .map(|(_, k)| k)
    }

    /// Number of allowed kinds.
    pub fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    /// Whether no kinds are allowed.
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
}

/// The shared recipe for a program's initial element stack, lifted from the
/// four robustness targets: plain `u64` seeds, multi-limb large values,
/// special-value entries, and a mask choosing constant vs. witness
/// allocation per slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Preamble {
    /// Plain seeds, each becoming one initial element.
    pub seeds: [u64; 4],
    /// Multi-limb seeds combined as `l0 + l1·2^32 + l2·2^48 + l3·2^56`,
    /// reaching values outside the `u64` range.
    pub large_seeds: [[u64; 4]; 2],
    /// Indices into [`special_value`] for two extra initial elements.
    pub special_seeds: [u8; 2],
    /// If bit `i % 8` is set, initial element `i` is created as a constant
    /// (virtual wire) instead of an allocated witness wire.
    pub constant_mask: u8,
}

impl Preamble {
    /// Number of initial elements a preamble produces.
    pub const LEN: usize = 4 + 2 + 2;

    /// The initial element values, in stack order.
    pub fn values<F: PrimeField>(&self) -> [F; Self::LEN] {
        let mut out = [F::ZERO; Self::LEN];
        let mut i = 0;
        for seed in self.seeds {
            out[i] = F::from(seed);
            i += 1;
        }
        for ls in self.large_seeds {
            out[i] = F::from(ls[0])
                + F::from(ls[1]) * F::from(1u64 << 32)
                + F::from(ls[2]) * F::from(1u64 << 48)
                + F::from(ls[3]) * F::from(1u64 << 56);
            i += 1;
        }
        for ss in self.special_seeds {
            out[i] = special_value(ss);
            i += 1;
        }
        out
    }

    /// Whether initial element `i` is a constant (vs. an allocated witness
    /// wire).
    pub fn is_constant(&self, i: usize) -> bool {
        self.constant_mask & (1 << (i % 8)) != 0
    }
}

/// A complete generated program: the initial stack recipe plus the op
/// stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    /// Recipe for the initial element stack.
    pub preamble: Preamble,
    /// The instruction stream, executed in order.
    pub ops: Vec<Op>,
}

/// Decoding limits, owned by each consumer.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Maximum number of ops to decode; further bytes are ignored.
    pub max_ops: usize,
}

impl Default for Limits {
    /// The historical bound shared by the existing fuzz targets.
    fn default() -> Self {
        Limits { max_ops: 48 }
    }
}

/// Cursor over the input bytes. Reads past the end yield zeros, which makes
/// decoding *total*: every byte slice is a valid program for every mask.
struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        Cursor { data, pos: 0 }
    }

    /// Whether any real (non-padding) bytes remain.
    fn has_bytes(&self) -> bool {
        self.pos < self.data.len()
    }

    fn u8(&mut self) -> u8 {
        let v = self.data.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        v
    }

    fn u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];
        for b in &mut bytes {
            *b = self.u8();
        }
        u64::from_le_bytes(bytes)
    }

    fn bytes32(&mut self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for b in &mut bytes {
            *b = self.u8();
        }
        bytes
    }
}

impl Program {
    /// Decodes a program from raw bytes — typically libFuzzer's input —
    /// restricted to the consumer's [`OpSet`].
    ///
    /// # Wire format
    ///
    /// A fixed-size preamble, then ops until the bytes run out or
    /// [`Limits::max_ops`] is reached:
    ///
    /// * preamble: 4 × `u64` seeds, 2 × 4 × `u64` large seeds (all
    ///   little-endian), 2 special-value bytes, 1 constant-mask byte;
    /// * each op: one kind byte `k`, then that kind's payload (`u8` operands
    ///   one byte each, `u64` seeds little-endian, booleans one byte, raw
    ///   values 32 bytes).
    ///
    /// The kind byte resolves as `OpKind::ALL[k % 20]`; when the mask
    /// disallows that kind it is *clamped* to `allowed[k % allowed.len()]`
    /// instead of rejected. Decoding is total — reads past the end of the
    /// input yield zero bytes (though no new op starts once the input is
    /// exhausted) — so every byte stream is a valid program under every
    /// non-empty mask, and corpora transfer between consumers with different
    /// masks. Payload widths follow the clamped kind, so the same bytes may
    /// decode to different op counts under different masks: corpus transfer
    /// is semantic (interesting byte patterns carry over), not positional.
    /// The kind table is append-only (see [`OpKind::ALL`]), which keeps old
    /// corpora meaningful as the vocabulary grows.
    ///
    /// An empty `set` yields a program with no ops.
    pub fn decode(data: &[u8], set: OpSet, limits: Limits) -> Program {
        let mut cur = Cursor::new(data);

        let mut seeds = [0u64; 4];
        for s in &mut seeds {
            *s = cur.u64();
        }
        let mut large_seeds = [[0u64; 4]; 2];
        for ls in &mut large_seeds {
            for l in ls.iter_mut() {
                *l = cur.u64();
            }
        }
        let special_seeds = [cur.u8(), cur.u8()];
        let constant_mask = cur.u8();
        let preamble = Preamble {
            seeds,
            large_seeds,
            special_seeds,
            constant_mask,
        };

        let allowed: Vec<OpKind> = set.allowed_kinds().collect();
        let mut ops = Vec::new();
        while cur.has_bytes() && ops.len() < limits.max_ops && !allowed.is_empty() {
            let k = cur.u8();
            let mut kind = OpKind::ALL[k as usize % OpKind::ALL.len()];
            if !set.allows(kind) {
                kind = allowed[k as usize % allowed.len()];
            }
            ops.push(match kind {
                OpKind::Add => Op::Add(cur.u8(), cur.u8()),
                OpKind::Sub => Op::Sub(cur.u8(), cur.u8()),
                OpKind::Mul => Op::Mul(cur.u8(), cur.u8()),
                OpKind::Square => Op::Square(cur.u8()),
                OpKind::Double => Op::Double(cur.u8()),
                OpKind::Negate => Op::Negate(cur.u8()),
                OpKind::Invert => Op::Invert(cur.u8()),
                OpKind::IsZero => Op::IsZero(cur.u8()),
                OpKind::Divide => Op::Divide(cur.u8(), cur.u8()),
                OpKind::Scale => Op::Scale(cur.u8(), cur.u64()),
                OpKind::Fold => Op::Fold(cur.u8(), cur.u8(), cur.u64()),
                OpKind::AllocConst => Op::AllocConst(cur.u64()),
                OpKind::AllocSpecial => Op::AllocSpecial(cur.u8()),
                OpKind::AllocSquare => Op::AllocSquare(cur.u64()),
                OpKind::AllocRaw => Op::AllocRaw(cur.bytes32()),
                OpKind::BoolAlloc => Op::BoolAlloc(cur.u8() & 1 == 1),
                OpKind::BoolNot => Op::BoolNot(cur.u8()),
                OpKind::BoolAnd => Op::BoolAnd(cur.u8(), cur.u8()),
                OpKind::ConditionalSelect => Op::ConditionalSelect(cur.u8(), cur.u8(), cur.u8()),
                OpKind::Anchor => Op::Anchor(cur.u8()),
            });
        }

        Program { preamble, ops }
    }

    /// Encodes this program into the wire format accepted by
    /// [`Program::decode`]. Useful for writing seed corpora and for
    /// round-trip testing.
    ///
    /// `decode(encode(p), set, limits)` reproduces `p` exactly whenever
    /// every op kind in `p` is allowed by `set` and `p.ops.len()` is within
    /// `limits` (kind bytes are written as positions in [`OpKind::ALL`], so
    /// they survive any mask that allows them).
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for s in self.preamble.seeds {
            out.extend_from_slice(&s.to_le_bytes());
        }
        for ls in self.preamble.large_seeds {
            for l in ls {
                out.extend_from_slice(&l.to_le_bytes());
            }
        }
        out.extend_from_slice(&self.preamble.special_seeds);
        out.push(self.preamble.constant_mask);

        for op in &self.ops {
            let kind_byte = OpKind::ALL
                .iter()
                .position(|k| *k == op.kind())
                .expect("OpKind::ALL is exhaustive") as u8;
            out.push(kind_byte);
            match *op {
                Op::Add(a, b) | Op::Sub(a, b) | Op::Mul(a, b) | Op::Divide(a, b) => {
                    out.push(a);
                    out.push(b);
                }
                Op::Square(a)
                | Op::Double(a)
                | Op::Negate(a)
                | Op::Invert(a)
                | Op::IsZero(a)
                | Op::AllocSpecial(a)
                | Op::BoolNot(a)
                | Op::Anchor(a) => out.push(a),
                Op::Scale(a, c) => {
                    out.push(a);
                    out.extend_from_slice(&c.to_le_bytes());
                }
                Op::Fold(a, b, s) => {
                    out.push(a);
                    out.push(b);
                    out.extend_from_slice(&s.to_le_bytes());
                }
                Op::AllocConst(v) | Op::AllocSquare(v) => {
                    out.extend_from_slice(&v.to_le_bytes());
                }
                Op::AllocRaw(bytes) => out.extend_from_slice(&bytes),
                Op::BoolAlloc(v) => out.push(v as u8),
                Op::BoolAnd(a, b) => {
                    out.push(a);
                    out.push(b);
                }
                Op::ConditionalSelect(c, a, b) => {
                    out.push(c);
                    out.push(a);
                    out.push(b);
                }
            }
        }
        out
    }
}

/// Structurally interesting field values, indexed by a fuzzer-chosen byte.
///
/// The 16-variant superset used by the robustness targets (the patcher
/// family previously used an 8-variant subset).
pub fn special_value<F: PrimeField>(idx: u8) -> F {
    match idx % 16 {
        0 => F::ZERO,
        1 => F::ONE,
        2 => -F::ONE,     // p - 1
        3 => -F::from(2), // p - 2
        4 => F::TWO_INV,  // (p + 1) / 2
        5 => F::from(2),
        6 => F::from(3),
        7 => F::from(7),
        8 => F::ROOT_OF_UNITY,                      // 2-adic primitive root
        9 => F::ROOT_OF_UNITY.square(),             // (S-1)-adic primitive root
        10 => F::ROOT_OF_UNITY.pow_vartime([4u64]), // (S-2)-adic primitive root
        11 => F::MULTIPLICATIVE_GENERATOR,          // smallest generator
        12 => F::MULTIPLICATIVE_GENERATOR.square(),
        13 => F::from(1u64 << 32), // 2^32 boundary
        14 => F::from(1u64 << 48), // 2^48 boundary
        _ => F::from(u64::MAX),    // large value near 2^64
    }
}

/// Proptest strategy for one op drawn from `set`.
///
/// The deterministic in-tree counterpart of [`Program::decode`]: properties
/// over generated programs run under plain `cargo test`, while the byte
/// decoder serves coverage-guided fuzzing.
///
/// # Panics
///
/// Panics if `set` is empty.
pub fn op_strategy(set: OpSet) -> BoxedStrategy<Op> {
    let kinds: Vec<OpKind> = set.allowed_kinds().collect();
    assert!(!kinds.is_empty(), "op_strategy requires a non-empty OpSet");
    select(kinds)
        .prop_flat_map(|kind| match kind {
            OpKind::Add => (any::<u8>(), any::<u8>())
                .prop_map(|(a, b)| Op::Add(a, b))
                .boxed(),
            OpKind::Sub => (any::<u8>(), any::<u8>())
                .prop_map(|(a, b)| Op::Sub(a, b))
                .boxed(),
            OpKind::Mul => (any::<u8>(), any::<u8>())
                .prop_map(|(a, b)| Op::Mul(a, b))
                .boxed(),
            OpKind::Square => any::<u8>().prop_map(Op::Square).boxed(),
            OpKind::Double => any::<u8>().prop_map(Op::Double).boxed(),
            OpKind::Negate => any::<u8>().prop_map(Op::Negate).boxed(),
            OpKind::Invert => any::<u8>().prop_map(Op::Invert).boxed(),
            OpKind::IsZero => any::<u8>().prop_map(Op::IsZero).boxed(),
            OpKind::Divide => (any::<u8>(), any::<u8>())
                .prop_map(|(a, b)| Op::Divide(a, b))
                .boxed(),
            OpKind::Scale => (any::<u8>(), any::<u64>())
                .prop_map(|(a, c)| Op::Scale(a, c))
                .boxed(),
            OpKind::Fold => (any::<u8>(), any::<u8>(), any::<u64>())
                .prop_map(|(a, b, s)| Op::Fold(a, b, s))
                .boxed(),
            OpKind::AllocConst => any::<u64>().prop_map(Op::AllocConst).boxed(),
            OpKind::AllocSpecial => any::<u8>().prop_map(Op::AllocSpecial).boxed(),
            OpKind::AllocSquare => any::<u64>().prop_map(Op::AllocSquare).boxed(),
            OpKind::AllocRaw => any::<[u8; 32]>().prop_map(Op::AllocRaw).boxed(),
            OpKind::BoolAlloc => any::<bool>().prop_map(Op::BoolAlloc).boxed(),
            OpKind::BoolNot => any::<u8>().prop_map(Op::BoolNot).boxed(),
            OpKind::BoolAnd => (any::<u8>(), any::<u8>())
                .prop_map(|(a, b)| Op::BoolAnd(a, b))
                .boxed(),
            OpKind::ConditionalSelect => (any::<u8>(), any::<u8>(), any::<u8>())
                .prop_map(|(c, a, b)| Op::ConditionalSelect(c, a, b))
                .boxed(),
            OpKind::Anchor => any::<u8>().prop_map(Op::Anchor).boxed(),
        })
        .boxed()
}

/// Proptest strategy for a [`Preamble`], mixing edge-biased and broad seeds.
pub fn preamble_strategy() -> BoxedStrategy<Preamble> {
    (
        any::<[u64; 4]>(),
        any::<[[u64; 4]; 2]>(),
        any::<[u8; 2]>(),
        any::<u8>(),
    )
        .prop_map(
            |(seeds, large_seeds, special_seeds, constant_mask)| Preamble {
                seeds,
                large_seeds,
                special_seeds,
                constant_mask,
            },
        )
        .boxed()
}

/// Proptest strategy for a whole [`Program`] over `set`, with up to
/// `max_ops` ops.
///
/// # Panics
///
/// Panics if `set` is empty.
pub fn program_strategy(set: OpSet, max_ops: usize) -> BoxedStrategy<Program> {
    (
        preamble_strategy(),
        proptest::collection::vec(op_strategy(set), 0..=max_ops),
    )
        .prop_map(|(preamble, ops)| Program { preamble, ops })
        .boxed()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `OpKind::ALL` must cover every variant exactly once; the encoding
    /// order is load-bearing for corpus stability.
    #[test]
    fn all_kinds_exhaustive_and_unique() {
        for (i, a) in OpKind::ALL.iter().enumerate() {
            for b in OpKind::ALL.iter().skip(i + 1) {
                assert_ne!(a, b, "duplicate kind in OpKind::ALL");
            }
        }
        // Compile-time exhaustiveness: a match over every variant. Adding a
        // variant without extending `ALL` fails the uniqueness/position
        // assertions in `opset_round_trips` below.
        for kind in OpKind::ALL {
            match kind {
                OpKind::Add
                | OpKind::Sub
                | OpKind::Mul
                | OpKind::Square
                | OpKind::Double
                | OpKind::Negate
                | OpKind::Invert
                | OpKind::IsZero
                | OpKind::Divide
                | OpKind::Scale
                | OpKind::Fold
                | OpKind::AllocConst
                | OpKind::AllocSpecial
                | OpKind::AllocSquare
                | OpKind::AllocRaw
                | OpKind::BoolAlloc
                | OpKind::BoolNot
                | OpKind::BoolAnd
                | OpKind::ConditionalSelect
                | OpKind::Anchor => {}
            }
        }
    }

    #[test]
    fn opset_round_trips() {
        assert_eq!(OpSet::ALL.len(), OpKind::ALL.len());
        for kind in OpKind::ALL {
            assert!(OpSet::ALL.allows(kind));
        }

        let no_bools = OpSet::ALL.without(Capabilities::BOOLEAN);
        let bool_kinds = OpKind::ALL
            .iter()
            .filter(|k| k.capabilities().intersects(Capabilities::BOOLEAN))
            .count();
        assert_eq!(no_bools.len(), OpKind::ALL.len() - bool_kinds);
        for kind in OpKind::ALL {
            assert_eq!(
                no_bools.allows(kind),
                !kind.capabilities().intersects(Capabilities::BOOLEAN),
            );
        }

        let filtered = OpSet::filtered(|k| matches!(k, OpKind::Add | OpKind::Anchor));
        assert_eq!(filtered.len(), 2);
        assert!(filtered.allows(OpKind::Add));
        assert!(filtered.allows(OpKind::Anchor));
        assert!(!filtered.allows(OpKind::Mul));
        assert!(OpSet::filtered(|_| false).is_empty());
    }

    #[test]
    fn capability_table_sanity() {
        // Every current op is shadowed.
        for kind in OpKind::ALL {
            assert!(
                kind.capabilities().contains(Capabilities::SHADOWED),
                "{kind:?} should be shadow-supported",
            );
        }
        // The value-fallible set is exactly the three ops with value-dependent
        // failure modes.
        let fallible: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::VALUE_FALLIBLE))
            .collect();
        assert_eq!(fallible, [OpKind::Invert, OpKind::Divide, OpKind::AllocRaw],);
        // Anchor is the only anchoring op, and the patcher mutation targets
        // are exactly the advice allocators.
        let anchors: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::ANCHORS))
            .collect();
        assert_eq!(anchors, [OpKind::Anchor]);
        let advice: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::ALLOCATES_ADVICE))
            .collect();
        assert_eq!(
            advice,
            [
                OpKind::Fold,
                OpKind::AllocSpecial,
                OpKind::AllocSquare,
                OpKind::AllocRaw,
                OpKind::BoolAlloc,
            ],
        );
    }

    /// One op of every kind, for encode/decode and kind-table tests.
    fn one_of_each() -> [Op; 20] {
        [
            Op::Add(0, 1),
            Op::Sub(2, 3),
            Op::Mul(4, 5),
            Op::Square(6),
            Op::Double(7),
            Op::Negate(8),
            Op::Invert(9),
            Op::IsZero(10),
            Op::Divide(11, 12),
            Op::Scale(13, 0xdead_beef_dead_beef),
            Op::Fold(14, 15, 42),
            Op::AllocConst(7),
            Op::AllocSpecial(3),
            Op::AllocSquare(u64::MAX),
            Op::AllocRaw([0xab; 32]),
            Op::BoolAlloc(true),
            Op::BoolNot(16),
            Op::BoolAnd(17, 18),
            Op::ConditionalSelect(19, 20, 21),
            Op::Anchor(22),
        ]
    }

    #[test]
    fn encode_decode_round_trip() {
        let program = Program {
            preamble: Preamble {
                seeds: [1, 2, u64::MAX, 0],
                large_seeds: [[5, 6, 7, 8], [9, 10, 11, 12]],
                special_seeds: [13, 14],
                constant_mask: 0b1010_1010,
            },
            ops: one_of_each().to_vec(),
        };
        let decoded = Program::decode(
            &program.encode(),
            OpSet::ALL,
            Limits {
                max_ops: program.ops.len(),
            },
        );
        assert_eq!(decoded, program);
    }

    #[test]
    fn decode_clamps_to_mask() {
        let program = Program {
            preamble: Preamble {
                seeds: [0; 4],
                large_seeds: [[0; 4]; 2],
                special_seeds: [0; 2],
                constant_mask: 0,
            },
            ops: one_of_each().to_vec(),
        };
        let bytes = program.encode();

        let linear_only = OpSet::filtered(|k| {
            matches!(
                k,
                OpKind::Add | OpKind::Sub | OpKind::Double | OpKind::Negate
            )
        });
        // Payload widths follow the *clamped* kind, so the op count may
        // differ from the original under a restricting mask; what must hold
        // is that decoding stays total and emits only allowed kinds.
        let decoded = Program::decode(&bytes, linear_only, Limits::default());
        assert!(!decoded.ops.is_empty());
        for op in &decoded.ops {
            assert!(
                linear_only.allows(op.kind()),
                "decoder emitted disallowed op {op:?}",
            );
        }

        // The same bytes under the full mask reproduce the original kinds.
        let full = Program::decode(&bytes, OpSet::ALL, Limits::default());
        assert_eq!(full.ops, program.ops);
    }

    #[test]
    fn decode_is_total() {
        // Arbitrary junk, truncated payloads, and the empty input all decode
        // without panicking and respect limits.
        for data in [
            &[][..],
            &[0xff][..],
            &[9][..],           // Scale kind byte, payload truncated
            &[14, 1, 2, 3][..], // AllocRaw kind byte, payload truncated
            &[1, 2, 3, 4, 5, 6, 7][..],
        ] {
            let p = Program::decode(data, OpSet::ALL, Limits::default());
            assert!(p.ops.len() <= Limits::default().max_ops);
        }
        let junk: Vec<u8> = (0..=255).cycle().take(4096).collect();
        let p = Program::decode(&junk, OpSet::ALL, Limits { max_ops: 7 });
        assert_eq!(p.ops.len(), 7);

        // Truncated payload bytes read as zero: a lone Scale kind byte (after
        // a full preamble) decodes to Scale(0, 0).
        let mut bytes = vec![0u8; 99];
        bytes.push(9); // OpKind::ALL[9] == Scale
        let p = Program::decode(&bytes, OpSet::ALL, Limits::default());
        assert_eq!(p.ops, vec![Op::Scale(0, 0)]);

        // The empty mask decodes to no ops.
        let p = Program::decode(&junk, OpSet::filtered(|_| false), Limits::default());
        assert!(p.ops.is_empty());
    }

    proptest::proptest! {
        /// Every byte stream decodes to allowed-only ops under any mask
        /// drawn from a few representative masks.
        #[test]
        fn proptest_decode_total_and_masked(
            data in proptest::collection::vec(any::<u8>(), 0..2048),
            mask_choice in 0u8..4,
        ) {
            let set = match mask_choice {
                0 => OpSet::ALL,
                1 => OpSet::ALL.without(Capabilities::BOOLEAN),
                2 => OpSet::ALL.without(Capabilities::VALUE_FALLIBLE),
                _ => OpSet::filtered(|k| matches!(k, OpKind::Add | OpKind::Mul | OpKind::Anchor)),
            };
            let p = Program::decode(&data, set, Limits::default());
            proptest::prop_assert!(p.ops.len() <= Limits::default().max_ops);
            for op in &p.ops {
                proptest::prop_assert!(set.allows(op.kind()));
            }
        }

        /// Strategy-generated programs round-trip through the wire format.
        #[test]
        fn proptest_strategy_encode_decode(
            program in program_strategy(OpSet::ALL, 48),
        ) {
            let decoded = Program::decode(&program.encode(), OpSet::ALL, Limits::default());
            proptest::prop_assert_eq!(decoded, program);
        }

        /// Masked strategies only generate allowed ops.
        #[test]
        fn proptest_strategy_respects_mask(
            program in program_strategy(OpSet::ALL.without(Capabilities::BOOLEAN), 32),
        ) {
            let set = OpSet::ALL.without(Capabilities::BOOLEAN);
            for op in &program.ops {
                proptest::prop_assert!(set.allows(op.kind()));
            }
        }
    }

    #[test]
    fn op_kind_agreement() {
        let ops = [
            Op::Add(0, 1),
            Op::Sub(0, 1),
            Op::Mul(0, 1),
            Op::Square(0),
            Op::Double(0),
            Op::Negate(0),
            Op::Invert(0),
            Op::IsZero(0),
            Op::Divide(0, 1),
            Op::Scale(0, 2),
            Op::Fold(0, 1, 2),
            Op::AllocConst(2),
            Op::AllocSpecial(3),
            Op::AllocSquare(2),
            Op::AllocRaw([0; 32]),
            Op::BoolAlloc(true),
            Op::BoolNot(0),
            Op::BoolAnd(0, 1),
            Op::ConditionalSelect(0, 1, 2),
            Op::Anchor(0),
        ];
        for (op, kind) in ops.iter().zip(OpKind::ALL) {
            assert_eq!(op.kind(), kind);
        }
    }
}
