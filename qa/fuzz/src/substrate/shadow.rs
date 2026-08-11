//! Layer 4: native shadow evaluation of generated programs.
//!
//! Evaluates a [`Program`] over plain field values, mirroring the synthesis
//! layer's semantics *exactly* — same operand clamping, same value-dependent
//! skip rules (invert-zero, divide-by-zero, non-canonical raw bytes), same
//! stack caps. The shadow is the differential oracle's "true semantics"
//! side: it knows what each gadget is *supposed* to compute, independently
//! of what constraints ragu emits.
//!
//! # Advice overrides
//!
//! [`Overrides`] models the malicious prover: each free advice site (a
//! witness-allocated preamble element, an [`Op::AllocSpecial`] /
//! [`Op::AllocRaw`] element, an [`Op::AllocSquare`] *root*, an
//! [`Op::BoolAlloc`] boolean, or an [`Op::Fold`] scale) takes its honest
//! value unless overridden. Crucially, advice is *decoupled*: overriding an
//! upstream value does not move a downstream advice site's honest value,
//! mirroring ragu, where advice wires are seeded from witness closures but
//! not constrained to their sources. Derived values always recompute from
//! their (possibly overridden) operands — overriding an `AllocSquare` root
//! moves its square.
//!
//! # Caveat: overrides can shift control flow
//!
//! Skip rules are value-dependent, so an override that changes a divisor's
//! zero-ness changes which pushes happen and therefore every later slot
//! index. Differential consumers that need slot stability across honest and
//! overridden runs must mask out [`Capabilities::VALUE_FALLIBLE`] ops (or
//! steer their generation) — the shadow itself stays faithful rather than
//! papering over the divergence.
//!
//! [`Capabilities::VALUE_FALLIBLE`]: super::Capabilities::VALUE_FALLIBLE

use ff::PrimeField;

use super::{
    Op, Program, special_value,
    synth::{BOOL_STACK_CAP, BOOL_TRUNCATE_TO, ELEM_STACK_CAP, ELEM_TRUNCATE_TO},
};

/// A free advice site discovered during shadow evaluation, identified
/// stably enough for a consumer to name it in [`Overrides`].
///
/// Element and boolean sites are identified by the stack index they occupy
/// *at creation*; fold scales (allocated but never pushed) are identified
/// by the index of their `Fold` op. Creation indices are unique as long as
/// the stack caps never trigger (guaranteed for programs of at most 60 ops,
/// since each op pushes at most two elements onto the eight preamble
/// slots); consumers relying on advice identity should bound `max_ops`
/// accordingly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdviceSlot {
    /// Element-stack slot `i` at creation: a witness-allocated preamble
    /// element, an `AllocSpecial`/`AllocRaw` element, or an `AllocSquare`
    /// root.
    Elem(usize),
    /// Boolean-stack slot `i` at creation (a `BoolAlloc`).
    Bool(usize),
    /// The scale element of the `Fold` at `program.ops[i]`.
    FoldScale(usize),
}

/// Advice overrides for a shadow run. Sites not listed keep their honest
/// values. Overrides naming constant preamble slots are ignored (constants
/// are circuit structure, not witness).
#[derive(Clone, Copy, Debug, Default)]
pub struct Overrides<'a, F> {
    /// Element-advice overrides, keyed by creation slot index.
    pub elems: &'a [(usize, F)],
    /// Boolean-advice overrides, keyed by creation slot index.
    pub bools: &'a [(usize, bool)],
    /// Fold-scale overrides, keyed by `Fold` op index.
    pub fold_scales: &'a [(usize, F)],
}

impl<F> Overrides<'_, F> {
    /// No overrides: the honest run.
    pub fn none() -> Self {
        Overrides {
            elems: &[],
            bools: &[],
            fold_scales: &[],
        }
    }
}

/// The result of a shadow evaluation.
#[derive(Clone, Debug)]
pub struct ShadowStacks<F> {
    /// The element stack after the final op.
    pub elems: Vec<F>,
    /// The boolean stack after the final op.
    pub bools: Vec<bool>,
    /// The value observed at each [`Op::Anchor`]'s target, in encounter
    /// order. In an honest run these are the constants to pin; in an
    /// overridden run, comparing them against the honest list yields the
    /// native verdict (see [`native_satisfied`]).
    pub anchors: Vec<F>,
    /// Every free advice site, in discovery order.
    pub advice: Vec<AdviceSlot>,
    /// Whether any [`Op::IsZero`] received an honestly-*zero* input. That is
    /// the one case where `is_zero`'s inverse hint becomes a genuinely free
    /// wire (the gate `0·inv = is_not_zero` is satisfied by any `inv`), which
    /// a whole-graph rank analysis would flag as a benign false positive.
    /// Distinct from "some boolean is true": a `BoolAlloc(true)` or a
    /// `BoolNot` produces a true boolean with no free hint.
    pub is_zero_degenerate: bool,
}

/// Evaluates `program` natively with the given advice overrides.
pub fn shadow_eval<F>(program: &Program, ov: Overrides<'_, F>) -> ShadowStacks<F>
where
    F: PrimeField<Repr = [u8; 32]>,
{
    let elem_ov = |slot: usize, honest: F| -> F {
        ov.elems
            .iter()
            .find(|(s, _)| *s == slot)
            .map_or(honest, |(_, v)| *v)
    };
    let bool_ov = |slot: usize, honest: bool| -> bool {
        ov.bools
            .iter()
            .find(|(s, _)| *s == slot)
            .map_or(honest, |(_, v)| *v)
    };
    let scale_ov = |op_idx: usize, honest: F| -> F {
        ov.fold_scales
            .iter()
            .find(|(s, _)| *s == op_idx)
            .map_or(honest, |(_, v)| *v)
    };

    let mut advice = Vec::new();
    let mut elems: Vec<F> = Vec::with_capacity(super::Preamble::LEN);
    for (i, v) in program.preamble.values::<F>().into_iter().enumerate() {
        if program.preamble.is_constant(i) {
            elems.push(v);
        } else {
            advice.push(AdviceSlot::Elem(i));
            elems.push(elem_ov(i, v));
        }
    }
    let mut bools: Vec<bool> = Vec::new();
    let mut anchors = Vec::new();
    let mut is_zero_degenerate = false;

    for (idx, op) in program.ops.iter().enumerate() {
        let elen = elems.len();
        let blen = bools.len();
        if elen == 0 {
            break;
        }

        match *op {
            Op::Add(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                elems.push(elems[a] + elems[b]);
            }
            Op::Sub(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                elems.push(elems[a] - elems[b]);
            }
            Op::Mul(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                elems.push(elems[a] * elems[b]);
            }
            Op::Square(a) => {
                let a = a as usize % elen;
                elems.push(elems[a].square());
            }
            Op::Double(a) => {
                let a = a as usize % elen;
                elems.push(elems[a].double());
            }
            Op::Negate(a) => {
                let a = a as usize % elen;
                elems.push(-elems[a]);
            }
            Op::Invert(a) => {
                let a = a as usize % elen;
                // Mirrors the gadget: inverting zero fails, skipping the push.
                let inv: Option<F> = elems[a].invert().into();
                if let Some(inv) = inv {
                    elems.push(inv);
                }
            }
            Op::IsZero(a) => {
                let a = a as usize % elen;
                let is_zero = elems[a] == F::ZERO;
                // A zero input frees the inverse hint (see the field doc).
                is_zero_degenerate |= is_zero;
                bools.push(is_zero);
            }
            Op::Divide(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                // Mirrors the gadget: a zero divisor fails enforce_nonzero,
                // skipping the push.
                let inv: Option<F> = elems[b].invert().into();
                if let Some(inv) = inv {
                    elems.push(elems[a] * inv);
                }
            }
            Op::Scale(a, c) => {
                let a = a as usize % elen;
                elems.push(elems[a] * F::from(c));
            }
            Op::Fold(a, b, s) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                advice.push(AdviceSlot::FoldScale(idx));
                let scale = scale_ov(idx, F::from(s));
                elems.push(elems[a] * scale + elems[b]);
            }
            Op::AllocConst(v) => {
                elems.push(F::from(v));
            }
            Op::AllocSpecial(sidx) => {
                let slot = elems.len();
                advice.push(AdviceSlot::Elem(slot));
                elems.push(elem_ov(slot, special_value(sidx)));
            }
            Op::AllocRaw(bytes) => {
                // Mirrors the gadget: non-canonical bytes skip the push.
                let v: Option<F> = F::from_repr(bytes).into();
                if let Some(honest) = v {
                    let slot = elems.len();
                    advice.push(AdviceSlot::Elem(slot));
                    elems.push(elem_ov(slot, honest));
                }
            }
            Op::AllocSquare(v) => {
                let root_slot = elems.len();
                advice.push(AdviceSlot::Elem(root_slot));
                // The root is decoupled advice: its honest value comes from
                // the payload, and only its own override moves it. The
                // square always recomputes from the (possibly overridden)
                // root.
                let root = elem_ov(root_slot, F::from(v));
                elems.push(root);
                elems.push(root.square());
            }
            Op::BoolAlloc(v) => {
                let slot = bools.len();
                advice.push(AdviceSlot::Bool(slot));
                bools.push(bool_ov(slot, v));
            }
            Op::BoolNot(a) => {
                if blen > 0 {
                    let a = a as usize % blen;
                    bools.push(!bools[a]);
                }
            }
            Op::BoolAnd(a, b) => {
                if blen > 0 {
                    let (a, b) = (a as usize % blen, b as usize % blen);
                    bools.push(bools[a] && bools[b]);
                }
            }
            Op::ConditionalSelect(cond, a, b) => {
                if blen > 0 {
                    let cond = cond as usize % blen;
                    let (a, b) = (a as usize % elen, b as usize % elen);
                    // `Boolean::conditional_select` returns `a` when false
                    // and `b` when true.
                    elems.push(if bools[cond] { elems[b] } else { elems[a] });
                }
            }
            Op::Anchor(a) => {
                let slot = a as usize % elen;
                anchors.push(elems[slot]);
            }
        }

        if elems.len() > ELEM_STACK_CAP {
            elems.truncate(ELEM_TRUNCATE_TO);
        }
        if bools.len() > BOOL_STACK_CAP {
            bools.truncate(BOOL_TRUNCATE_TO);
        }
    }

    ShadowStacks {
        elems,
        bools,
        anchors,
        advice,
        is_zero_degenerate,
    }
}

/// The native oracle verdict: with `ov` applied, does every anchor still
/// observe its honest value?
pub fn native_satisfied<F>(program: &Program, honest_anchors: &[F], ov: Overrides<'_, F>) -> bool
where
    F: PrimeField<Repr = [u8; 32]>,
{
    shadow_eval(program, ov).anchors == honest_anchors
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use ragu_core::maybe::Maybe;
    use ragu_pasta::Fp;
    use ragu_primitives::{Simulator, allocator::Standard};

    use super::{
        super::{Capabilities, Limits, OpSet, Preamble, program_strategy, synthesize},
        *,
    };

    fn preamble() -> Preamble {
        Preamble {
            seeds: [3, 5, 7, 11],
            large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
            special_seeds: [1, 11],
            constant_mask: 0b0000_0101,
        }
    }

    /// The shadow's honest element and boolean stacks agree with the
    /// Simulator's gadget values for arbitrary generated programs — the
    /// core fidelity property of the mirror.
    #[test]
    fn proptest_shadow_agrees_with_simulator() {
        let strategy = program_strategy(
            OpSet::ALL.without(Capabilities::ANCHORS),
            Limits::default().max_ops,
        );
        proptest!(|(program in strategy)| {
            let shadow = shadow_eval::<Fp>(&program, Overrides::none());
            let sim = Simulator::<Fp>::simulate((), |dr, _| {
                let stacks = synthesize(dr, &mut Standard::new(), &program, &[])?;
                let values: Vec<Fp> =
                    stacks.elems.iter().map(|e| *e.value().take()).collect();
                let bvalues: Vec<bool> =
                    stacks.bools.iter().map(|b| b.value().take()).collect();
                assert_eq!(values, shadow.elems, "element stacks diverge");
                assert_eq!(bvalues, shadow.bools, "boolean stacks diverge");
                Ok(())
            });
            prop_assert!(sim.is_ok());
        });
    }

    /// Anchors observed by an honest shadow run are satisfiable pins for
    /// synthesis, for arbitrary anchored programs.
    #[test]
    fn proptest_honest_anchors_satisfiable() {
        let strategy = program_strategy(OpSet::ALL, Limits::default().max_ops);
        proptest!(|(program in strategy)| {
            let honest = shadow_eval::<Fp>(&program, Overrides::none());
            let sim = Simulator::<Fp>::simulate((), |dr, _| {
                synthesize(dr, &mut Standard::new(), &program, &honest.anchors)?;
                Ok(())
            });
            prop_assert!(sim.is_ok(), "honest anchors must be satisfiable");
        });
    }

    /// AllocSquare roots are decoupled: an upstream override does not move
    /// the root, while a root override moves the square.
    #[test]
    fn alloc_square_decoupling() {
        let program = Program {
            preamble: preamble(),
            ops: vec![Op::AllocSquare(6), Op::Anchor(9)],
        };
        let honest = shadow_eval::<Fp>(&program, Overrides::none());
        // Slots: preamble 0..8, root at 8, square at 9.
        assert_eq!(honest.elems[8], Fp::from(6));
        assert_eq!(honest.elems[9], Fp::from(36));
        assert!(honest.advice.contains(&AdviceSlot::Elem(8)));
        assert_eq!(honest.anchors, vec![Fp::from(36)]);

        // Overriding an upstream witness slot does not move the root.
        let upstream = shadow_eval::<Fp>(
            &program,
            Overrides {
                elems: &[(1, Fp::from(999))],
                ..Overrides::none()
            },
        );
        assert_eq!(upstream.elems[8], Fp::from(6));
        assert!(native_satisfied(
            &program,
            &honest.anchors,
            Overrides {
                elems: &[(1, Fp::from(999))],
                ..Overrides::none()
            }
        ));

        // Overriding the root moves the square, violating the anchor.
        let cheat = Overrides {
            elems: &[(8, Fp::from(7))],
            ..Overrides::none()
        };
        let cheated = shadow_eval::<Fp>(&program, cheat);
        assert_eq!(cheated.elems[9], Fp::from(49));
        assert!(!native_satisfied(&program, &honest.anchors, cheat));
    }

    /// Constant preamble slots ignore overrides; witness slots accept them.
    #[test]
    fn constant_slots_not_overridable() {
        let program = Program {
            preamble: preamble(), // slots 0 and 2 constant
            ops: vec![],
        };
        let ov = Overrides {
            elems: &[(0, Fp::from(123)), (1, Fp::from(456))],
            ..Overrides::none()
        };
        let s = shadow_eval::<Fp>(&program, ov);
        assert_eq!(s.elems[0], Fp::from(3), "constant slot must not move");
        assert_eq!(s.elems[1], Fp::from(456), "witness slot must move");
        assert!(!s.advice.contains(&AdviceSlot::Elem(0)));
        assert!(s.advice.contains(&AdviceSlot::Elem(1)));
    }
}
