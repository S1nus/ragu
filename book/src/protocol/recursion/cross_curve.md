# Cross-Curve Binding

Each recursion step in Ragu produces a single proof whose circuits span both
curves of the cycle. The **native circuits** (over $\F_p$) verify the
Fiat-Shamir transcript, fold the children's revdot claims, and recompute the
accumulated polynomial evaluation. The **nested circuits** (over $\F_q$)
perform the group arithmetic that the native circuits cannot afford: adding
and scaling the commitments that accumulate the proof's polynomials. Neither
field can express the other's arithmetic cheaply, so every value shared
between the two halves must be *bound* by an explicit consistency check.
This chapter enumerates those checks and explains why each one is necessary.

```admonish warning title="Work in progress"
The recursion implementation in `ragu_pcd` is incomplete. This chapter
describes the checks present in the code today and, where the code has gaps,
the checks the design implies must exist. Inferred material is explicitly
marked as such, both inline and in the [final section](#incomplete).
```

## The Two Halves of a Proof

Ragu's recursion follows a [CycleFold](https://eprint.iacr.org/2023/1192)-inspired
asymmetric design. Application steps, header logic, and accumulator folding
live entirely on the native side; the nested side is a small, fixed set of
satellite circuits that exists only to perform deferred group operations and
to bind commitments across the curve boundary.

|  | Native half | Nested half |
|---|---|---|
| Field | $\F_p$ (`Cycle::CircuitField`) | $\F_q$ (`Cycle::ScalarField`) |
| Trace commitments live on | $\G_{host}$ (coordinates in $\F_q$) | $\G_{nested}$ (coordinates in $\F_p$) |
| Circuits | application step, `hashes_1`, `hashes_2`, `inner_collapse`, `outer_collapse`, `compute_v` | endoscaling steps, `loading`, `copying` (left/right) |
| Stages | `preamble`, `inner_error`, `outer_error`, `query`, `eval` | endoscalar, points, and eight *bridge* stages |

The pivotal fact, established in
[Nested Commitment](../prelim/nested_commitment.md), is that a commitment
always lives on the curve whose *scalar* field matches the committed
polynomial's coefficients — so its *coordinates* land in the other field of
the cycle. A commitment to a native ($\F_p$) trace is a $\G_{host}$ point
with $\F_q$ coordinates: opaque to the native circuit, but plain wire data
to the nested circuit. Symmetrically, a commitment to a nested ($\F_q$)
stage is a $\G_{nested}$ point with $\F_p$ coordinates, which the native
circuit can hash and compare natively.

## What Crosses the Boundary

Four kinds of values must be kept consistent between the two halves:

1. **Fiat-Shamir challenges.** Every challenge in the step
   ($w, y, z, \mu, \nu, \mu', \nu', x, \alpha, u, \beta$) must be bound to
   the commitments produced so far — but those commitments are $\G_{host}$
   points that the native transcript cannot absorb directly.
2. **The accumulated commitment $P$.** The step folds dozens of committed
   polynomials into a single $p(X)$ with claimed evaluation $p(u) = v$. The
   *polynomial* fold happens natively; the matching *commitment* fold
   $P = \sum_j \beta^j C_j$ is group arithmetic and must be deferred to the
   nested circuits.
3. **The folding scalar $\beta$ itself,** which is squeezed from the native
   transcript but must also drive the group fold on the nested side. It
   crosses the boundary as an [endoscalar](../extensions/endoscalar.md).
4. **The children's commitments.** Each child proof's commitments enter the
   parent's transcript and the parent's $P$ fold; the parent must be unable
   to lie about what those commitments were.
5. **The nested side's own claims,** in the opposite direction. The nested
   circuits produce revdot claims over $\F_q$ and commitments on
   $\G_{nested}$, and folding *those* requires scalar work in $\F_q$
   circuits and group work in $\F_p$ circuits — the mirror image of items
   2–3. This direction of the construction
   [is not yet built](#nested-folding).

## The Mechanism: Bonded Traces

All of the nested-side checks are built from one mechanism, an application
of [staging](../extensions/staging.md). Each stage polynomial occupies a
reserved, disjoint range of wire positions, enforced by a stage-mask revdot
claim $\revdot{\v{a}}{\v{s}} = 0$. Because the ranges are disjoint, stage
polynomials can be summed into a combined trace without interference — and
crucially, the summed stages do not all have to come from the *same* proof.

A **bonding circuit** is a circuit with no witness of its own: its trace is
defined to be a sum of existing stage polynomials, and its constraints
enforce relations *between* the wires of those stages. The `loading` circuit
bonds the current step's nested stages together; each `copying` circuit
bonds the current step's `preamble` bridge stage with a **child proof's**
bridge stages. This is how one proof's circuits get constraint-level access
to another proof's committed data: the child's stage polynomial literally
becomes part of the copying circuit's trace. Every bonding circuit
contributes an ordinary revdot claim (with $k(y) = 0$, since bonding
circuits have no public inputs), checked by the decider alongside all other
claims.

One wrinkle: two stages can only be bonded if their wire ranges don't
collide. The child's `preamble` bridge stage occupies the same range as the
current step's, so the copying circuit cannot load both. The current step's
native preamble commitment is therefore *relayed* — stashed redundantly in
the `s_prime` bridge stage (where the `loading` circuit enforces the copy is
faithful) so that a future parent's copying circuit can read it from a
non-colliding position.

## Check 1: Challenges Are Bound to Commitments

The prover cannot hash $\G_{host}$ commitments into the native Poseidon
transcript. Instead, each round's commitments are written — as raw $\F_q$
coordinate pairs — into a **bridge stage** of the nested trace. The
commitment to that bridge stage is a $\G_{nested}$ point with $\F_p$
coordinates: a [nested commitment](../prelim/nested_commitment.md) that the
native circuit absorbs directly.

The `hashes_1` and `hashes_2` circuits replay the *entire* transcript
in-circuit: starting from the domain-separation tag, they absorb each bridge
commitment (taken from the shared *unified instance*, described below) and
squeeze each challenge, forcing the challenge values in the instance to
equal the Poseidon outputs. The rounds and their contents:

| Bridge stage | Host-curve commitments it encodes | Challenge(s) squeezed after absorbing it |
|---|---|---|
| `preamble` | current native preamble; all 15 commitments of each child (see Check 2) | $w$ |
| `s_prime` | registry restrictions $m(w, x_0, Y)$, $m(w, x_1, Y)$; relayed preamble | $y$, $z$ |
| `inner_error` | native inner error terms; registry $m(w, X, y)$ | $\mu$, $\nu$ |
| `outer_error` | native outer error terms | $\mu'$, $\nu'$ |
| `ab` | folded revdot traces $A$, $B$ | $x$ |
| `query` | native query stage; registry $m(W, x, y)$ | $\alpha$ |
| `f` | quotient aggregate $f(X)$ | $u$ |
| `eval` | native eval stage | $\beta$ (as `pre_beta`) |

The transcript spans two circuits because it does not fit in one. `hashes_1`
computes through the absorption of the `inner_error` bridge commitment, then
saves the sponge state and enforces equality against a copy of that state
witnessed in the native `outer_error` stage. `hashes_2` resumes from the
witnessed state and completes the transcript. The equality check makes the
handoff sound: `hashes_2`'s challenges are forced to continue exactly the
sponge that `hashes_1` verified.

All challenges and bridge commitments live in a single shared public
instance — the **unified instance** — used by every internal native circuit.
Each of its 21 slots is *covered* (constrained) by exactly one circuit:
`hashes_1` covers $w, y, z$ and the early bridge commitments, `hashes_2` the
remaining challenges and commitments, `outer_collapse` the folded claim $c$,
and `compute_v` the evaluation $v$. A prover-side completeness assertion
guarantees no slot goes unconstrained. Internal circuit instances are
serialized with a trailing zero so that the linear term of $k(Y)$ is zero —
application headers never end in zero, which prevents substituting an
internal circuit's proof where an application step is expected.

Absorbing a nested commitment binds the challenges to the *bridge stage
contents* — the coordinate lists — not yet to the real commitments those
coordinates claim to describe. Closing that gap is the job of the next two
checks.

## Check 2: Bridge Stages Faithfully Encode the Real Commitments

Two nested bonding circuits pin the bridge stage contents down, one for the
current step and one per child.

### Loading (current step)

The `loading` circuit walks every input slot of the **points stage** — the
list of 37 points that the endoscaling circuits (Check 3) fold into $P$ —
and enforces point-equality against the bridge stages, in exactly the order
the prover's `compute_p` routine accumulates them:

* for each child, its 15 stashed commitments from the `preamble` bridge
  stage: the 11 trace commitments (application, the five internal circuits,
  and the five native stages), the two revdot traces $A$ and $B$, the
  registry commitment $m(W, x, y)$, and the child's accumulated $P$;
* the current step's registry restrictions ($m(w, x_0, Y)$, $m(w, x_1, Y)$,
  $m(w, X, y)$), current $A$ and $B$, and current $m(W, x, y)$ from their
  respective bridge stages;
* the initial accumulator, enforced equal to the $f(X)$ commitment in the
  `f` bridge stage.

It also enforces the preamble relay described above
(`s_prime` stash $=$ `preamble`'s native preamble commitment). The result:
the points that get folded into $P$ are *the same points* whose nested
commitments derived the transcript challenges.

### Copying (per child)

The `preamble` bridge stage's per-child entries are witnessed by the parent
— nothing yet stops the parent from stashing fabricated child commitments.
The `copying` circuit (one instance per side) closes this by bonding the
parent's `preamble` bridge stage with the *child proof's own* bridge stages
and enforcing, entry by entry, that each stashed commitment equals the value
the child itself committed: the child's native stage commitments against the
child's `inner_error`/`outer_error`/`query`/`eval` bridge stages, $A$ and
$B$ against the child's `ab` stage, the registry commitment against the
child's `query` stage, and the child's preamble commitment against the
child's relayed copy in `s_prime`.

The final and most important equality: the child's stashed $P$ must equal
the **last interstitial of the child's points stage** — the output of the
child's own endoscaling walk. This links each step's accumulated commitment
into the next step's accumulation, forming the inductive chain that carries
commitment correctness up the PCD tree.

To make these claims checkable, each proof retains one generation of its
children's nested stage polynomials (the points stage and six bridge
stages). Deeper ancestors' polynomials are dropped — which is only sound
once their claims have been folded into a running accumulator, machinery
that does not exist yet (see
[the missing direction](#nested-folding)).

## Check 3: The Deferred $\beta$-Fold

At the end of each step the prover folds all constituent polynomials into a
single accumulator $p(X)$ using the challenge $\beta$:

$$
p(X) = \sum_j \beta^{\,j} \, p_j(X), \qquad
P = \com(p) = \sum_j \beta^{\,j} \, C_j .
$$

The two sides of this equation are verified on different curves.

**Polynomial side (native).** The `compute_v` circuit recomputes the claimed
evaluation $v = p(u)$ entirely from *claimed evaluations*: it re-derives
$a(xz)$ and $b(x)$ through the same two-layer revdot fold the collapse
circuits verify, recomputes the quotient aggregate
$f(u) = \sum_i \alpha^{n-1-i} (p_i(u) - v_i)/(u - x_i)$ from the query-stage
claims, and then folds $f(u)$ together with the eval-stage claims using the
same Horner-in-$\beta$ walk as $p(X)$ itself. The result is constrained
equal to the $v$ slot of the unified instance.

**Commitment side (nested).** The endoscaling circuits verify the matching
fold over $\G_{host}$ points. The points stage holds the 37 points (the
$f(X)$ commitment as the initial value, then 36 inputs in `compute_p` order)
plus one *interstitial* output per step; each `EndoscalingStep` circuit
performs up to four scale-and-add operations of the Horner walk
($\mathsf{acc} \leftarrow \underline{\beta} \cdot \mathsf{acc} + C_j$, nine
circuits in total) and constrains its interstitial. The final interstitial
is the claimed $P$ — picked up by the *next* step's copying circuit, as
described above.

**The scalar $\beta$ crosses as an endoscalar.** The native transcript
squeezes `pre_beta` $\in \F_p$; `compute_v` extracts the 128-bit endoscalar
$\underline{\beta}$ from it in-circuit and uses the lifted value
$\mathsf{lift}(\underline{\beta}) \in \F_p$ for the evaluation fold. The nested
endoscalar stage witnesses the same 128 bits, and the endoscaling circuits
apply them as an endomorphism-based scalar multiplication, which agrees with
$\mathsf{lift}(\underline{\beta}) \in \F_q$ by endoscaling consistency. No
circuit directly compares the two bit strings across the curve boundary.
Instead — and *this is inferred, not yet visible as an explicit check in the
code* — a mismatched endoscalar makes the final interstitial $P$ disagree
with $\com(p)$, which must be caught by the decider's commitment
recomputation (see [Closing the Loop](#closing-the-loop)). This mirrors the
original Halo argument, where endoscalar correctness is enforced through the
commitment equality rather than bit-by-bit.

## Check 4: Child Instances Enter Through $k(y)$

The previous checks bind *commitments*; the child's public *instance* — its
challenges, its own bridge commitments, its folded claim $c$, its headers —
is bound through the instance polynomial machinery on the native side. The
parent's native `preamble` stage witnesses, per child: the child's unified
instance, the headers the child claimed for its own children, the child's
output header, and the child's circuit ID. From these, three $k(y)$ values
are recomputed in-circuit:

* `application_ky` over (left header, right header, output header) — the
  child's application-circuit instance;
* `unified_ky` over (unified instance, $0$) — the instance shared by the
  child's internal circuits;
* `unified_bridge_ky` over (unified instance, left header, right header,
  $0$) — the instance of the child's `hashes_1` circuit, which uniquely
  exposes the headers so they can be cross-checked against the application
  circuit.

The `outer_collapse` circuit enforces these recomputed values against the
copies witnessed in the `outer_error` stage, where they serve as the
$k(y)$ inputs to the two-layer claim folding verified by `inner_collapse`
and `outer_collapse`. `hashes_1` additionally enforces that both child
circuit IDs are valid roots of unity in the registry domain, so the $b$-side
of each child's application claim is looked up from a well-defined registry
row.

The cross-curve significance: the child's unified instance *contains the
child's bridge commitments*. Folding the child's claims against
`unified_ky` therefore pins the very $\G_{nested}$ points that the child's
transcript circuits hashed — the native claim folding and the nested
copying checks grip the same objects from both sides.

## The Missing Direction: Verifying the Nested Side's Fold {#nested-folding}

Accumulation on a curve cycle is symmetric: each side's accumulator
contains scalars that fold natively and commitments that must fold on the
*other* side of the cycle (see the
[split-up of the folding work](../core/accumulation/index.md#split-up-folding-work)).
Checks 1–3 implement one direction of that symmetry. The *native*
accumulator's fold is fully cross-verified: its scalar side by the collapse
circuits and `compute_v` (over $\F_p$), its commitment side by the nested
endoscaling circuits (over $\G_{host}$ points).

The mirror direction is required but **not yet built**. The nested circuits
produce an accumulator of their own: every endoscaling step, stage mask,
loading, and copying circuit contributes a revdot claim over $\F_q$, and
every nested stage carries a $\G_{nested}$ commitment. Keeping recursion
constant-size requires folding these exactly as the native claims are
folded, with the work split in mirror image:

* the *scalar* side — error terms, challenge folding, a running nested
  claim — belongs in nested ($\F_q$) circuits, mirroring
  `inner_collapse`/`outer_collapse`;
* the *commitment* side — folding the $\G_{nested}$ commitments, whose
  coordinates lie in $\F_p$ — belongs in the **native** circuits, where
  those points are native group elements, mirroring the endoscaling
  circuits.

None of this machinery exists today: there are no nested error-term stages
or collapse circuits, the proof carries no accumulated nested claim or
nested counterpart of $p(X)$ and $P$, and the native circuits hash the
bridge commitments (Check 1) but never fold them. In its place is a
stopgap: each proof retains one generation of its children's nested stage
polynomials so that the decider can check the loading and copying claims
directly, and the nested claims of deeper ancestors are simply dropped when
their proofs are fused. The stashed-$P$ chain of Check 2 keeps the
accumulated *commitments* linked from step to step, but it does not
discharge the dropped *claims* — until the symmetric fold is built, the
nested-side checks are anchored only one generation deep.

The eventual construction can be expected to mirror the native side
closely: folding challenges carried across the boundary as endoscalars,
error terms committed in dedicated nested stages, and native circuits
performing the (natively cheap) scalar multiplications that fold the bridge
and points commitments into a running nested accumulator. *That sketch is
our reading of where the design must go, not a description of code.*

## Closing the Loop {#closing-the-loop}

All of the above are constraints inside circuits; they hold only if the
corresponding revdot claims are true. The decider (the out-of-circuit
`verify`, run on the final proof with the full witness available) closes the
loop. As implemented today it checks:

* **all native revdot claims** — the raw claim
  $c = \revdot{\v{A}}{\v{B}}$, the application claim against
  `application_ky`, each internal circuit's claim against `unified_ky` (or
  `unified_bridge_ky` for `hashes_1`), and $k(y) = 0$ for every stage mask
  and final-stage mask;
* **all nested revdot claims** — $k(y) = 1$ for each endoscaling step and
  $k(y) = 0$ for the endoscalar/points/bridge masks and for the loading and
  copying bonding circuits (the latter evaluated over the retained child
  stage polynomials);
* the registry consistency evaluation
  $m(w', x, y)$ of the committed `registry_xy` polynomial at a freshly
  sampled $w'$.

The design also requires the decider to check that the *commitments* the
circuits consumed as advice match the polynomials the proof actually
carries: recomputing each trace commitment from its polynomial and comparing
against the coordinates recorded in the bridge stages and points stage, and
in particular checking $\com(p)$ against the final endoscaling interstitial.
The proof structure anticipates this — every commitment field is cached and
derivable from its polynomial — but these decider-side comparisons are not
yet implemented in `verify`. *This closure step is our inference from the
structure of the code, not yet code one can point to.* And even with it,
today's guarantees reach only one generation deep: carrying them down the
whole tree by induction additionally requires the nested-side accumulation
described in [the missing direction](#nested-folding).

## Summary of the Binding Chain

For any single host-curve commitment $C_j$ produced in a step, the chain
reads:

1. $C_j$'s coordinates are written into a bridge stage ($\F_q$ wires).
2. The bridge stage's nested commitment is absorbed by `hashes_1`/`hashes_2`,
   binding every subsequent challenge to it (Check 1).
3. The `loading` circuit forces the points-stage copy of $C_j$ to equal the
   bridge stage entry, so the same point enters the $P$ fold (Check 2).
4. The endoscaling circuits fold it into $P$ with $\underline{\beta}$; `compute_v`
   folds the matching evaluation into $v$ with $\mathsf{lift}(\underline{\beta})$
   (Check 3).
5. When this proof becomes a child, the parent's `copying` circuit forces
   the parent's stash of $C_j$ (and of $P$) to equal what this proof
   committed (Check 2), and the parent's native claim folding pins this
   proof's unified instance (Check 4).
6. The decider validates every claim in the chain, and — once complete —
   the commitment/polynomial consistency that anchors it.

As built today, steps 5–6 extend the chain only one generation. Carrying it
down the whole PCD tree requires the symmetric
[nested-side accumulation](#nested-folding), which is not yet implemented.

## Known Gaps in the Implementation {#incomplete}

```admonish warning title="Incomplete areas, as of this writing"
* The symmetric half of the accumulation is unbuilt: nested revdot claims
  are never folded (no nested error terms, collapse circuits, or running
  nested claim), and the native circuits never fold $\G_{nested}$
  commitments. Ancestors' nested claims are dropped after one generation.
  See [the missing direction](#nested-folding).
* The transcript domain-separation tag is a placeholder (`RAGU_TAG = b"FIXME"`).
* `verify` does not yet check the committed registry restrictions
  $m(w, x_0, Y)$, $m(w, x_1, Y)$, $m(w, X, y)$ (noted as a TODO in the
  code: the child $x$ challenges they depend on are not currently
  reconstructible by the decider).
* Decider-side commitment recomputation (bridge/points contents vs. actual
  commitments, $\com(p)$ vs. the final interstitial) is not implemented;
  its necessity is inferred above.
* Curve-membership checks for points-stage coordinates and boolean
  constraints for the endoscalar bits are deliberately deferred to the
  bonding ("routing") circuits and not yet all present (tracked as #172).
* `Endoscalar::extract` is under-constrained on exceptional inputs
  (unreachable for transcript-derived challenges; tracked as #765).
```
