# Circuits

> Normal circuit, multi-stage circuits etc.

The [`ragu_circuits`] crate turns arithmetic circuit definitions into
polynomials. For the underlying protocol-level arithmetization see the
[arithmetization chapter](../protocol/core/arithmetization.md); for the
multi-stage extension layered on top see the
[staging implementation](staging.md).

## The `Circuit` Trait

[`Circuit<F>`][circuit-trait] is the core abstraction. Any type that
implements it declares an `Instance` type (public data the verifier
possesses), a `Witness` type (secret data the prover supplies), an
`Output` type serialized into the $k(Y)$ instance polynomial, and an
`Aux` type for auxiliary data useful in future synthesis passes.

Two methods reflect each other.
[`instance`][circuit-instance] derives the expected output from public
data alone; [`witness`][circuit-witness] performs the full computation
and returns both the output gadget and any auxiliary data. Both take a
[`Driver`], the same circuit code runs whether the driver is counting
constraints, evaluating the wiring polynomial, or computing a real
trace.

[`CircuitExt`][circuit-ext] is blanket-implemented for every
`Circuit<F>`. Its [`trace`][circuit-trace] method runs `witness` on an
evaluating driver to produce a [`Trace`] of raw gate values; its
[`ky`][circuit-ky] method evaluates the instance polynomial $k(y)$ at a
concrete challenge $y$.

## Maybe Values

Explains the `Maybe<T>` abstraction for type-level encoding of optional
witness data, enabling zero-cost optimizations.

Circuit code runs under drivers that may or may not need concrete
values. `Maybe<T>` resolves this at the type level: drivers with
`Always` carry real values, while drivers with `Empty` use a
zero-sized stand-in and never execute value-producing closures. This
lets the same circuit code serve witness generation, instance
evaluation, metrics, and wiring evaluation without runtime branching.

## Witness Structure

The prover's witness $\v{r}$ is defined by
$\v{a}, \v{b}, \v{c} \in \F^n$, where $n = 2^k$. Individual elements of
this witness are known as _wires_—specifically, _allocated_ wires, because
the prover must commit to them and thus they exist at a cost. They are
referred to as "wires," rather than "variables," because they principally
behave as inputs and outputs to multiplication gates.

Ragu defines the witness $\v{r}$ as the concatenation
$\v{c} || \v{\hat{b}} || \v{a} || \v{0^n}$, which is an example of a
[structured vector](../protocol/prelim/structured_vectors.md).

### Virtual Wires

The left-hand side of all constraints are linear combinations of
elements within $\v{a}, \v{b}, \v{c}$. Any linear combination of wires can
itself be considered a _virtual_ wire (as opposed to an allocated wire)
which imposes no cost on the protocol.

### `ONE`

Circuits always have the specially-labeled `ONE` wire $\v{c}_0 = 1$. This
is enforced with the
[constraint](../protocol/core/arithmetization.md#constraints)
$\v{c}_0 = \v{k}_0 = 1$.

[`ragu_circuits`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/
[circuit-trait]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html
[circuit-instance]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html#tymethod.instance
[circuit-witness]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html#tymethod.witness
[circuit-ext]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html
[circuit-trace]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html#method.trace
[circuit-ky]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html#method.ky
[`Driver`]: https://docs.rs/ragu_core/latest/ragu_core/drivers/trait.Driver.html
[`Trace`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/struct.Trace.html
