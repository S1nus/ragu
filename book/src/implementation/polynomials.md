# Polynomial Management

Ragu's prover works primarily with polynomials: constructing them from
circuit descriptions, multiplying them via FFTs, and decomposing their
products into forms the verifier can check. This chapter covers the
wiring polynomial that encodes an arithmetic circuit, the synthesis
process that builds it incrementally, and the low-level polynomial
utilities in [`ragu_arithmetic`] that support these operations.

## Wiring Polynomials

Individual arithmetic circuits are defined by the
[structured vector](../protocol/prelim/structured_vectors.md)
$\v{s} \in \F^{4n}$ that describes the
[constraints](../protocol/core/arithmetization.md#constraints)
enforced over the witness, given a concrete choice of random challenge $y$.
This vector is the coefficient vector of a special polynomial

$$
s(X, Y) = \sum\limits_{j=0}^{4n - 1} Y^j \Big(
      \sum_{i = 0}^{n - 1} (\v{u})_{i,j} X^{2n - 1 - i}
    + \sum_{i = 0}^{n - 1} (\v{v})_{i,j} X^{2n + i}
    + \sum_{i = 0}^{n - 1} (\v{w})_{i,j} X^{4n - 1 - i}
\Big)
$$

at the restriction $Y = y$. This is known as the "wiring polynomial."

## Synthesis {#synthesis}

Ragu will directly synthesize circuit code into (partial) evaluations of
the reduced wiring polynomial. There are two operations that influence this
polynomial:

* `enforce_zero` creates a
  [constraint](../protocol/core/arithmetization.md#constraints)
  that enforces that a linear combination of wires must equal zero. This
  produces a new term in $Y^j$ for some unused $j$.
* `mul` creates new wires $(a, b, c)$ that must satisfy a
  [gate]
  $ab = c$. This allocates (or assigns) the corresponding powers
  $(X^{2n + i}, X^{2n - 1 - i}, X^i)$ for some unused $i$.

**Importantly, this synthesis process is procedural.** Any contiguous
sequence of `enforce_zero` and `mul` operations is defined by the
polynomials $g, h \in \F[X, Y]$ and transforms $s(X, Y)$ into $s'(X, Y)$
where for some $i, j$

$$
s'(X, Y) = s(X, Y) + Y^j (X^i g(X, Y) + h(X, Y)).
$$

Here, only $h(X, Y)$ varies depending on wires not allocated within that
sequence of operations. In many cases, $h$ is either extremely sparse (and
so trivial to compute as necessary) or is used in multiple repeated
sequences. Any repeated sequence produces the same $g$ polynomial by
definition, and so its evaluation can be fully memoized for future
invocations of an identical sequence of operations by simply scaling by
$X^i Y^j$.

[gate]: ../protocol/core/arithmetization.md#gates

## Polynomial Arithmetic

The synthesis machinery above relies on standard polynomial operations
provided by the [`ragu_arithmetic`] crate. These operate on coefficient
vectors in ascending
degree order: the slice $[c_0, c_1, \ldots, c_n]$ represents the
polynomial
$c_0 + c_1 X + \cdots + c_n X^n$.

### Evaluation and Inner Products

[`eval`] evaluates a polynomial at a point using Horner's method.
[`dot`] computes the inner product $\langle \v{a}, \v{b} \rangle$ of
two equal-length coefficient vectors. These helpers provide the scalar
operations underlying polynomial evaluation and inner-product checks.

### Polynomial Multiplication

[`poly_mul`] computes the coefficient convolution of two polynomials,
implemented using FFTs. Given polynomials $a(X)$ of degree $d_a$ and
$b(X)$ of degree $d_b$, it produces $c(X) = a(X) \cdot b(X)$ of degree
$d_a + d_b$. Internally, both inputs are zero-padded to a power-of-two
length, transformed into evaluation form via [`Domain::fft`], multiplied
pointwise, and transformed back via [`Domain::ifft`].

The output is written into a caller-supplied `&mut Vec<F>` so that
repeated multiplications can reuse a single allocation.

[`ragu_arithmetic`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/
[`eval`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.eval.html
[`dot`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.dot.html
[`poly_mul`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.poly_mul.html
[`Domain::fft`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/struct.Domain.html#method.fft
[`Domain::ifft`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/struct.Domain.html#method.ifft
