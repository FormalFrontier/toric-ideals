# Mathematical references and credits

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
2025 draft, Exercise 3.6.F) motivates the Hankel presentation, not the Jacobson
criterion. No source text or PDF is reproduced, and the citation implies
neither participation nor endorsement. The curve definitions, descent,
terminal-exponent uniqueness and normalization proofs are Formal Frontier
work. The Jacobson proof follows the constant-coefficient augmentation argument
of this library's Noetherian module and uses the Jacobson providers in
`Mathlib.RingTheory.Jacobson.Ring`. The left coefficient-module criteria use
this library's coordinate-axis surjection, the polynomial coefficient-module
criteria in [multivariate-polynomials](https://github.com/FormalFrontier/multivariate-polynomials),
and Mathlib's Noetherian and Artinian module theory. Coefficient-module
finiteness uses the same coordinate-axis surjection and directly reuses
Mathlib's `Polynomial.not_finite`, surjective-image finiteness and finiteness
of subsingleton modules. Raw-map surjectivity combines this library's
exponent-image divisibility criterion and coefficient-vanishing API with
Mathlib's `Finsupp.mapDomain_surjective`, monoid-algebra coefficient equivalence
and subsingleton-target surjectivity. Freeness over the raw source composes
this library's semiring injectivity criterion and degree-one map identity with
Mathlib's free-module faithfulness, faithful algebra-map injectivity, singleton
basis and empty basis APIs. Coefficient faithful flatness reuses the existing
coefficient augmentation and freeness, together with Mathlib's nontrivial
free-module result and transport from nonempty-index finitely supported
functions for zero coefficients. Its tensor clients directly reuse Mathlib's
faithfully-flat injectivity reflection and canonical unit injection. The
quotient-map flatness proof uses the origin derivative on a two-generated quotient ideal and a linear
coefficient functional on the target to exhibit the obstruction to flatness
of the quotient parametrization. That argument combines this library's
exponent-image criterion and coefficient-vanishing API with Mathlib's partial
derivations, additive quotient descent, tensor maps and flat-module
preservation of injections. The boundary degrees use the bijective quotient
projection and this library's raw-map flatness criterion. This flatness
classification is independent of the cited source motivation for the Hankel
presentation. The
augmentation-kernel description reuses the evaluation-ideal theorem in
multivariate-polynomials and Mathlib's ideal map/comap APIs; the coefficient
quotient clients instantiate Mathlib's first isomorphism theorem. Homogeneous-basis
coefficient change uses the library's characteristic representative laws and
Hankel kernel theorem, together with Mathlib's polynomial and quotient maps;
independent terminal choices are compared through their images. The Hankel
quotient dimension formula combines this library's endpoint map with the
injective-integral dimension theorem in
[minimal-primes](https://github.com/FormalFrontier/minimal-primes/blob/537058e2a3f4610d3126f22af057a1f6cd96c886/MinimalPrimes/RingTheory/KrullDimension/Integral.lean),
whose finite-chain proof uses incomparability, lying-over and going-up,
and Mathlib's Noetherian polynomial dimension formula. The code depends on
mathlib, multivariate-polynomials and minimal-primes (all Apache-2.0; see the
[complete minimal-primes license](https://github.com/FormalFrontier/minimal-primes/blob/537058e2a3f4610d3126f22af057a1f6cd96c886/LICENSE)).
Lean and doc-gen4 are separately credited tools, not bundled sources. The Markdown adapter follows earlier
Formal Frontier documentation tooling.
Contributions use AI-assisted development and independent agent review;
`Authors: Formal Frontier Agents` is collective author credit, not a
copyright-ownership claim.
