# Mathematical references and credits

Uniform monomial-evaluation kernels use
`MonoidAlgebra.uniform_fiber_span_of_fg` from
[group-rings](https://github.com/FormalFrontier/group-rings) for one finite family
of same-fiber exponent pairs independent of the coefficient ring. The polynomial
argument combines that theorem with the weighted-evaluation identity in
`ToricIdeals.MonoidAlgebra.Evaluation`, Mathlib's finite-generation results for
natural exponent vectors, its additive/multiplicative type-tag algebra
equivalences, and ideal map/comap transport. GroupRings is also the canonical home
of the coefficientwise fiber-normalization theorems in the root
`AddMonoidAlgebra` namespace; ToricIdeals re-exports these Formal Frontier Agents
results with compatibility aliases rather than a duplicate proof. GroupRings is
Apache-2.0; see its [complete license](https://github.com/FormalFrontier/group-rings/blob/main/LICENSE).

Arithmetic gcd recognition reuses Mathlib's natural-number set gcd and forward
conductor theorem in `Mathlib.NumberTheory.FrobeniusNumber`, by Alex Zhao, Daniel
Buth, Sebastian Meier and Junyan Xu. Its converse follows the adjacent-member
divisibility argument in Mathlib's `exists_frobeniusNumber_iff`, applied to
consecutive large multiples of the proposed arithmetic step. The numerical
semigroup example reuses Mathlib's two-generator Frobenius theorem. No source
text or implementation is reproduced.

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
2025 draft, Exercise 3.6.F) motivates the Hankel presentation, not the Jacobson
criterion. No source text or PDF is reproduced, and the citation implies
neither participation nor endorsement. The curve definitions, descent,
terminal-exponent uniqueness and normalization proofs are Formal Frontier
work. The coprime natural-weight kernel presentation reuses this library's
all-coefficient binomial congruence and the coefficientwise normalization theorem
re-exported from GroupRings, with imagewise preimage choice and Mathlib's
natural-weight and monoid-algebra pushforward APIs. The gcd-reduced natural-weight presentation reuses that
coprime theorem with Mathlib's coprime gcd quotients, injectivity of natural
exponent multiplication, monoid-algebra pushforward composition and invariance
of kernels under injective postcomposition. The Jacobson proof follows the
constant-coefficient augmentation argument of this library's Noetherian module
and uses the Jacobson providers in
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
mathlib, multivariate-polynomials, minimal-primes, integral-closure,
coherent-modules, group-theory and group-rings (all Apache-2.0; see the
[complete coherent-modules license](https://github.com/FormalFrontier/coherent-modules/blob/b9bb233399aab0f864a2a1a1bb3d414dff530812/LICENSE),
[complete group-theory license](https://github.com/FormalFrontier/group-theory/blob/07948c9888686ade711654c1433c3efb2652e1aa/LICENSE), and the
[complete minimal-primes license](https://github.com/FormalFrontier/minimal-primes/blob/537058e2a3f4610d3126f22af057a1f6cd96c886/LICENSE)
and [complete integral-closure license](https://github.com/FormalFrontier/integral-closure/blob/3e89fa94dfa32e9d4f4c43fca8dd15462686201c/LICENSE)).
Base-ring normality of monomial exponent subalgebras directly applies
`IsIntegrallyClosed.of_linearRetract` from the Formal Frontier integral-closure
library. The scalar retraction is Mathlib's polynomial evaluation at zero,
composed with the subalgebra inclusion and converted to a linear map. The
polynomial evaluation development credits Chris Hughes, Johannes Hölzl,
Kim Morrison and Jens Wagemaker; the algebra-homomorphism API credits Kenny Lau
and Yury Kudryashov.
Lean and doc-gen4 are separately credited tools, not bundled sources. The Markdown adapter follows earlier
Formal Frontier documentation tooling.
Contributions use AI-assisted development and independent agent review;
`Authors: Formal Frontier Agents` is collective author credit, not a
copyright-ownership claim.

## Monomial support, spans and finite covers

The monomial-subalgebra and three generic finite-cover interfaces have their
canonical home in
[GroupRings](https://github.com/FormalFrontier/group-rings/tree/8a10fb8c1285227a36501fa50206a0bed05fc98a/GroupRings/MonoidAlgebra).
Their lineage is the multivariate-polynomial support proof, the monoid-algebra
supported-span proof, and the finite-cover support-union argument formalized by
Formal Frontier Agents. The monomial-subalgebra definition and characteristic
support API retain expression from the ToricIdeals formalization; the scalar-action
span and generic finite-module proofs use GroupRings' generalized map-domain
engine. The predecessors already allowed arbitrary exponent monoids over
commutative semirings. The broader engine allows possibly noncommutative
semiring coefficients and a given-map action, including the
subsingleton-coefficient alternative.

Mathlib supplies adjoining and subalgebra lattices (Kenny Lau and Yury
Kudryashov), monoid-algebra modules and restricted support (Johannes Hölzl, Yury
Kudryashov and Kim Morrison), support estimates (Damiano Testa), finite generation
(Johan Commelin), and scalar restriction (Nathaniel Thomas, Jeremy Avigad,
Johannes Hölzl and Mario Carneiro). Its span API is due to Johannes Hölzl, Mario
Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth.
ToricIdeals retains the cancellative commutative power corollary through its
finite-cover factorial argument; the generic engine has no ToricIdeals dependency.

These are academic and expression-lineage credits, not copyright-ownership or
redistribution-permission claims. Original Formal Frontier expression is
Apache-2.0; authentic dependency licenses and notices remain with their
contributions. See the [complete project license](../LICENSE) and
[complete GroupRings license](https://github.com/FormalFrontier/group-rings/blob/8a10fb8c1285227a36501fa50206a0bed05fc98a/LICENSE).
