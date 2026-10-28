/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.Evaluation
public import ToricIdeals.SplitQuadric.Basic
public import ToricIdeals.SplitQuadric.Exponents

/-!
# The determinantal parametrization as a map of monoid algebras

`SplitQuadric.theta` is Mathlib's existing `AddMonoidAlgebra.mapDomainAlgHom`
for `ToricIdeals.SplitQuadric.exponentMap`. This identifies polynomial
substitution with the map that sums coefficients along exponent fibers.
The coefficient ring is arbitrary, including zero rings and rings with nilpotents.

## Implementation notes

The bridge specializes weighted monomial evaluation to the four variable images.
It makes no assertion about kernels, quotient rings or
surjectivity. No coefficient or exponent-map construction is duplicated.

## References

* Mathlib, `Algebra/MonoidAlgebra/Basic` and `Algebra/MonoidAlgebra/MapDomain`:
  the existing `AddMonoidAlgebra.mapDomainAlgHom` and its monomial computation.
* Mathlib, `Algebra/MvPolynomial/Basic`: the additive-monoid-algebra
  representation of multivariate polynomials and `MvPolynomial.algHom_ext`.
* `ToricIdeals.SplitQuadric.Exponents`: the additive determinantal exponent map and its
  coordinate computations.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

open ToricIdeals.SplitQuadric

variable (A : Type u) [CommRing A]

/-- Polynomial substitution by `(W, WT, Y, YT)` is the existing algebra
homomorphism induced by the additive determinantal exponent map. -/
theorem theta_eq_mapDomainAlgHom :
    theta A =
      AddMonoidAlgebra.mapDomainAlgHom A A exponentMap := by
  rw [exponentMap, ← MvPolynomial.aeval_single_eq_mapDomainAlgHom]
  apply MvPolynomial.algHom_ext
  intro i
  rw [theta_X, MvPolynomial.aeval_X]
  fin_cases i <;>
    simp [parameterValues, MvPolynomial.X, MvPolynomial.single_eq_monomial,
      MvPolynomial.monomial_mul_monomial]

end SplitQuadric
