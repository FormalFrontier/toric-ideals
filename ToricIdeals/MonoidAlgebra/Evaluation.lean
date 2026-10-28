/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Finsupp.Weight

/-!
# Weighted monomial evaluation

Evaluating multivariate variables at coefficient-one monomials is the algebra
homomorphism induced by the additive weight map on exponents. For natural-number
weights, the polynomial/additive-monoid-algebra equivalence identifies evaluation
at powers of `Polynomial.X` with this same homomorphism.

## References

* Mathlib's `MvPolynomial.algHom_ext` and `MvPolynomial.comp_aeval` express the
  universal property and postcomposition naturality of evaluation.
* Mathlib's `Finsupp.weight_single` and `AddMonoidAlgebra.mapDomain_single`
  compute the induced map on monomials.
* Mathlib's `Polynomial.toFinsupp_X_pow` identifies powers of `Polynomial.X`
  with coefficient-one monomials.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommSemiring R] {σ : Type v}

/-- Evaluation at coefficient-one monomials transports exponents along the weight map. -/
theorem aeval_single_eq_mapDomainAlgHom {M : Type w} [AddCommMonoid M] (weights : σ → M) :
    aeval (fun i => AddMonoidAlgebra.single (weights i) (1 : R)) =
      AddMonoidAlgebra.mapDomainAlgHom R R (Finsupp.weight weights) := by
  apply algHom_ext
  intro i
  rw [aeval_X]
  simp only [AddMonoidAlgebra.mapDomainAlgHom_apply, X, ← single_eq_monomial,
    AddMonoidAlgebra.mapDomain_single, Finsupp.weight_single, one_nsmul]

/-- Under the polynomial/additive-monoid-algebra equivalence, evaluation at powers of
`Polynomial.X` transports exponents along the natural-number weight map. -/
theorem toFinsuppIsoAlg_comp_aeval_X_pow (weights : σ → ℕ) :
    (Polynomial.toFinsuppIsoAlg R).toAlgHom.comp
        (aeval (fun i => (Polynomial.X : Polynomial R) ^ weights i)) =
      AddMonoidAlgebra.mapDomainAlgHom R R (Finsupp.weight weights) := by
  rw [comp_aeval]
  change aeval (fun i => ((Polynomial.X : Polynomial R) ^ weights i).toFinsupp) = _
  simp_rw [Polynomial.toFinsupp_X_pow]
  exact aeval_single_eq_mapDomainAlgHom weights

end MvPolynomial
