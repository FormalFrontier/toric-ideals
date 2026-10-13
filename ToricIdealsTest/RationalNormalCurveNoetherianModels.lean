/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PrincipalIdealDomain
import ToricIdeals.RationalNormalCurve.Noetherian

/-!
# Noetherian coefficient models for Hankel quotients

Integer coefficients, the two-element field `ZMod 2`, the product `ℤ × ℤ`,
`ZMod 4` and the zero ring `ZMod 1` give Noetherian Hankel quotients in every
degree. The source-and-quotient models use Mathlib's finite-variable Hilbert
basis theorem and Noetherian quotient instance, independently of the quotient
criterion. Further examples apply both directions of the criterion over an
arbitrary commutative ring and specialize it to the nonreduced, zero and
product coefficient rings.

The product and `ZMod 4` models allow zero divisors and nonreduced coefficients,
respectively; the zero-ring model allows `1 = 0`. The small-degree models use
the existing Hankel-ideal boundary results and retain the one-variable source
at degree zero and the two-variable source at degree one.

## References

* Mathlib contributors, the Noetherian finite-ring, product-ring,
  principal-ideal-ring, finite-variable polynomial and quotient instances.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the Hankel
  presentation and its degree-zero and degree-one ideal equalities.
-/

public section

open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.NoetherianModels

noncomputable section

universe u

private theorem integer_source_and_quotient_noetherian (n : ℕ) :
    IsNoetherianRing ℤ ∧ IsNoetherianRing (Source ℤ n) ∧
      IsNoetherianRing (Source ℤ n ⧸ hankelIdeal ℤ n) := by
  let : IsNoetherianRing (Source ℤ n) := MvPolynomial.isNoetherianRing_fin
  exact ⟨inferInstance, inferInstance, Ideal.Quotient.isNoetherianRing _⟩

private theorem binary_field_source_and_quotient_noetherian (n : ℕ) :
    IsNoetherianRing (ZMod 2) ∧ IsNoetherianRing (Source (ZMod 2) n) ∧
      IsNoetherianRing (Source (ZMod 2) n ⧸ hankelIdeal (ZMod 2) n) := by
  let : IsNoetherianRing (ZMod 2) := isNoetherian_of_finite (ZMod 2) (ZMod 2)
  let : IsNoetherianRing (Source (ZMod 2) n) := MvPolynomial.isNoetherianRing_fin
  exact ⟨inferInstance, inferInstance, Ideal.Quotient.isNoetherianRing _⟩

private theorem integer_product_source_and_quotient_noetherian (n : ℕ) :
    IsNoetherianRing (ℤ × ℤ) ∧ IsNoetherianRing (Source (ℤ × ℤ) n) ∧
      IsNoetherianRing (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := by
  let : IsNoetherianRing (ℤ × ℤ) := inferInstance
  let : IsNoetherianRing (Source (ℤ × ℤ) n) := MvPolynomial.isNoetherianRing_fin
  exact ⟨inferInstance, inferInstance, Ideal.Quotient.isNoetherianRing _⟩

private theorem mod_four_source_and_quotient_noetherian (n : ℕ) :
    IsNoetherianRing (ZMod 4) ∧ IsNoetherianRing (Source (ZMod 4) n) ∧
      IsNoetherianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  let : IsNoetherianRing (ZMod 4) := isNoetherian_of_finite (ZMod 4) (ZMod 4)
  let : IsNoetherianRing (Source (ZMod 4) n) := MvPolynomial.isNoetherianRing_fin
  exact ⟨inferInstance, inferInstance, Ideal.Quotient.isNoetherianRing _⟩

private theorem zero_coefficients_source_and_quotient_noetherian (n : ℕ) :
    IsNoetherianRing (ZMod 1) ∧ IsNoetherianRing (Source (ZMod 1) n) ∧
      IsNoetherianRing (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  let : IsNoetherianRing (ZMod 1) := isNoetherian_of_finite (ZMod 1) (ZMod 1)
  let : IsNoetherianRing (Source (ZMod 1) n) := MvPolynomial.isNoetherianRing_fin
  exact ⟨inferInstance, inferInstance, Ideal.Quotient.isNoetherianRing _⟩

private theorem degree_zero_one_variable_quotient_noetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Source R 0 = MvPolynomial (Fin 1) R ∧ hankelIdeal R 0 = ⊥ ∧
      IsNoetherianRing (Source R 0 ⧸ hankelIdeal R 0) := by
  refine ⟨rfl, hankelIdeal_zero R, ?_⟩
  rw [hankelIdeal_zero]
  let : IsNoetherianRing (Source R 0) := MvPolynomial.isNoetherianRing_fin
  exact Ideal.Quotient.isNoetherianRing _

private theorem degree_one_two_variable_quotient_noetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Source R 1 = MvPolynomial (Fin 2) R ∧ hankelIdeal R 1 = ⊥ ∧
      IsNoetherianRing (Source R 1 ⧸ hankelIdeal R 1) := by
  refine ⟨rfl, hankelIdeal_one R, ?_⟩
  rw [hankelIdeal_one]
  let : IsNoetherianRing (Source R 1) := MvPolynomial.isNoetherianRing_fin
  exact Ideal.Quotient.isNoetherianRing _

/-- A supplied Noetherian coefficient hypothesis gives a Noetherian Hankel
quotient in every degree, over a commutative ring in any universe. -/
private theorem hankel_quotient_noetherian_of_noetherian_coefficients
    (R : Type u) [CommRing R] (n : ℕ) (hR : IsNoetherianRing R) :
    IsNoetherianRing (Source R n ⧸ hankelIdeal R n) := by
  exact (quotient_isNoetherianRing_iff R n).mpr hR

/-- Noetherianity of a Hankel quotient recovers Noetherianity of its
coefficient ring without a positivity or nontriviality assumption. -/
private theorem coefficients_noetherian_of_noetherian_hankel_quotient
    (R : Type u) [CommRing R] (n : ℕ)
    (hQ : IsNoetherianRing (Source R n ⧸ hankelIdeal R n)) :
    IsNoetherianRing R := by
  exact (quotient_isNoetherianRing_iff R n).mp hQ

/-- The quotient criterion applies uniformly to nonreduced coefficients,
the zero ring and a product of integer rings. -/
private theorem nonreduced_zero_and_product_hankel_quotients_noetherian (n : ℕ) :
    IsNoetherianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      IsNoetherianRing (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      IsNoetherianRing (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := by
  exact ⟨(quotient_isNoetherianRing_iff (ZMod 4) n).mpr
      (isNoetherian_of_finite (ZMod 4) (ZMod 4)),
    (quotient_isNoetherianRing_iff (ZMod 1) n).mpr
      (isNoetherian_of_finite (ZMod 1) (ZMod 1)),
    (quotient_isNoetherianRing_iff (ℤ × ℤ) n).mpr inferInstance⟩


end

end ToricIdeals.RationalNormalCurve.NoetherianModels
