/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.PowerSeries.Inverse
import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.Noetherian

/-!
# Power-series coefficient Jacobson boundary models

The coefficient ring `PowerSeries ℚ` is a Noetherian local domain and a discrete
valuation ring, but it is not a field or a Jacobson ring. Its zero ideal is prime.
The Jacobson radical of that ideal is the nonzero maximal ideal, contradicting
what the prime-ideal criterion would require of a Jacobson ring.

Every full Hankel quotient over these coefficients is Noetherian and is not
Jacobson. For the negative conclusion, constant-coefficient evaluation kills
each displayed minor and descends to a surjective homomorphism onto the
coefficient ring. The preimage of a power series is its constant polynomial
class. Thus Noetherianity of these quotients does not imply Jacobsonness.

Degree zero and degree one retain the full one-variable and two-variable
polynomial quotients by the bottom ideal. In degree zero the Hankel ideal is
strictly smaller than the parametrization kernel; that kernel is not used to
replace the quotient.

## References

* `ToricIdeals.RationalNormalCurve` supplies the full Hankel presentation and
  its small-degree boundary results.
* `ToricIdeals.RationalNormalCurve.Noetherian` supplies the Noetherian quotient
  criterion and the constant-coefficient evaluation argument followed here.
* Mathlib's power-series, discrete-valuation-ring and local-ring theory supplies
  the coefficient domain, local, Noetherian and nonfield properties.
* Mathlib's Jacobson ring theory supplies the prime-ideal criterion and descent
  along surjective ring homomorphisms.
-/

namespace ToricIdeals.RationalNormalCurve.JacobsonModels

noncomputable section

/-- The zero prime in the power-series domain has nonzero Jacobson radical. -/
private theorem power_series_coefficients_not_jacobson :
    ¬ IsJacobsonRing (PowerSeries ℚ) := by
  intro h
  have hprime : (⊥ : Ideal (PowerSeries ℚ)).IsPrime := Ideal.isPrime_bot
  have hbot : (⊥ : Ideal (PowerSeries ℚ)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.mp h _ hprime
  have hmax : (⊥ : Ideal (PowerSeries ℚ)).jacobson =
      IsLocalRing.maximalIdeal (PowerSeries ℚ) :=
    IsLocalRing.jacobson_eq_maximalIdeal _ hprime.ne_top
  exact IsDiscreteValuationRing.not_a_field (PowerSeries ℚ) (hmax.symm.trans hbot)


/-- Rational power series form a Noetherian local domain and a nonfield DVR,
but not a Jacobson ring. -/
private theorem power_series_coefficients :
    IsDomain (PowerSeries ℚ) ∧
      IsLocalRing (PowerSeries ℚ) ∧
      IsDiscreteValuationRing (PowerSeries ℚ) ∧
      IsNoetherianRing (PowerSeries ℚ) ∧
      ¬ IsField (PowerSeries ℚ) ∧
      ¬ IsJacobsonRing (PowerSeries ℚ) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.not_isField (PowerSeries ℚ),
    power_series_coefficients_not_jacobson⟩


/-- Every full Hankel quotient with rational power-series coefficients is
Noetherian but not Jacobson, including degrees zero and one. -/
private theorem power_series_quotients_noetherian_not_jacobson (n : ℕ) :
    IsNoetherianRing (Source (PowerSeries ℚ) n ⧸ hankelIdeal (PowerSeries ℚ) n) ∧
      ¬ IsJacobsonRing (Source (PowerSeries ℚ) n ⧸ hankelIdeal (PowerSeries ℚ) n) := by
  constructor
  · exact (quotient_isNoetherianRing_iff (PowerSeries ℚ) n).mpr
      power_series_coefficients.2.2.2.1
  · intro hQ
    let : IsJacobsonRing (Source (PowerSeries ℚ) n ⧸ hankelIdeal (PowerSeries ℚ) n) := hQ
    let e : Source (PowerSeries ℚ) n →+* PowerSeries ℚ := MvPolynomial.constantCoeff
    have hI : hankelIdeal (PowerSeries ℚ) n ≤ RingHom.ker e := by
      apply Ideal.span_le.mpr
      rintro _ ⟨p, rfl⟩
      apply RingHom.mem_ker.mpr
      simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
        mul_zero, sub_self]
    let g : (Source (PowerSeries ℚ) n ⧸ hankelIdeal (PowerSeries ℚ) n) →+* PowerSeries ℚ :=
      Ideal.Quotient.lift (hankelIdeal (PowerSeries ℚ) n) e
        (fun _ hf => RingHom.mem_ker.mp (hI hf))
    have hg : Function.Surjective g := by
      intro r
      refine ⟨Ideal.Quotient.mk (hankelIdeal (PowerSeries ℚ) n) (MvPolynomial.C r), ?_⟩
      simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
    exact power_series_coefficients_not_jacobson (isJacobsonRing_of_surjective ⟨g, hg⟩)


/-- The degree-zero quotient is the full one-variable polynomial ring modulo
bottom, rather than the parametrization kernel quotient; it is Noetherian and
not Jacobson. -/
private theorem power_series_degree_zero_shape :
    hankelIdeal (PowerSeries ℚ) 0 = ⊥ ∧
      hankelIdeal (PowerSeries ℚ) 0 < RingHom.ker (rncMap (PowerSeries ℚ) 0) ∧
      Nonempty ((Source (PowerSeries ℚ) 0 ⧸ hankelIdeal (PowerSeries ℚ) 0) ≃+*
        MvPolynomial (Fin 1) (PowerSeries ℚ)) ∧
      IsNoetherianRing (Source (PowerSeries ℚ) 0 ⧸ hankelIdeal (PowerSeries ℚ) 0) ∧
      ¬ IsJacobsonRing (Source (PowerSeries ℚ) 0 ⧸ hankelIdeal (PowerSeries ℚ) 0) := by
  refine ⟨hankelIdeal_zero (PowerSeries ℚ), hankelIdeal_zero_lt_ker (PowerSeries ℚ),
    ?_, power_series_quotients_noetherian_not_jacobson 0⟩
  rw [hankelIdeal_zero]
  exact ⟨RingEquiv.quotientBot (Source (PowerSeries ℚ) 0)⟩


/-- The degree-one quotient is the full two-variable polynomial ring modulo
bottom, and is Noetherian but not Jacobson. -/
private theorem power_series_degree_one_shape :
    hankelIdeal (PowerSeries ℚ) 1 = ⊥ ∧
      Nonempty ((Source (PowerSeries ℚ) 1 ⧸ hankelIdeal (PowerSeries ℚ) 1) ≃+*
        MvPolynomial (Fin 2) (PowerSeries ℚ)) ∧
      IsNoetherianRing (Source (PowerSeries ℚ) 1 ⧸ hankelIdeal (PowerSeries ℚ) 1) ∧
      ¬ IsJacobsonRing (Source (PowerSeries ℚ) 1 ⧸ hankelIdeal (PowerSeries ℚ) 1) := by
  refine ⟨hankelIdeal_one (PowerSeries ℚ), ?_,
    power_series_quotients_noetherian_not_jacobson 1⟩
  rw [hankelIdeal_one]
  exact ⟨RingEquiv.quotientBot (Source (PowerSeries ℚ) 1)⟩


end

end ToricIdeals.RationalNormalCurve.JacobsonModels
