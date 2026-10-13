/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import MultivariatePolynomials.Artinian
import MultivariatePolynomials.Noetherian
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.AxisProjection

/-!
# Coefficient-module boundaries for Hankel quotients

These examples use the canonical coefficient action on the full quotient
`Source R n ⧸ hankelIdeal R n`. They distinguish this action from multiplication
by the quotient ring itself. In every degree, zero coefficients give both a
Noetherian and an Artinian coefficient module. The nonzero finite ring `ZMod 4`
is Noetherian and Artinian over itself, but its Hankel quotients have neither
property as coefficient modules and retain a nonzero square-zero constant.

The integer examples retain the full one-variable and two-variable presentations
in degrees zero and one. Integer-product coefficients exhibit surviving
orthogonal nonzero constants. A lifted copy of `ZMod 4` tests the same coefficient
action in a higher universe.

Each negative Noetherian and Artinian conclusion is proved separately by the
coefficient-linear surjection `axisProjection R n`. Neither conclusion is deduced
from the other, and no criterion for the Hankel quotient is used. Constant
classes are tested through the public coefficient augmentation.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.AxisProjection` and
  `ToricIdeals.RationalNormalCurve.Augmentation`, for the canonical split axis
  projection and coefficient augmentation of the full Hankel quotient.
* Formal Frontier Agents, `MultivariatePolynomials.Noetherian` and
  `MultivariatePolynomials.Artinian`, for the coefficient-module criteria
  `Polynomial.isNoetherian_iff` and `Polynomial.isArtinian_iff`.
* Formal Frontier Agents, `ToricIdealsTest.RationalNormalCurveArtinianModels`,
  for the integer, nonreduced and product-ring boundary examples developed here
  with the coefficient action rather than the quotient's self-action.
* Mathlib contributors, `Mathlib.RingTheory.Noetherian.Basic` and
  `Mathlib.RingTheory.Artinian.Module`, for linear surjective descent and
  the finite and trivial-coefficient module results.
-/

namespace ToricIdeals.RationalNormalCurve.CoefficientModules

noncomputable section

universe u

/-- Zero coefficients give both chain conditions for the coefficient action,
in every degree. -/
private theorem zero_coefficients_quotients_noetherian_artinian (n : ℕ) :
    IsNoetherian (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      IsArtinian (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  refine ⟨isNoetherian_of_subsingleton (ZMod 1) _, ?_⟩
  let : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
    Algebra.subsingleton (ZMod 1) _
  let : Finite (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := inferInstance
  exact isArtinian_of_finite (R := ZMod 1)
    (M := Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n)

/-- Finite nonreduced coefficients satisfy both self-module conditions, while
neither condition holds for their full Hankel quotient as a coefficient module.
The nonzero square-zero coefficient remains nonzero and square-zero in the quotient. -/
private theorem mod_four_quotients_with_nilpotent_constants (n : ℕ) :
    IsNoetherianRing (ZMod 4) ∧ IsArtinianRing (ZMod 4) ∧
      (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧ ¬ IsReduced (ZMod 4) ∧
      ¬ IsNoetherian (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      ¬ IsArtinian (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 ∧
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n)
        (MvPolynomial.C (2 : ZMod 4))) ^ 2 = 0 := by
  let : Fact (1 < 4) := ⟨by decide⟩
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨isNoetherian_of_finite (ZMod 4) (ZMod 4),
    isArtinian_of_finite, hne, hsq, ?_, ?_, ?_, ?_, ?_⟩
  · intro hR
    let : IsReduced (ZMod 4) := hR
    exact hne (show IsNilpotent (2 : ZMod 4) from ⟨2, hsq⟩).eq_zero
  · intro hQ
    let : IsNoetherian (ZMod 4)
        (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := hQ
    have hP : IsNoetherian (ZMod 4) (Polynomial (ZMod 4)) :=
      isNoetherian_of_surjective (σ := RingHom.id (ZMod 4))
        (axisProjection (ZMod 4) n).toLinearMap
        (LinearMap.range_eq_top.mpr (axisProjection_surjective (ZMod 4) n))
    exact (not_subsingleton (ZMod 4)) ((Polynomial.isNoetherian_iff (ZMod 4)).mp hP)
  · intro hQ
    let : IsArtinian (ZMod 4)
        (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := hQ
    have hP : IsArtinian (ZMod 4) (Polynomial (ZMod 4)) :=
      isArtinian_of_surjective (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)
        (axisProjection (ZMod 4) n).toLinearMap (axisProjection_surjective (ZMod 4) n)
    exact (not_subsingleton (ZMod 4)) ((Polynomial.isArtinian_iff (ZMod 4)).mp hP)
  · intro hzero
    apply hne
    simpa only [quotientAugmentation_mk, MvPolynomial.constantCoeff_C, map_zero] using
      congrArg (quotientAugmentation (ZMod 4) n) hzero
  · calc
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n)
          (MvPolynomial.C (2 : ZMod 4))) ^ 2 =
          Ideal.Quotient.mk (hankelIdeal (ZMod 4) n)
            (MvPolynomial.C ((2 : ZMod 4) ^ 2)) := by simp only [map_pow]
      _ = 0 := by rw [hsq, map_zero, map_zero]

/-- The integer Hankel quotient has neither coefficient-module chain condition,
even though integer coefficients are Noetherian over themselves. -/
private theorem integer_quotients_not_noetherian_artinian (n : ℕ) :
    ¬ IsNoetherian ℤ (Source ℤ n ⧸ hankelIdeal ℤ n) ∧
      ¬ IsArtinian ℤ (Source ℤ n ⧸ hankelIdeal ℤ n) := by
  constructor
  · intro hQ
    let : IsNoetherian ℤ (Source ℤ n ⧸ hankelIdeal ℤ n) := hQ
    have hP : IsNoetherian ℤ (Polynomial ℤ) :=
      isNoetherian_of_surjective (σ := RingHom.id ℤ) (axisProjection ℤ n).toLinearMap
        (LinearMap.range_eq_top.mpr (axisProjection_surjective ℤ n))
    exact (not_subsingleton ℤ) ((Polynomial.isNoetherian_iff ℤ).mp hP)
  · intro hQ
    let : IsArtinian ℤ (Source ℤ n ⧸ hankelIdeal ℤ n) := hQ
    have hP : IsArtinian ℤ (Polynomial ℤ) :=
      isArtinian_of_surjective (Source ℤ n ⧸ hankelIdeal ℤ n)
        (axisProjection ℤ n).toLinearMap (axisProjection_surjective ℤ n)
    exact (not_subsingleton ℤ) ((Polynomial.isArtinian_iff ℤ).mp hP)

/-- Degree zero retains `X₀`; degree one retains both quotient coordinates,
although the axis projection kills `X₁`. Both full integer quotients fail both
coefficient-module chain conditions. -/
private theorem integer_degree_zero_and_one_quotients :
    (Source ℤ 0 = MvPolynomial (Fin 1) ℤ ∧ hankelIdeal ℤ 0 = ⊥ ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) ∧
      axisProjection ℤ 0
        (Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1))) = Polynomial.X ∧
      ¬ IsNoetherian ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      ¬ IsArtinian ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0)) ∧
    (Source ℤ 1 = MvPolynomial (Fin 2) ℤ ∧ hankelIdeal ℤ 1 = ⊥ ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (MvPolynomial.X (1 : Fin 2)) ≠ 0 ∧
      axisProjection ℤ 1
        (Ideal.Quotient.mk (hankelIdeal ℤ 1) (MvPolynomial.X (0 : Fin 2))) = Polynomial.X ∧
      axisProjection ℤ 1
        (Ideal.Quotient.mk (hankelIdeal ℤ 1) (MvPolynomial.X (1 : Fin 2))) = 0 ∧
      ¬ IsNoetherian ℤ (Source ℤ 1 ⧸ hankelIdeal ℤ 1) ∧
      ¬ IsArtinian ℤ (Source ℤ 1 ⧸ hankelIdeal ℤ 1)) := by
  refine ⟨⟨rfl, hankelIdeal_zero ℤ, hankelIdeal_zero_lt_ker ℤ,
    axisProjection_X_zero ℤ 0, integer_quotients_not_noetherian_artinian 0⟩,
    ⟨rfl, hankelIdeal_one ℤ, ?_, axisProjection_X_zero ℤ 1, ?_,
      integer_quotients_not_noetherian_artinian 1⟩⟩
  · intro hzero
    apply MvPolynomial.X_ne_zero (R := ℤ) (1 : Fin 2)
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_one] at hmem
    exact hmem
  · exact axisProjection_X_of_ne_zero ℤ 1 (1 : Fin 2) (by decide)

/-- Integer-product coefficients give nonzero orthogonal constant classes in
all degrees. Each coefficient-module chain condition fails independently. -/
private theorem integer_product_quotients_with_orthogonal_constants (n : ℕ) :
    ¬ IsNoetherian (ℤ × ℤ) (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) ∧
      ¬ IsArtinian (ℤ × ℤ) (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
        (MvPolynomial.C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
        (MvPolynomial.C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((0, 1) : ℤ × ℤ)) = 0 := by
  have hleft : ((1, 0) : ℤ × ℤ) ≠ 0 := by decide
  have hright : ((0, 1) : ℤ × ℤ) ≠ 0 := by decide
  have horth : ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hQ
    let : IsNoetherian (ℤ × ℤ) (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := hQ
    have hP : IsNoetherian (ℤ × ℤ) (Polynomial (ℤ × ℤ)) :=
      isNoetherian_of_surjective (σ := RingHom.id (ℤ × ℤ))
        (axisProjection (ℤ × ℤ) n).toLinearMap
        (LinearMap.range_eq_top.mpr (axisProjection_surjective (ℤ × ℤ) n))
    exact (not_subsingleton (ℤ × ℤ)) ((Polynomial.isNoetherian_iff (ℤ × ℤ)).mp hP)
  · intro hQ
    let : IsArtinian (ℤ × ℤ) (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := hQ
    have hP : IsArtinian (ℤ × ℤ) (Polynomial (ℤ × ℤ)) :=
      isArtinian_of_surjective (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n)
        (axisProjection (ℤ × ℤ) n).toLinearMap (axisProjection_surjective (ℤ × ℤ) n)
    exact (not_subsingleton (ℤ × ℤ)) ((Polynomial.isArtinian_iff (ℤ × ℤ)).mp hP)
  · intro hzero
    apply hleft
    simpa only [quotientAugmentation_mk, MvPolynomial.constantCoeff_C, map_zero] using
      congrArg (quotientAugmentation (ℤ × ℤ) n) hzero
  · intro hzero
    apply hright
    simpa only [quotientAugmentation_mk, MvPolynomial.constantCoeff_C, map_zero] using
      congrArg (quotientAugmentation (ℤ × ℤ) n) hzero
  · calc
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((0, 1) : ℤ × ℤ)) =
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
            (MvPolynomial.C (((1, 0) : ℤ × ℤ) * (0, 1))) := by simp only [map_mul]
      _ = 0 := by rw [horth, map_zero, map_zero]

/-- A genuine copy of the finite nonreduced coefficient ring in `Type (u + 1)`
has both self-module conditions, but its Hankel quotients have neither condition
for the canonical lifted coefficient action. -/
private theorem lifted_mod_four_quotients_not_noetherian_artinian (n : ℕ) :
    IsNoetherianRing (ULift.{u + 1} (ZMod 4)) ∧
      IsArtinianRing (ULift.{u + 1} (ZMod 4)) ∧
      ¬ IsNoetherian (ULift.{u + 1} (ZMod 4))
        (Source (ULift.{u + 1} (ZMod 4)) n ⧸ hankelIdeal (ULift.{u + 1} (ZMod 4)) n) ∧
      ¬ IsArtinian (ULift.{u + 1} (ZMod 4))
        (Source (ULift.{u + 1} (ZMod 4)) n ⧸ hankelIdeal (ULift.{u + 1} (ZMod 4)) n) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  refine ⟨isNoetherian_of_finite (ULift.{u + 1} (ZMod 4)) (ULift.{u + 1} (ZMod 4)),
    isArtinian_of_finite, ?_, ?_⟩
  · intro hQ
    let : IsNoetherian (ULift.{u + 1} (ZMod 4))
        (Source (ULift.{u + 1} (ZMod 4)) n ⧸ hankelIdeal (ULift.{u + 1} (ZMod 4)) n) := hQ
    have hP : IsNoetherian (ULift.{u + 1} (ZMod 4)) (Polynomial (ULift.{u + 1} (ZMod 4))) :=
      isNoetherian_of_surjective (σ := RingHom.id (ULift.{u + 1} (ZMod 4)))
        (axisProjection (ULift.{u + 1} (ZMod 4)) n).toLinearMap
        (LinearMap.range_eq_top.mpr (axisProjection_surjective (ULift.{u + 1} (ZMod 4)) n))
    exact (not_subsingleton (ULift.{u + 1} (ZMod 4)))
      ((Polynomial.isNoetherian_iff (ULift.{u + 1} (ZMod 4))).mp hP)
  · intro hQ
    let : IsArtinian (ULift.{u + 1} (ZMod 4))
        (Source (ULift.{u + 1} (ZMod 4)) n ⧸ hankelIdeal (ULift.{u + 1} (ZMod 4)) n) := hQ
    have hP : IsArtinian (ULift.{u + 1} (ZMod 4)) (Polynomial (ULift.{u + 1} (ZMod 4))) :=
      isArtinian_of_surjective
        (Source (ULift.{u + 1} (ZMod 4)) n ⧸ hankelIdeal (ULift.{u + 1} (ZMod 4)) n)
        (axisProjection (ULift.{u + 1} (ZMod 4)) n).toLinearMap
        (axisProjection_surjective (ULift.{u + 1} (ZMod 4)) n)
    exact (not_subsingleton (ULift.{u + 1} (ZMod 4)))
      ((Polynomial.isArtinian_iff (ULift.{u + 1} (ZMod 4))).mp hP)

end

end ToricIdeals.RationalNormalCurve.CoefficientModules
