/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.NormNum
import ToricIdeals

/-!
# Clients of the small-degree Hankel quotient dimension formulas

These clients use the public dimension theorems through the aggregate import.
They compose the formulas with the dimension of `R[X]` over an arbitrary
Noetherian commutative ring `R`, and give numerical dimensions over the rationals,
integers and the nonreduced ring `ZMod 4`, as well as bottom over zero coefficients.
The conditional infinite-dimension clients check the formulas at `⊤` without
assuming finite Krull dimension. All clients concern the full Hankel quotient,
including its one variable in degree zero.
-/

namespace ToricIdealsTest.RationalNormalCurveDimensionBaseCases

open ToricIdeals.RationalNormalCurve

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

private theorem polynomialCoefficientsZero :
    ringKrullDim (Source (Polynomial R) 0 ⧸ hankelIdeal (Polynomial R) 0) =
      ringKrullDim R + 2 := by
  rw [ringKrullDim_quotient_hankelIdeal_zero,
    Polynomial.ringKrullDim_of_isNoetherianRing, add_assoc]
  norm_num

private theorem polynomialCoefficientsOne :
    ringKrullDim (Source (Polynomial R) 1 ⧸ hankelIdeal (Polynomial R) 1) =
      ringKrullDim R + 3 := by
  rw [ringKrullDim_quotient_hankelIdeal_one,
    Polynomial.ringKrullDim_of_isNoetherianRing, add_assoc]
  norm_num

private theorem rationalZero :
    ringKrullDim (Source ℚ 0 ⧸ hankelIdeal ℚ 0) = 1 := by
  simpa [ringKrullDim_eq_zero_of_field] using
    (ringKrullDim_quotient_hankelIdeal_zero (R := ℚ))

private theorem rationalOne :
    ringKrullDim (Source ℚ 1 ⧸ hankelIdeal ℚ 1) = 2 := by
  simpa [ringKrullDim_eq_zero_of_field] using
    (ringKrullDim_quotient_hankelIdeal_one (R := ℚ))

private theorem integerZero :
    ringKrullDim (Source ℤ 0 ⧸ hankelIdeal ℤ 0) = 2 := by
  rw [ringKrullDim_quotient_hankelIdeal_zero,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  norm_num

private theorem integerOne :
    ringKrullDim (Source ℤ 1 ⧸ hankelIdeal ℤ 1) = 3 := by
  rw [ringKrullDim_quotient_hankelIdeal_one,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  norm_num

private theorem nonreducedZero :
    ringKrullDim (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) = 1 := by
  have : Nontrivial (ZMod 4) :=
    (ZMod.nontrivial_iff (n := 4)).2 (by decide)
  have : IsArtinianRing (ZMod 4) := isArtinian_of_finite
  have hdim : ringKrullDim (ZMod 4) = 0 :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := ZMod 4)).mp inferInstance
  rw [ringKrullDim_quotient_hankelIdeal_zero, hdim, zero_add]

private theorem nonreducedOne :
    ringKrullDim (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) = 2 := by
  have : Nontrivial (ZMod 4) :=
    (ZMod.nontrivial_iff (n := 4)).2 (by decide)
  have : IsArtinianRing (ZMod 4) := isArtinian_of_finite
  have hdim : ringKrullDim (ZMod 4) = 0 :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := ZMod 4)).mp inferInstance
  rw [ringKrullDim_quotient_hankelIdeal_one, hdim, zero_add]

private theorem zeroRingZero :
    ringKrullDim (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = ⊥ := by
  rw [ringKrullDim_quotient_hankelIdeal_zero]
  simp [ringKrullDim_eq_bot_of_subsingleton]

private theorem zeroRingOne :
    ringKrullDim (Source (ZMod 1) 1 ⧸ hankelIdeal (ZMod 1) 1) = ⊥ := by
  rw [ringKrullDim_quotient_hankelIdeal_one]
  simp [ringKrullDim_eq_bot_of_subsingleton]

private theorem infiniteZero (hR : ringKrullDim R = ⊤) :
    ringKrullDim (Source R 0 ⧸ hankelIdeal R 0) = ⊤ := by
  simpa [hR] using (ringKrullDim_quotient_hankelIdeal_zero (R := R))

private theorem infiniteOne (hR : ringKrullDim R = ⊤) :
    ringKrullDim (Source R 1 ⧸ hankelIdeal R 1) = ⊤ := by
  simpa [hR] using (ringKrullDim_quotient_hankelIdeal_one (R := R))

end ToricIdealsTest.RationalNormalCurveDimensionBaseCases
