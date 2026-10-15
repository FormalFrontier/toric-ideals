/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.NormNum
import ToricIdeals.RationalNormalCurve.Dimension

/-!
# Krull dimension of full Hankel quotients

The degree-two full Hankel quotients have numerical dimensions two over the
rationals, three over the integers and two over the nonreduced ring `ZMod 4`.
These applications use the general quotient-dimension theorem, beyond the
small-degree polynomial-ring cases.

Zero coefficients give dimension `⊥` in every degree, and the formula transports
across a universe lift. Over `ZMod 2`, the full degree-zero quotient retains its
variable and has dimension one, unlike the raw parametrization image of
dimension zero.

## References

* Ravi Vakil, *The Rising Sea*, Exercise 3.6.F, motivates the Hankel presentation.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Dimension`, supplies
  the general and degree-zero dimension theorems for the full Hankel quotient.
* Mathlib contributors supply field, principal-ideal-domain and Artinian-ring
  dimensions, and transport along ring equivalences.
-/

noncomputable section

namespace ToricIdealsTest.RationalNormalCurveDimensionType

open ToricIdeals.RationalNormalCurve

universe u v

private theorem rationalTwo :
    ringKrullDim (Source ℚ 2 ⧸ hankelIdeal ℚ 2) = 2 := by
  simpa [ringKrullDim_eq_zero_of_field] using
    (ringKrullDim_quotient_hankelIdeal ℚ 2)

private theorem integerTwo :
    ringKrullDim (Source ℤ 2 ⧸ hankelIdeal ℤ 2) = 3 := by
  rw [ringKrullDim_quotient_hankelIdeal,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  norm_num

private theorem nonreducedTwo :
    ringKrullDim (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) = 2 := by
  have : Nontrivial (ZMod 4) :=
    (ZMod.nontrivial_iff (n := 4)).2 (by decide)
  have : IsArtinianRing (ZMod 4) := isArtinian_of_finite
  have hdim : ringKrullDim (ZMod 4) = 0 :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := ZMod 4)).mp inferInstance
  rw [ringKrullDim_quotient_hankelIdeal, hdim]
  norm_num

private theorem zeroCoefficients (n : ℕ) :
    ringKrullDim (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = ⊥ := by
  simpa [ringKrullDim_eq_bot_of_subsingleton] using
    (ringKrullDim_quotient_hankelIdeal (ZMod 1) n)

private theorem uliftDimension (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) :
    ringKrullDim (Source (ULift.{v} R) n ⧸ hankelIdeal (ULift.{v} R) n) =
      ringKrullDim R + (if n = 0 then 1 else 2) := by
  letI : IsNoetherianRing (ULift.{v} R) :=
    isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  calc
    ringKrullDim (Source (ULift.{v} R) n ⧸ hankelIdeal (ULift.{v} R) n) =
        ringKrullDim (ULift.{v} R) + (if n = 0 then 1 else 2) :=
      ringKrullDim_quotient_hankelIdeal (ULift.{v} R) n
    _ = ringKrullDim R + (if n = 0 then 1 else 2) := by
      rw [ringKrullDim_eq_of_ringEquiv (ULift.ringEquiv : ULift.{v} R ≃+* R)]

private theorem binaryZeroRawFactor :
    rncMap (ZMod 2) 0 = MvPolynomial.C.comp
      (MvPolynomial.eval₂Hom (RingHom.id (ZMod 2)) (fun _ => 1)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [coordinateExponent]

private theorem binaryZeroRawConstant (x : (rncMap (ZMod 2) 0).range) :
    MvPolynomial.C (MvPolynomial.constantCoeff x.val) = x.val := by
  obtain ⟨p, hp⟩ := x.property
  simp only [← hp, binaryZeroRawFactor, RingHom.comp_apply,
    MvPolynomial.constantCoeff_C]

/-- The raw degree-zero image is the coefficient field. -/
private def binaryZeroRawEquiv : (rncMap (ZMod 2) 0).range ≃+* ZMod 2 := by
  let f : (rncMap (ZMod 2) 0).range →+* ZMod 2 :=
    MvPolynomial.constantCoeff.comp (rncMap (ZMod 2) 0).range.subtype
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    calc
      x.val = MvPolynomial.C (f x) := (binaryZeroRawConstant x).symm
      _ = MvPolynomial.C (f y) := congrArg MvPolynomial.C h
      _ = y.val := binaryZeroRawConstant y
  · intro r
    refine ⟨⟨MvPolynomial.C r, ⟨MvPolynomial.C r, rncMap_C (ZMod 2) 0 r⟩⟩, ?_⟩
    simp [f]

private theorem binaryZeroDimensionDistinction :
    ringKrullDim (Source (ZMod 2) 0 ⧸ hankelIdeal (ZMod 2) 0) ≠
      ringKrullDim (rncMap (ZMod 2) 0).range := by
  have hfull : ringKrullDim (Source (ZMod 2) 0 ⧸ hankelIdeal (ZMod 2) 0) = 1 := by
    simpa [ringKrullDim_eq_zero_of_field] using
      (ringKrullDim_quotient_hankelIdeal_zero (R := ZMod 2))
  have hraw : ringKrullDim (rncMap (ZMod 2) 0).range = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv binaryZeroRawEquiv, ringKrullDim_eq_zero_of_field]
  rw [hfull, hraw]
  exact one_ne_zero

end ToricIdealsTest.RationalNormalCurveDimensionType
