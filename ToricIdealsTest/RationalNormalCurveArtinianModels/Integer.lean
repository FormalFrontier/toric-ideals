/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module
import ToricIdeals.RationalNormalCurve

/-!
# Integer and zero-coefficient Artinian quotient models

The Hankel quotients over the integers are not Artinian in any degree:
evaluation at zero descends to a surjective homomorphism onto the integers,
where the regular element `2` is not a unit. Degree zero retains the full
one-variable polynomial presentation, with its bottom Hankel ideal strictly
smaller than the parametrization kernel. Degree one retains the full
two-variable polynomial presentation and also has bottom Hankel ideal.

Over the zero coefficient ring `ZMod 1`, every Hankel quotient is a singleton
zero ring and hence Artinian. These conclusions use the polynomial presentation
and the quotient by the Hankel ideal, not a replacement by the parametrization
kernel or image.

## References

* `ToricIdeals.RationalNormalCurve` supplies the Hankel presentation and the
  degree-zero and degree-one boundary results.
* Mathlib's Artinian ring theory supplies surjective transfer and the fact that
  regular elements of an Artinian ring are units.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve.ArtinianModels

noncomputable section

/-- The integer `2` is regular but not a unit, so the integers are not Artinian. -/
private theorem integer_coefficients_not_artinian : ¬ IsArtinianRing ℤ := by
  intro hZ
  let : IsArtinianRing ℤ := hZ
  have hregular : IsRegular (2 : ℤ) := IsRegular.of_ne_zero (by decide)
  have hunit : IsUnit (2 : ℤ) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr hregular
  have hnot : ¬ ((2 : ℤ) = 1 ∨ (2 : ℤ) = -1) := by decide
  exact hnot (Int.isUnit_eq_one_or hunit)

/-- Evaluation at zero makes every integer Hankel quotient surject onto the
non-Artinian integer coefficient ring. -/
private theorem integer_hankel_quotient_not_artinian (n : ℕ) :
    ¬ IsArtinianRing (Source ℤ n ⧸ hankelIdeal ℤ n) := by
  intro hQ
  let : IsArtinianRing (Source ℤ n ⧸ hankelIdeal ℤ n) := hQ
  let e : Source ℤ n →+* ℤ := MvPolynomial.constantCoeff
  have hI : hankelIdeal ℤ n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero, sub_self]
  let g : (Source ℤ n ⧸ hankelIdeal ℤ n) →+* ℤ :=
    Ideal.Quotient.lift (hankelIdeal ℤ n) e
      (fun _ hf => RingHom.mem_ker.mp (hI hf))
  have hg : Function.Surjective g := by
    intro r
    refine ⟨Ideal.Quotient.mk (hankelIdeal ℤ n) (MvPolynomial.C r), ?_⟩
    simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
  exact integer_coefficients_not_artinian hg.isArtinianRing

/-- Zero coefficients give a singleton Artinian quotient with top Hankel ideal
and vanishing unit, in every degree. -/
private theorem zero_coefficients_quotients_artinian (n : ℕ) :
    Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      hankelIdeal (ZMod 1) n = ⊤ ∧
      (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 ∧
      IsArtinianRing (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  have htop : hankelIdeal (ZMod 1) n = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Subsingleton.elim (1 : Source (ZMod 1) n) 0]
    exact (hankelIdeal (ZMod 1) n).zero_mem
  have hsub : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  let : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := hsub
  have hunit : (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 :=
    Subsingleton.elim _ _
  exact ⟨hsub, htop, hunit, Ring.isArtinian_of_zero_eq_one hunit.symm⟩


/-- The degree-zero integer quotient is the full one-variable presentation:
its Hankel ideal is bottom and strictly smaller than the parametrization kernel,
and the quotient is not Artinian. -/
private theorem integer_degree_zero_not_artinian :
    hankelIdeal ℤ 0 = ⊥ ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) ∧
      ¬ IsArtinianRing (Source ℤ 0 ⧸ hankelIdeal ℤ 0) := by
  exact ⟨hankelIdeal_zero ℤ, hankelIdeal_zero_lt_ker ℤ,
    integer_hankel_quotient_not_artinian 0⟩


/-- The degree-one integer quotient retains its two-variable presentation and
bottom Hankel ideal, and is not Artinian. -/
private theorem integer_degree_one_not_artinian :
    hankelIdeal ℤ 1 = ⊥ ∧
      ¬ IsArtinianRing (Source ℤ 1 ⧸ hankelIdeal ℤ 1) := by
  exact ⟨hankelIdeal_one ℤ, integer_hankel_quotient_not_artinian 1⟩


/-- Every Hankel quotient with integer coefficients is not Artinian. -/
private theorem integer_quotients_not_artinian (n : ℕ) :
    ¬ IsArtinianRing (Source ℤ n ⧸ hankelIdeal ℤ n) := by
  exact integer_hankel_quotient_not_artinian n


end

end ToricIdeals.RationalNormalCurve.ArtinianModels
