/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module
import ToricIdeals.RationalNormalCurve

/-!
# Non-Artinian Hankel quotients over `ZMod 4`

The finite coefficient ring `ZMod 4` is Artinian but has a nonzero square-zero
constant. Its Hankel quotients are non-Artinian in every degree, while the
square-zero constant survives in each quotient. At degrees zero and one these
are the full one-variable and two-variable polynomial presentations, not
quotients by the parametrization kernel. The degree-two relation is a Hankel
minor.

The non-Artinian examples use endpoint evaluation onto `Polynomial (ZMod 4)`.
The indeterminate is regular over this nonreduced coefficient ring but is not
a unit, whereas a regular element of an Artinian ring must be a unit.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve.ArtinianModels

/-- Every Hankel quotient over `ZMod 4` has a non-Artinian polynomial image. -/
private theorem mod_four_quotient_not_artinian (n : ℕ) :
    ¬ IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  intro hQ
  let : IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := hQ
  let e : Source (ZMod 4) n →+* Polynomial (ZMod 4) :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin (n + 1) => if i = 0 then Polynomial.X else 0)
  have hI : hankelIdeal (ZMod 4) n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp [e, hankelMinor]
  let s : Polynomial (ZMod 4) →+* Source (ZMod 4) n :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin (n + 1)))
  have hes : e.comp s = RingHom.id (Polynomial (ZMod 4)) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [e, s]
    · simp [e, s]
  have he : Function.Surjective e := by
    intro f
    exact ⟨s f, RingHom.congr_fun hes f⟩
  let g : (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) →+*
      Polynomial (ZMod 4) :=
    Ideal.Quotient.lift (hankelIdeal (ZMod 4) n) e
      (fun _ hf => RingHom.mem_ker.mp (hI hf))
  have hg : Function.Surjective g :=
    Ideal.Quotient.lift_surjective_of_surjective (hankelIdeal (ZMod 4) n)
      (fun _ hf => RingHom.mem_ker.mp (hI hf)) he
  let : IsArtinianRing (Polynomial (ZMod 4)) := hg.isArtinianRing
  have hregular : IsRegular (Polynomial.X : Polynomial (ZMod 4)) :=
    Polynomial.isRegular_X (R := ZMod 4)
  have hunit : IsUnit (Polynomial.X : Polynomial (ZMod 4)) :=
    (IsArtinianRing.isUnit_iff_isRegular (R := Polynomial (ZMod 4))
      (x := (Polynomial.X : Polynomial (ZMod 4)))).mpr hregular
  exact Polynomial.not_isUnit_X (R := ZMod 4) hunit

/-- The square-zero coefficient `2` remains nonzero in each Hankel quotient. -/
private theorem mod_four_quotient_constant_two_ne_zero (n : ℕ) :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 := by
  let e : Source (ZMod 4) n →+* ZMod 4 := MvPolynomial.constantCoeff
  have hI : hankelIdeal (ZMod 4) n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero, sub_self]
  let g : (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) →+* ZMod 4 :=
    Ideal.Quotient.lift (hankelIdeal (ZMod 4) n) e
      (fun _ hf => RingHom.mem_ker.mp (hI hf))
  intro h
  have htwo : (2 : ZMod 4) = 0 := by
    simpa only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C, map_zero]
      using congrArg g h
  exact (by decide : (2 : ZMod 4) ≠ 0) htwo

/-- Finite Artinian coefficients need not be reduced. -/
private theorem mod_four_coefficients_artinian_nonreduced :
    IsArtinianRing (ZMod 4) ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      ¬ IsReduced (ZMod 4) := by
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨isArtinian_of_finite, hne, hsq, ?_⟩
  intro hR
  let : IsReduced (ZMod 4) := hR
  have hn : IsNilpotent (2 : ZMod 4) := ⟨2, hsq⟩
  exact hne hn.eq_zero


/-- The full polynomial quotients in degrees zero and one are non-Artinian. -/
private theorem mod_four_small_degree_quotients_not_artinian :
    hankelIdeal (ZMod 4) 0 = ⊥ ∧ hankelIdeal (ZMod 4) 1 = ⊥ ∧
      hankelIdeal (ZMod 4) 0 < RingHom.ker (rncMap (ZMod 4) 0) ∧
      ¬ IsArtinianRing (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) ∧
      ¬ IsArtinianRing (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  exact ⟨hankelIdeal_zero (ZMod 4), hankelIdeal_one (ZMod 4),
    hankelIdeal_zero_lt_ker (ZMod 4), mod_four_quotient_not_artinian 0,
    mod_four_quotient_not_artinian 1⟩


/-- Every quotient is non-Artinian and retains the nonzero square-zero constant. -/
private theorem mod_four_quotients_not_artinian (n : ℕ) :
    ¬ IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 ∧
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) ^ 2 = 0 := by
  refine ⟨mod_four_quotient_not_artinian n, mod_four_quotient_constant_two_ne_zero n, ?_⟩
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  calc
    (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) ^ 2 =
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C ((2 : ZMod 4) ^ 2)) := by
      simp only [map_pow]
    _ = 0 := by rw [hsq, map_zero, map_zero]


/-- The conic quotient is non-Artinian and satisfies its defining Hankel relation. -/
private theorem mod_four_conic_not_artinian :
    ¬ IsArtinianRing (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) -
          MvPolynomial.X (1 : Fin 3) ^ 2) = 0 := by
  refine ⟨mod_four_quotient_not_artinian 2, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hcast0 : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have hsucc1 : (1 : Fin 2).succ = (2 : Fin 3) := rfl
  have hsucc0 : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have hcast1 : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  simpa only [hankelMinor, hcast0, hsucc1, hsucc0, hcast1, pow_two] using
    (minor_mem (ZMod 4) 2 (⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩ : MinorIndex 2))


end ToricIdeals.RationalNormalCurve.ArtinianModels
