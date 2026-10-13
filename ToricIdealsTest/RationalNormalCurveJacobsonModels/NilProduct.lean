/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Ring
import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.Artinian

/-!
# Jacobson Hankel quotients with nilpotents and zero divisors

The finite coefficient ring `ZMod 4` is Artinian and Jacobson, although `2` is
nonzero and square-zero. In every degree its Hankel quotient is Jacobson,
non-Artinian and nonreduced: the same square-zero constant survives.

The coefficient ring `ℚ × ℚ` is Artinian and Jacobson but is not a domain.
The complementary constants `(1, 0)` and `(0, 1)` remain nonzero in every
Hankel quotient and have zero product. These quotients are Jacobson,
non-Artinian and not domains.

All statements concern the quotient ring over itself and the full Hankel
presentation `Source R n ⧸ hankelIdeal R n`, including degrees zero and one.
The examples use finite-variable polynomial and quotient Jacobson instances;
they do not require reduced or domain coefficients. Constant-coefficient
evaluation kills every minor, and its quotient lift recovers each coefficient
from its constant-polynomial class.

## References

* Mathlib contributors, `Mathlib.RingTheory.Artinian.Module` and
  `Mathlib.RingTheory.Jacobson.Ring`, for finite, field and product Artinianity,
  Artinian Jacobson rings, and finite-variable polynomial and quotient closure.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Basic` and
  `Mathlib.RingTheory.Ideal.Quotient.Defs`, for constant-coefficient evaluation,
  its constant and variable laws, and quotient lifts.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and
  `ToricIdeals.RationalNormalCurve.Artinian`, for the Hankel presentation and
  the criterion for Artinianity over the quotient itself. The local
  constant-coefficient argument follows the proof of
  `ToricIdeals.RationalNormalCurve.quotient_isNoetherianRing_iff`.
-/

namespace ToricIdeals.RationalNormalCurve.JacobsonModels

/-- Finiteness supplies Artinianity of `ZMod 4` over itself. -/
private theorem mod_four_coefficients_artinian : IsArtinianRing (ZMod 4) := by
  apply isArtinian_of_finite

#print axioms mod_four_coefficients_artinian

/-- The Jacobson coefficient ring `ZMod 4` has a nonzero square-zero element. -/
private theorem mod_four_coefficients_jacobson_nonreduced :
    IsJacobsonRing (ZMod 4) ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      ¬ IsReduced (ZMod 4) := by
  let : IsArtinianRing (ZMod 4) := mod_four_coefficients_artinian
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨inferInstance, hne, hsq, ?_⟩
  intro hR
  let : IsReduced (ZMod 4) := hR
  have hn : IsNilpotent (2 : ZMod 4) := ⟨2, hsq⟩
  exact hne hn.eq_zero

#print axioms mod_four_coefficients_jacobson_nonreduced

/-- Every Hankel quotient over `ZMod 4` is Jacobson and retains the nonzero
square-zero constant `2`, so it is nonreduced and non-Artinian. -/
private theorem mod_four_quotients_jacobson_nonreduced (n : ℕ) :
    IsJacobsonRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      ¬ IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 ∧
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) ^ 2 = 0 ∧
      ¬ IsReduced (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  have hcoeff := mod_four_coefficients_jacobson_nonreduced
  let : IsJacobsonRing (ZMod 4) := hcoeff.1
  have hJac : IsJacobsonRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) :=
    inferInstance
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
  have hC (r : ZMod 4) :
      g (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C r)) = r := by
    simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
  have hne :
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 := by
    intro h
    apply hcoeff.2.1
    calc
      (2 : ZMod 4) =
          g (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) :=
        (hC 2).symm
      _ = 0 := by rw [h, map_zero]
  have hsq :
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) ^ 2 = 0 := by
    calc
      (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) ^ 2 =
          Ideal.Quotient.mk (hankelIdeal (ZMod 4) n)
            (MvPolynomial.C ((2 : ZMod 4) ^ 2)) := by simp only [map_pow]
      _ = 0 := by rw [hcoeff.2.2.1, map_zero, map_zero]
  have hnotArt : ¬ IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
    intro h
    have hs := (quotient_isArtinianRing_iff (ZMod 4) n).mp h
    exact hcoeff.2.1 (hs.elim _ _)
  have hnotReduced : ¬ IsReduced (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
    intro h
    let : IsReduced (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := h
    have hn : IsNilpotent
        (Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (MvPolynomial.C (2 : ZMod 4))) :=
      ⟨2, hsq⟩
    exact hne hn.eq_zero
  exact ⟨hJac, hnotArt, hne, hsq, hnotReduced⟩

#print axioms mod_four_quotients_jacobson_nonreduced

/-- The product of the two rational fields is Artinian over itself. -/
private theorem rat_product_coefficients_artinian : IsArtinianRing (ℚ × ℚ) := by
  let : IsArtinianRing ℚ := DivisionRing.instIsArtinianRing
  infer_instance

#print axioms rat_product_coefficients_artinian

/-- The Jacobson ring `ℚ × ℚ` is not a domain, with nonzero orthogonal constants. -/
private theorem rat_product_coefficients_jacobson_nondomain :
    IsJacobsonRing (ℚ × ℚ) ∧ ¬ IsDomain (ℚ × ℚ) ∧
      ((1, 0) : ℚ × ℚ) ≠ 0 ∧ ((0, 1) : ℚ × ℚ) ≠ 0 ∧
      ((1, 0) : ℚ × ℚ) * ((0, 1) : ℚ × ℚ) = 0 := by
  let : IsArtinianRing (ℚ × ℚ) := rat_product_coefficients_artinian
  have hleft : ((1, 0) : ℚ × ℚ) ≠ 0 := by
    intro h
    have h10 : (1 : ℚ) = 0 := congrArg Prod.fst h
    exact one_ne_zero h10
  have hright : ((0, 1) : ℚ × ℚ) ≠ 0 := by
    intro h
    have h10 : (1 : ℚ) = 0 := congrArg Prod.snd h
    exact one_ne_zero h10
  have hmul : ((1, 0) : ℚ × ℚ) * ((0, 1) : ℚ × ℚ) = 0 := by
    apply Prod.ext <;> simp
  have hnotDomain : ¬ IsDomain (ℚ × ℚ) := by
    intro h
    let : IsDomain (ℚ × ℚ) := h
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hzero
    · exact hleft hzero
    · exact hright hzero
  exact ⟨inferInstance, hnotDomain, hleft, hright, hmul⟩

#print axioms rat_product_coefficients_jacobson_nondomain

/-- Every Hankel quotient over `ℚ × ℚ` is Jacobson and non-Artinian, with
surviving nonzero orthogonal constant classes witnessing failure of the domain property. -/
private theorem rat_product_quotients_jacobson_nondomain (n : ℕ) :
    IsJacobsonRing (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) ∧
      ¬ IsArtinianRing (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) ∧
      Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
        (MvPolynomial.C ((1, 0) : ℚ × ℚ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
        (MvPolynomial.C ((0, 1) : ℚ × ℚ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((1, 0) : ℚ × ℚ)) *
        Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((0, 1) : ℚ × ℚ)) = 0 ∧
      ¬ IsDomain (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) := by
  have hcoeff := rat_product_coefficients_jacobson_nondomain
  let : IsJacobsonRing (ℚ × ℚ) := hcoeff.1
  have hJac : IsJacobsonRing (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) :=
    inferInstance
  let e : Source (ℚ × ℚ) n →+* (ℚ × ℚ) := MvPolynomial.constantCoeff
  have hI : hankelIdeal (ℚ × ℚ) n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero, sub_self]
  let g : (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) →+* (ℚ × ℚ) :=
    Ideal.Quotient.lift (hankelIdeal (ℚ × ℚ) n) e
      (fun _ hf => RingHom.mem_ker.mp (hI hf))
  have hC (r : ℚ × ℚ) :
      g (Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C r)) = r := by
    simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
  have hleft : Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
      (MvPolynomial.C ((1, 0) : ℚ × ℚ)) ≠ 0 := by
    intro h
    apply hcoeff.2.2.1
    calc
      ((1, 0) : ℚ × ℚ) = g (Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
          (MvPolynomial.C ((1, 0) : ℚ × ℚ))) := (hC _).symm
      _ = 0 := by rw [h, map_zero]
  have hright : Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
      (MvPolynomial.C ((0, 1) : ℚ × ℚ)) ≠ 0 := by
    intro h
    apply hcoeff.2.2.2.1
    calc
      ((0, 1) : ℚ × ℚ) = g (Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
          (MvPolynomial.C ((0, 1) : ℚ × ℚ))) := (hC _).symm
      _ = 0 := by rw [h, map_zero]
  have hmul :
      Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((1, 0) : ℚ × ℚ)) *
        Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((0, 1) : ℚ × ℚ)) = 0 := by
    calc
      Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((1, 0) : ℚ × ℚ)) *
          Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n) (MvPolynomial.C ((0, 1) : ℚ × ℚ)) =
          Ideal.Quotient.mk (hankelIdeal (ℚ × ℚ) n)
            (MvPolynomial.C (((1, 0) : ℚ × ℚ) * ((0, 1) : ℚ × ℚ))) := by
        simp only [map_mul]
      _ = 0 := by rw [hcoeff.2.2.2.2, map_zero, map_zero]
  have hnotArt : ¬ IsArtinianRing (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) := by
    intro h
    have hs := (quotient_isArtinianRing_iff (ℚ × ℚ) n).mp h
    exact hcoeff.2.2.1 (hs.elim _ _)
  have hnotDomain : ¬ IsDomain (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) := by
    intro h
    let : IsDomain (Source (ℚ × ℚ) n ⧸ hankelIdeal (ℚ × ℚ) n) := h
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hzero
    · exact hleft hzero
    · exact hright hzero
  exact ⟨hJac, hnotArt, hleft, hright, hmul, hnotDomain⟩

#print axioms rat_product_quotients_jacobson_nondomain

end ToricIdeals.RationalNormalCurve.JacobsonModels
