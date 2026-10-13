/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ring
import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.Artinian

/-!
# Zero and rational coefficients in Hankel quotients

The zero coefficient ring `ZMod 1` is Jacobson, and its polynomial sources and
Hankel quotients are singleton Jacobson zero rings in every degree. Their Hankel
ideals are top and their multiplicative identities vanish.

The rational numbers are Jacobson because they form a field. Every Hankel
quotient over the rationals is also Jacobson: its source has the finite variable
set `Fin (n + 1)`, and quotients of Jacobson rings are Jacobson. Nevertheless,
these quotients are not Artinian in any degree.

At degree zero the quotient is the full polynomial ring on `Fin 1` modulo the
bottom ideal, and at degree one it is the full polynomial ring on `Fin 2`
modulo the bottom ideal. The bottom-ideal equivalences identify each polynomial
class with that same polynomial. Since the rationals are nontrivial, the
degree-zero Hankel ideal is strictly smaller than the parametrization kernel;
the Hankel quotient is not replaced by the parametrization image.

## References

* `ToricIdeals.RationalNormalCurve` supplies the Hankel presentation and its
  degree-zero and degree-one boundary results.
* `ToricIdeals.RationalNormalCurve.Artinian` supplies the criterion for
  Artinianity of the full Hankel quotient.
* Mathlib contributors, `Mathlib.RingTheory.Jacobson.Ring` and
  `Mathlib.RingTheory.Artinian.Module`, for Jacobsonness of Artinian rings,
  finite-variable polynomial rings and quotients.
* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations`, for
  the bottom-ideal ring equivalence and its representative law.
-/

namespace ToricIdeals.RationalNormalCurve.JacobsonModels

/-- The coefficient ring `ZMod 1` is a singleton Jacobson ring with vanishing unit. -/
private theorem zero_coefficients_jacobson :
    Subsingleton (ZMod 1) ∧ (1 : ZMod 1) = 0 ∧ IsJacobsonRing (ZMod 1) := by
  have hunit : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
  letI : IsArtinianRing (ZMod 1) := Ring.isArtinian_of_zero_eq_one hunit.symm
  exact ⟨inferInstance, hunit, inferInstance⟩

#print axioms zero_coefficients_jacobson

/-- In every degree, zero coefficients give singleton Jacobson polynomial
sources and Hankel quotients, with top Hankel ideal and vanishing identities. -/
private theorem zero_coefficients_sources_quotients_jacobson (n : ℕ) :
    Subsingleton (Source (ZMod 1) n) ∧
      (1 : Source (ZMod 1) n) = 0 ∧ IsJacobsonRing (Source (ZMod 1) n) ∧
      Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      hankelIdeal (ZMod 1) n = ⊤ ∧
      (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 ∧
      IsJacobsonRing (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  letI : Subsingleton (ZMod 1) := zero_coefficients_jacobson.1
  letI : IsJacobsonRing (ZMod 1) := zero_coefficients_jacobson.2.2
  have hsource : Subsingleton (Source (ZMod 1) n) := inferInstance
  have htop : hankelIdeal (ZMod 1) n = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Subsingleton.elim (1 : Source (ZMod 1) n) 0]
    exact (hankelIdeal (ZMod 1) n).zero_mem
  have hsub : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  letI : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := hsub
  have hunit : (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 :=
    Subsingleton.elim _ _
  letI : IsJacobsonRing (Source (ZMod 1) n) :=
    MvPolynomial.isJacobsonRing_MvPolynomial_fin (n + 1)
  exact ⟨hsource, Subsingleton.elim _ _, inferInstance, hsub, htop, hunit,
    isJacobsonRing_quotient⟩

#print axioms zero_coefficients_sources_quotients_jacobson

/-- The rational coefficient field is Artinian and Jacobson, and is nontrivial. -/
private theorem rational_coefficients_artinian_jacobson :
    Nontrivial ℚ ∧ IsArtinianRing ℚ ∧ IsJacobsonRing ℚ := by
  letI : IsArtinianRing ℚ := DivisionRing.instIsArtinianRing
  exact ⟨inferInstance, inferInstance, inferInstance⟩

#print axioms rational_coefficients_artinian_jacobson

/-- Every rational Hankel quotient is Jacobson but not Artinian. Jacobsonness
uses finite-variable polynomial and quotient closure; non-Artinianity uses the
criterion that an Artinian Hankel quotient has singleton coefficients. -/
private theorem rational_quotients_jacobson_not_artinian (n : ℕ) :
    IsJacobsonRing (Source ℚ n ⧸ hankelIdeal ℚ n) ∧
      ¬ IsArtinianRing (Source ℚ n ⧸ hankelIdeal ℚ n) := by
  letI : Nontrivial ℚ := rational_coefficients_artinian_jacobson.1
  letI : IsJacobsonRing ℚ := rational_coefficients_artinian_jacobson.2.2
  letI : IsJacobsonRing (Source ℚ n) :=
    MvPolynomial.isJacobsonRing_MvPolynomial_fin (n + 1)
  refine ⟨isJacobsonRing_quotient, ?_⟩
  intro hArt
  have hsub : Subsingleton ℚ := (quotient_isArtinianRing_iff ℚ n).mp hArt
  exact (zero_ne_one : (0 : ℚ) ≠ 1) (@Subsingleton.elim ℚ hsub 0 1)

#print axioms rational_quotients_jacobson_not_artinian

/-- Degree zero over the rationals retains the full one-variable polynomial
quotient by bottom. Its equivalence fixes polynomial representatives, its
Hankel ideal is strictly below the parametrization kernel, and the quotient
is Jacobson but not Artinian. -/
private theorem rational_degree_zero_presentation :
    Source ℚ 0 = MvPolynomial (Fin 1) ℚ ∧
      hankelIdeal ℚ 0 = (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      (∃ e : (Source ℚ 0 ⧸ hankelIdeal ℚ 0) ≃+* MvPolynomial (Fin 1) ℚ,
        ∀ f : MvPolynomial (Fin 1) ℚ,
          e (Ideal.Quotient.mk (hankelIdeal ℚ 0) f) = f) ∧
      hankelIdeal ℚ 0 < RingHom.ker (rncMap ℚ 0) ∧
      IsJacobsonRing (Source ℚ 0 ⧸ hankelIdeal ℚ 0) ∧
      ¬ IsArtinianRing (Source ℚ 0 ⧸ hankelIdeal ℚ 0) := by
  letI : Nontrivial ℚ := rational_coefficients_artinian_jacobson.1
  refine ⟨rfl, hankelIdeal_zero ℚ, ?_, hankelIdeal_zero_lt_ker ℚ,
    rational_quotients_jacobson_not_artinian 0⟩
  rw [hankelIdeal_zero ℚ]
  exact ⟨RingEquiv.quotientBot (MvPolynomial (Fin 1) ℚ),
    fun f => RingEquiv.quotientBot_mk f⟩

#print axioms rational_degree_zero_presentation

/-- Degree one over the rationals retains the full two-variable polynomial
quotient by bottom. Its bottom-ideal equivalence fixes representatives, and
the quotient is Jacobson but not Artinian. -/
private theorem rational_degree_one_presentation :
    Source ℚ 1 = MvPolynomial (Fin 2) ℚ ∧
      hankelIdeal ℚ 1 = (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      (∃ e : (Source ℚ 1 ⧸ hankelIdeal ℚ 1) ≃+* MvPolynomial (Fin 2) ℚ,
        ∀ f : MvPolynomial (Fin 2) ℚ,
          e (Ideal.Quotient.mk (hankelIdeal ℚ 1) f) = f) ∧
      IsJacobsonRing (Source ℚ 1 ⧸ hankelIdeal ℚ 1) ∧
      ¬ IsArtinianRing (Source ℚ 1 ⧸ hankelIdeal ℚ 1) := by
  refine ⟨rfl, hankelIdeal_one ℚ, ?_, rational_quotients_jacobson_not_artinian 1⟩
  rw [hankelIdeal_one ℚ]
  exact ⟨RingEquiv.quotientBot (MvPolynomial (Fin 2) ℚ),
    fun f => RingEquiv.quotientBot_mk f⟩

#print axioms rational_degree_one_presentation

end ToricIdeals.RationalNormalCurve.JacobsonModels
