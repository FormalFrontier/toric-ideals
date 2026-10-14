/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.ExponentImage

/-!
# Surjectivity boundaries for the raw rational-normal-curve map

These examples concern the map from the full polynomial source to the full
bivariate polynomial target. Over the natural numbers, degree one reaches every
target polynomial, degree zero has constant image, and degree two reaches the
interior column monomial but misses the first target variable. The same
degree-two obstruction persists over the nonreduced ring `ZMod 4`. With zero
coefficients, the target collapses in degrees zero and two even though the
exponent maps are not surjective. Lifted natural-number coefficients give a
degree-one example in an independent coefficient universe.

The negative examples use the characteristic coefficient API and the exponent-image
criterion. They do not concern a Hankel quotient: in degree zero, the raw map
sends the sole source variable to `1`.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and
  `ToricIdeals.RationalNormalCurve.ExponentImage`, for the parametrization,
  its monomial and coefficient APIs and the exponent-image divisibility criterion.
* Mathlib contributors, `Mathlib.Data.Finsupp.Basic` and
  `Mathlib.Algebra.MonoidAlgebra.Defs`, for surjectivity of coefficient transport
  and the coefficient equivalence.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Basic`,
  `Mathlib.Data.ZMod.Basic` and `Mathlib.Algebra.Ring.ULift`, for polynomial
  induction, coefficient computations and the coefficient semirings.
-/

namespace ToricIdeals.RationalNormalCurve.SurjectivityModels

open MvPolynomial

noncomputable section

universe u

#check (∀ (R : Type u) [CommSemiring R] (n : ℕ),
  Function.Surjective (rncMap R n) ↔ n = 1 ∨ Subsingleton R : Prop)

/-- The first target-variable exponent is absent in degree zero. -/
private theorem degree_zero_first_exponent_not_mem :
    Finsupp.single (0 : Fin 2) 1 ∉ Set.range (rncExponent 0) := by
  intro hmem
  have hdiv := (mem_mrange_rncExponent_iff 0 (Finsupp.single (0 : Fin 2) 1)).mp
    (AddMonoidHom.mem_mrange.mpr hmem)
  simp at hdiv

/-- The first target-variable exponent is absent in degree two. -/
private theorem degree_two_first_exponent_not_mem :
    Finsupp.single (0 : Fin 2) 1 ∉ Set.range (rncExponent 2) := by
  intro hmem
  have hdiv := (mem_mrange_rncExponent_iff 2 (Finsupp.single (0 : Fin 2) 1)).mp
    (AddMonoidHom.mem_mrange.mpr hmem)
  simp at hdiv

/-- Degree one over the natural numbers reaches the full target, with the two
source variables mapping to the corresponding target variables. -/
private theorem nat_degree_one_surjective_and_variables :
    Function.Surjective (rncMap ℕ 1) ∧
      rncMap ℕ 1 (X (0 : Fin 2)) = X (0 : Fin 2) ∧
      rncMap ℕ 1 (X (1 : Fin 2)) = X (1 : Fin 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have hexp : Function.Surjective (rncExponent 1) :=
      fun d => ⟨d, rncExponent_one d⟩
    intro q
    obtain ⟨d, hd⟩ := Finsupp.mapDomain_surjective (M := ℕ) hexp q.coeff
    refine ⟨AddMonoidAlgebra.ofCoeff d, ?_⟩
    rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
    apply AddMonoidAlgebra.coeff_injective
    simpa only [AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff] using hd
  · rw [rncMap_X, ← rncExponent_single, rncExponent_one]
    rfl
  · rw [rncMap_X, ← rncExponent_single, rncExponent_one]
    rfl

/-- Every degree-zero image over the natural numbers is a constant polynomial. -/
private theorem nat_degree_zero_constant_image (p : Source ℕ 0) :
    ∃ c : ℕ, rncMap ℕ 0 p = C c := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨c, rncMap_C ℕ 0 c⟩
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      exact ⟨c + d, by simp only [map_add, hc, hd]⟩
  | mul_X p i hp =>
      obtain ⟨c, hc⟩ := hp
      have hi : i = (0 : Fin 1) := by
        apply Fin.ext
        omega
      subst i
      exact ⟨c, by simp [map_mul, hc, rncMap_X, coordinateExponent]⟩

/-- The degree-zero map has constant image and sends the sole source variable to
`1`, but the first target variable has no preimage over the natural numbers. -/
private theorem nat_degree_zero_variable_and_not_surjective :
    rncMap ℕ 0 (X (0 : Fin 1)) = 1 ∧
      (∀ p : Source ℕ 0, ∃ c : ℕ, rncMap ℕ 0 p = C c) ∧
      (∀ p : Source ℕ 0, rncMap ℕ 0 p ≠ X (0 : Fin 2)) ∧
      ¬ Function.Surjective (rncMap ℕ 0) := by
  have hmiss : ∀ p : Source ℕ 0, rncMap ℕ 0 p ≠ X (0 : Fin 2) := by
    intro p hp
    have hcoeff := coeff_rncMap_of_not_mem_range ℕ 0 p
      (Finsupp.single (0 : Fin 2) 1) degree_zero_first_exponent_not_mem
    rw [hp, coeff_X_same] at hcoeff
    exact Nat.one_ne_zero hcoeff
  refine ⟨by simp [rncMap_X, coordinateExponent], nat_degree_zero_constant_image,
    hmiss, ?_⟩
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (X (0 : Fin 2))
  exact hmiss p hp

/-- The interior column gives exponent `(1,1)` in degree two, whereas the first
target variable is missed by every source polynomial. -/
private theorem nat_degree_two_interior_and_not_surjective :
    rncMap ℕ 2 (X (1 : Fin 3)) =
        monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 ∧
      (∀ p : Source ℕ 2, rncMap ℕ 2 p ≠ X (0 : Fin 2)) ∧
      ¬ Function.Surjective (rncMap ℕ 2) := by
  have hmiss : ∀ p : Source ℕ 2, rncMap ℕ 2 p ≠ X (0 : Fin 2) := by
    intro p hp
    have hcoeff := coeff_rncMap_of_not_mem_range ℕ 2 p
      (Finsupp.single (0 : Fin 2) 1) degree_two_first_exponent_not_mem
    rw [hp, coeff_X_same] at hcoeff
    exact Nat.one_ne_zero hcoeff
  refine ⟨by simp [rncMap_X, coordinateExponent], hmiss, ?_⟩
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (X (0 : Fin 2))
  exact hmiss p hp

/-- Degree two is not onto over `ZMod 4`, which has a nonzero square-zero
coefficient. No domain assumption is used. -/
private theorem mod_four_degree_two_not_surjective_with_nilpotent :
    (∀ p : Source (ZMod 4) 2, rncMap (ZMod 4) 2 p ≠ X (0 : Fin 2)) ∧
      ¬ Function.Surjective (rncMap (ZMod 4) 2) ∧
      (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  have hmiss : ∀ p : Source (ZMod 4) 2,
      rncMap (ZMod 4) 2 p ≠ X (0 : Fin 2) := by
    intro p hp
    have hcoeff := coeff_rncMap_of_not_mem_range (ZMod 4) 2 p
      (Finsupp.single (0 : Fin 2) 1) degree_two_first_exponent_not_mem
    rw [hp, coeff_X_same] at hcoeff
    exact (by decide : (1 : ZMod 4) ≠ 0) hcoeff
  refine ⟨hmiss, ?_, by decide, by decide⟩
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (X (0 : Fin 2))
  exact hmiss p hp

/-- Zero coefficients make the raw maps onto in degrees zero and two despite
nonsurjectivity of both exponent maps; zero is a preimage of every target. -/
private theorem zero_coefficients_degree_zero_and_two_surjective :
    Function.Surjective (rncMap (ZMod 1) 0) ∧
      Function.Surjective (rncMap (ZMod 1) 2) ∧
      (∀ q : Target (ZMod 1),
        rncMap (ZMod 1) 0 (0 : Source (ZMod 1) 0) = q ∧
        rncMap (ZMod 1) 2 (0 : Source (ZMod 1) 2) = q) ∧
      ¬ Function.Surjective (rncExponent 0) ∧
      ¬ Function.Surjective (rncExponent 2) := by
  refine ⟨Function.surjective_to_subsingleton _, Function.surjective_to_subsingleton _,
    fun q => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro hsurj
    exact degree_zero_first_exponent_not_mem (hsurj (Finsupp.single (0 : Fin 2) 1))
  · intro hsurj
    exact degree_two_first_exponent_not_mem (hsurj (Finsupp.single (0 : Fin 2) 1))

/-- Degree one reaches the full target after lifting the coefficient universe. -/
private theorem lifted_nat_degree_one_surjective :
    Function.Surjective (rncMap (ULift.{u + 1} ℕ) 1) := by
  intro q
  refine ⟨q, ?_⟩
  induction q using MvPolynomial.induction_on with
  | C c => exact rncMap_C (ULift.{u + 1} ℕ) 1 c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, hp, rncMap_X, ← rncExponent_single, rncExponent_one]
      rfl

end

end ToricIdeals.RationalNormalCurve.SurjectivityModels
