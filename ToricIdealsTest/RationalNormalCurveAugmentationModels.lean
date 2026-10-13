/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ToricIdeals.RationalNormalCurve

/-!
# Coefficients and zero evaluation in small-degree Hankel quotients

Coefficients embed in the full Hankel quotient over every commutative ring,
in every degree. The proof uses the inclusion of the Hankel ideal in the
parametrization kernel and preservation of constants, without identifying the
quotient with a kernel quotient or a parametrization image.

Over the integers, the degree-zero and degree-one ideals are bottom. The
quotients therefore retain the full one-variable and two-variable polynomial
rings, respectively. Their variable classes are nonzero, and the two classes
in degree one are distinct with nonzero difference. Applying the bottom-ideal
quotient equivalence and then constant coefficient evaluates the displayed
mixed representatives to `37`. In contrast, the degree-zero parametrization
sends the sole variable to `1`.

Over `ZMod 1`, every degree gives a singleton quotient, with the coefficient
class of zero and every variable class equal to one. This boundary case is
compatible with coefficient injectivity and requires no nontriviality premise.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  Hankel presentation and the small-degree ideal identities. The coefficient
  argument follows the constant-preservation proof in `quotient_isReduced_iff`.
* Formal Frontier Agents, the rational-normal-curve coordinate-regularity
  models, supplies the bottom-ideal quotient and singleton-ring proof patterns.
* Mathlib contributors, multivariate-polynomial coefficients, monoid-algebra
  exponent maps, and ideal quotients, supply the evaluation and injection APIs.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.CoefficientAndSmallDegreeModels

noncomputable section

universe u

/-- Constant classes are distinct whenever their coefficients are distinct,
over any commutative coefficient ring and in every degree. -/
private theorem coefficient_classes_injective (R : Type u) [CommRing R] (n : ℕ) :
    Function.Injective
      ((Ideal.Quotient.mk (hankelIdeal R n)).comp (MvPolynomial.C : R →+* Source R n)) := by
  intro a b hab
  change Ideal.Quotient.mk (hankelIdeal R n) (C a) =
    Ideal.Quotient.mk (hankelIdeal R n) (C b) at hab
  have hker := hankelIdeal_le_ker R n (Ideal.Quotient.eq.mp hab)
  change rncMap R n (C a - C b) = 0 at hker
  rw [map_sub, rncMap_C, rncMap_C, sub_eq_zero] at hker
  exact MvPolynomial.C_injective (Fin 2) R hker

/-- The full degree-zero integer quotient retains a nonzero variable. Its
constant-coefficient evaluation differs from the monomial parametrization. -/
private theorem integer_degree_zero_variable_and_evaluation :
    hankelIdeal ℤ 0 = ⊥ ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      MvPolynomial.constantCoeff
        ((RingEquiv.quotientBot (Source ℤ 0))
          ((Ideal.quotEquivOfEq (hankelIdeal_zero ℤ))
            (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1) + C (37 : ℤ))))) = 37 ∧
      rncMap ℤ 0 (X (0 : Fin 1)) = 1 := by
  have hmk : Function.Injective (Ideal.Quotient.mk (hankelIdeal ℤ 0)) := by
    rw [hankelIdeal_zero]
    intro p q hpq
    have h := congrArg (RingEquiv.quotientBot (Source ℤ 0)) hpq
    simpa only [RingEquiv.quotientBot_mk] using h
  refine ⟨hankelIdeal_zero ℤ, ?_, ?_, ?_⟩
  · intro hzero
    have hpoly : (X (0 : Fin 1) : Source ℤ 0) = 0 :=
      hmk (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (0 : Fin 1) hpoly
  · simp only [Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk, map_add,
      MvPolynomial.constantCoeff_X, MvPolynomial.constantCoeff_C, zero_add]
  · simp [rncMap_X, coordinateExponent]

/-- The full degree-one integer quotient retains both variables and their
nonzero difference, while zero-variable evaluation of a mixed polynomial is `37`. -/
private theorem integer_degree_one_distinct_variables_and_evaluation :
    hankelIdeal ℤ 1 = ⊥ ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠
        Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2)) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2) - X (1 : Fin 2)) ≠ 0 ∧
      MvPolynomial.constantCoeff
        ((RingEquiv.quotientBot (Source ℤ 1))
          ((Ideal.quotEquivOfEq (hankelIdeal_one ℤ))
            (Ideal.Quotient.mk (hankelIdeal ℤ 1)
              (X (0 : Fin 2) * X (1 : Fin 2) + X (0 : Fin 2) + C (37 : ℤ))))) = 37 := by
  have hmk : Function.Injective (Ideal.Quotient.mk (hankelIdeal ℤ 1)) := by
    rw [hankelIdeal_one]
    intro p q hpq
    have h := congrArg (RingEquiv.quotientBot (Source ℤ 1)) hpq
    simpa only [RingEquiv.quotientBot_mk] using h
  have hdistinct : Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2)) := by
    intro heq
    have hindex := MvPolynomial.X_injective (hmk heq)
    exact (by decide : (0 : Fin 2) ≠ 1) hindex
  refine ⟨hankelIdeal_one ℤ, ?_, ?_, hdistinct, ?_, ?_⟩
  · intro hzero
    have hpoly : (X (0 : Fin 2) : Source ℤ 1) = 0 :=
      hmk (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (0 : Fin 2) hpoly
  · intro hzero
    have hpoly : (X (1 : Fin 2) : Source ℤ 1) = 0 :=
      hmk (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (1 : Fin 2) hpoly
  · intro hzero
    apply hdistinct
    apply sub_eq_zero.mp
    simpa only [map_sub] using hzero
  · simp only [Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk, map_add, map_mul,
      MvPolynomial.constantCoeff_X, MvPolynomial.constantCoeff_C, zero_mul, zero_add]

/-- With zero coefficients, every degree gives a singleton quotient, and the
coefficient class of zero and every variable class equal one. -/
private theorem zero_coefficients_all_degrees_singleton (n : ℕ) :
    Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      ((Ideal.Quotient.mk (hankelIdeal (ZMod 1) n)).comp
        (MvPolynomial.C : ZMod 1 →+* Source (ZMod 1) n)) (0 : ZMod 1) = 1 ∧
      ∀ i : Fin (n + 1), Ideal.Quotient.mk (hankelIdeal (ZMod 1) n) (X i) = 1 := by
  have hone : (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) n))
        (Subsingleton.elim (1 : Source (ZMod 1) n) 0)
  refine ⟨subsingleton_of_zero_eq_one hone.symm, ?_, ?_⟩
  · simpa only [map_zero] using hone.symm
  · intro i
    simpa only [map_one] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) n))
        (Subsingleton.elim (X i : Source (ZMod 1) n) 1)

end

end ToricIdeals.RationalNormalCurve.CoefficientAndSmallDegreeModels
