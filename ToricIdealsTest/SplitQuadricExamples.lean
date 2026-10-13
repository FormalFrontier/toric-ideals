/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

/-!
# Split quadric coefficient models

Boundary cases and polynomial computations through the public API, including
zero rings, positive characteristic, zero divisors and integer coefficients.
-/

noncomputable section

universe u

namespace ToricIdealsTest.SplitQuadricExamples

open SplitQuadric SplitQuadric.Examples ToricIdeals.SplitQuadric

variable (A : Type u) [CommRing A]

/-- The field-coefficient hypotheses have concrete inhabitants. -/
@[instance_reducible] private def rational_field : Field ℚ := inferInstance

private theorem rational_domain : IsDomain ℚ := inferInstance

@[instance_reducible] private def prime_field : Field (ZMod 2) := inferInstance

/-- Positive characteristic is allowed. -/
private theorem positive_characteristic : (2 : ZMod 2) = 0 := by decide

private theorem prime_field_nonzero_coordinate : w (ZMod 2) ≠ 0 := w_ne_zero (ZMod 2)

/-- Zero coefficients are also allowed in all the definitions. -/
private theorem zero_coordinate_ring : Subsingleton (CoordinateRing (ZMod 1)) := inferInstance

private theorem zero_coordinate : w (ZMod 1) = 0 := coordinate_eq_zero (ZMod 1) 0

/-- A non-domain coefficient ring supplies genuine nonzero zero divisors in the quotient. -/
private theorem coefficient_zero_divisors_mod_six :
    ∃ a b : CoordinateRing (ZMod 6), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine ⟨coefficientMap (ZMod 6) 2, coefficientMap (ZMod 6) 3, ?_⟩
  exact coefficient_zero_divisors (ZMod 6) (by decide) (by decide) (by decide)

private theorem rational_proper_relation : relationIdeal ℚ ≠ ⊤ := relationIdeal_ne_top ℚ

/-- Canonical chart models exist independently of the comparison equivalence. -/
private theorem quadric_localization_model :
    IsLocalization.Away (w ℚ) (Localization.Away (w ℚ)) := inferInstance

private theorem parameter_localization_model :
    IsLocalization.Away (W ℚ) (Localization.Away (W ℚ)) := inferInstance

/-- A concrete use of the universal morphism: evaluating the coordinate `w` at any coefficient. -/
private theorem axis_evaluation (a : A) : axisPoint A a (w A) = a := axisPoint_w A a

/-- The range equivalence sends the coordinate `x` to `WT`, not to an independent variable. -/
private theorem range_coordinate : (rangeEquiv ℤ (x ℤ) : ParameterPolynomial ℤ) = W ℤ * T ℤ := by
  rw [rangeEquiv_coe_apply, phi_x]

/-- The determinant identity can also be checked through the injective parametrization. -/
private theorem determinant_via_injection : w ℤ * z ℤ = x ℤ * y ℤ := by
  apply phi_injective ℤ
  simp only [map_mul, phi_w, phi_z, phi_x, phi_y]
  ring

/-- A field hypothesis is not needed for the domain conclusion. -/
private theorem integer_domain : IsDomain (CoordinateRing ℤ) :=
  (coordinateRing_isDomain_iff ℤ).mpr inferInstance

/-- The relation ideal over the rationals is prime, not merely proper. -/
private theorem rational_prime_relation : (relationIdeal ℚ).IsPrime :=
  (relationIdeal_isPrime_iff ℚ).mpr inferInstance

/-- In the zero-ring case the quotient parametrization is also surjective. -/
private theorem zero_surjective : Function.Surjective (phi (ZMod 1)) := by
  intro p
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Distinct integer coefficients remain distinct in the coordinate algebra. -/
private theorem coefficientMap_int_two_ne_three :
    coefficientMap ℤ 2 ≠ coefficientMap ℤ 3 := by
  intro h
  exact (by norm_num : (2 : ℤ) ≠ 3) (SplitQuadric.coefficientMap_injective ℤ h)

/-- The `wz` versus `xy` congruence with coefficient `2` over the integers. -/
private theorem integer_two_monomials_mem_relationIdeal :
    MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 3 1) (2 : ℤ) -
        MvPolynomial.monomial (Finsupp.single 1 1 + Finsupp.single 2 1) 2 ∈
      relationIdeal ℤ := by
  let m : Fin 4 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 3 1
  have hn : normal (exponentMap m) =
      Finsupp.single 1 1 + Finsupp.single 2 1 := by
    rw [normal_exponentMap]
    ext i
    fin_cases i
    · change reduce m (0 : Fin 4) =
        (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) 0
      simp [m]
    · change reduce m (1 : Fin 4) =
        (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) 1
      simp [m]
    · change reduce m (2 : Fin 4) =
        (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) 2
      simp [m]
    · change reduce m (3 : Fin 4) =
        (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) 3
      simp [m]
  simpa only [hn, m] using monomial_sub_normal_mem_relationIdeal m (2 : ℤ)

/-- A generator product computed through the bridge, over any coefficient ring. -/
private theorem mapDomain_generator_product :
    AddMonoidAlgebra.mapDomainAlgHom A A exponentMap
        (MvPolynomial.X 0 * MvPolynomial.X 3) = W A * (Y A * T A) := by
  rw [← theta_eq_mapDomainAlgHom A]
  simp [parameterValues]

/-- A nonzero nilpotent coefficient remains nonzero and nilpotent in the quotient. -/
private theorem nilpotent_coefficient :
    coefficientMap (ZMod 4) 2 ≠ 0 ∧ (coefficientMap (ZMod 4) 2) ^ 2 = 0 := by
  constructor
  · intro h
    exact (by decide : (2 : ZMod 4) ≠ 0)
      (SplitQuadric.coefficientMap_injective (ZMod 4) (by simpa using h))
  · rw [← map_pow]
    have h : (2 : ZMod 4) ^ 2 = 0 := by decide
    rw [h, map_zero]

private theorem zero_not_domain : ¬ IsDomain (CoordinateRing (ZMod 1)) := by
  intro h
  let := h
  exact zero_ne_one (Subsingleton.elim (0 : CoordinateRing (ZMod 1)) 1)

private theorem zero_relation_not_prime : ¬ (relationIdeal (ZMod 1)).IsPrime := by
  intro h
  have hd := (relationIdeal_isPrime_iff (ZMod 1)).mp h
  exact zero_not_domain ((coordinateRing_isDomain_iff (ZMod 1)).mpr hd)

end ToricIdealsTest.SplitQuadricExamples
