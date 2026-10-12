/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.Homogeneous

/-!
# Homogeneous Hankel ideals and coefficient models

The one-variable and two-variable bottom-ideal models, the conic's single
quadratic, and the twisted cubic's three ordered quadratics use the existing
Hankel presentation. The fixed-degree ideal proofs use Mathlib's homogeneous
span theorem, independently of `hankelIdeal_isHomogeneous`. Integer,
characteristic-two, nilpotent, product and zero coefficients are included.
A polynomial with both quadratic and cubic terms in the conic ideal supplies
component-membership and componentwise-membership uses of Mathlib's API.

## Limitations

Degree label `2` does not imply total degree `2` for a zero generator. The
zero coefficient ring has only zero polynomials and preserves every degree
label. The inhomogeneous parametrization-kernel example is local to integer
coefficients and `n = 0`; it is not the Hankel ideal. No quotient grading,
rank or Hilbert-function formula is asserted.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  source, ordered minors, ideal membership and small-degree boundary API.
* Mathlib contributors, the standard polynomial grading, homogeneous-span
  and homogeneous-component membership results, and coefficient-ring API.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.HomogeneityModels

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private def conicColumns : MinorIndex 2 := ⟨(0, 1), by decide⟩

private def cubicFirstColumns : MinorIndex 3 := ⟨(0, 1), by decide⟩

private def cubicOuterColumns : MinorIndex 3 := ⟨(0, 2), by decide⟩

private def cubicLastColumns : MinorIndex 3 := ⟨(1, 2), by decide⟩

private theorem degree_zero_one_variable_bottom_homogeneous
    (R : Type u) [CommRing R] :
    Source R 0 = MvPolynomial (Fin 1) R ∧ hankelIdeal R 0 = ⊥ ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 1) R) (hankelIdeal R 0) := by
  refine ⟨rfl, hankelIdeal_zero R, ?_⟩
  rw [hankelIdeal_zero]
  exact Ideal.IsHomogeneous.bot _

private theorem degree_one_two_variable_bottom_homogeneous
    (R : Type u) [CommRing R] :
    Source R 1 = MvPolynomial (Fin 2) R ∧ hankelIdeal R 1 = ⊥ ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 2) R) (hankelIdeal R 1) := by
  refine ⟨rfl, hankelIdeal_one R, ?_⟩
  rw [hankelIdeal_one]
  exact Ideal.IsHomogeneous.bot _

private theorem conic_columns_exhaustive : ∀ p : MinorIndex 2, p = conicColumns := by
  decide

private theorem cubic_columns_exhaustive : ∀ p : MinorIndex 3,
    p = cubicFirstColumns ∨ p = cubicOuterColumns ∨ p = cubicLastColumns := by
  decide

private theorem conic_minor_eq (R : Type u) [CommRing R] :
    hankelMinor R 2 conicColumns =
      (X 0 * X 2 - X 1 * X 1 : Source R 2) := rfl

private theorem cubic_minors_eq (R : Type u) [CommRing R] :
    hankelMinor R 3 cubicFirstColumns = (X 0 * X 2 - X 1 * X 1 : Source R 3) ∧
      hankelMinor R 3 cubicOuterColumns = (X 0 * X 3 - X 1 * X 2 : Source R 3) ∧
      hankelMinor R 3 cubicLastColumns = (X 1 * X 3 - X 2 * X 2 : Source R 3) :=
  ⟨rfl, rfl, rfl⟩

private theorem conic_ideal_eq_span (R : Type u) [CommRing R] :
    hankelIdeal R 2 = Ideal.span {(X 0 * X 2 - X 1 * X 1 : Source R 2)} := by
  rw [hankelIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    rw [conic_columns_exhaustive p, conic_minor_eq]
    exact Set.mem_singleton _
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨conicColumns, (conic_minor_eq R).trans hf.symm⟩

private theorem conic_minor_isHomogeneous (R : Type u) [CommRing R] :
    (hankelMinor R 2 conicColumns).IsHomogeneous 2 := by
  rw [conic_minor_eq]
  exact ((isHomogeneous_X R (0 : Fin 3)).mul (isHomogeneous_X R 2)).sub
    ((isHomogeneous_X R (1 : Fin 3)).mul (isHomogeneous_X R 1))

private theorem conic_ideal_isHomogeneous (R : Type u) [CommRing R] :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 3) R) (hankelIdeal R 2) := by
  rw [conic_ideal_eq_span]
  apply Ideal.homogeneous_span (homogeneousSubmodule (Fin 3) R)
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  subst f
  refine ⟨2, ?_⟩
  rw [mem_homogeneousSubmodule, ← conic_minor_eq R]
  exact conic_minor_isHomogeneous R

private theorem cubic_minors_isHomogeneous (R : Type u) [CommRing R] :
    (hankelMinor R 3 cubicFirstColumns).IsHomogeneous 2 ∧
      (hankelMinor R 3 cubicOuterColumns).IsHomogeneous 2 ∧
      (hankelMinor R 3 cubicLastColumns).IsHomogeneous 2 := by
  rw [(cubic_minors_eq R).1, (cubic_minors_eq R).2.1, (cubic_minors_eq R).2.2]
  exact ⟨((isHomogeneous_X R (0 : Fin 4)).mul (isHomogeneous_X R 2)).sub
      ((isHomogeneous_X R (1 : Fin 4)).mul (isHomogeneous_X R 1)),
    ((isHomogeneous_X R (0 : Fin 4)).mul (isHomogeneous_X R 3)).sub
      ((isHomogeneous_X R (1 : Fin 4)).mul (isHomogeneous_X R 2)),
    ((isHomogeneous_X R (1 : Fin 4)).mul (isHomogeneous_X R 3)).sub
      ((isHomogeneous_X R (2 : Fin 4)).mul (isHomogeneous_X R 2))⟩

private theorem cubic_ideal_isHomogeneous (R : Type u) [CommRing R] :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 4) R) (hankelIdeal R 3) := by
  rw [hankelIdeal]
  apply Ideal.homogeneous_span (homogeneousSubmodule (Fin 4) R)
  rintro f ⟨p, rfl⟩
  refine ⟨2, ?_⟩
  rw [mem_homogeneousSubmodule]
  rcases cubic_columns_exhaustive p with h | h | h
  · rw [h]
    exact (cubic_minors_isHomogeneous R).1
  · rw [h]
    exact (cubic_minors_isHomogeneous R).2.1
  · rw [h]
    exact (cubic_minors_isHomogeneous R).2.2

private theorem conic_exponents_distinct :
    outerExponent 2 conicColumns ≠ innerExponent 2 conicColumns := by
  intro h
  have heval := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
  simp [outerExponent, innerExponent, conicColumns] at heval

private theorem conic_minor_coefficients (R : Type u) [CommRing R] :
    (hankelMinor R 2 conicColumns).coeff (outerExponent 2 conicColumns) = 1 ∧
      (hankelMinor R 2 conicColumns).coeff (innerExponent 2 conicColumns) = -1 := by
  constructor <;> rw [← monomial_outer_sub_inner R 2 conicColumns, coeff_sub] <;>
    simp [conic_exponents_distinct, Ne.symm conic_exponents_distinct]

private theorem conic_minor_ne_zero (R : Type u) [CommRing R] [Nontrivial R] :
    hankelMinor R 2 conicColumns ≠ 0 := by
  intro hzero
  have hcoeff := (conic_minor_coefficients R).1
  rw [hzero] at hcoeff
  simp at hcoeff

private theorem conic_scaled_outer_coefficient (R : Type u) [CommRing R] (r : R) :
    (C r * hankelMinor R 2 conicColumns).coeff (outerExponent 2 conicColumns) = r := by
  rw [coeff_C_mul, (conic_minor_coefficients R).1, mul_one]

private theorem integer_conic_and_cubic_homogeneous_nonzero :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℤ) (hankelIdeal ℤ 2) ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 4) ℤ) (hankelIdeal ℤ 3) ∧
      hankelMinor ℤ 2 conicColumns ≠ 0 ∧
      (hankelMinor ℤ 2 conicColumns).totalDegree = 2 ∧
      hankelMinor ℤ 2 conicColumns ∈ hankelIdeal ℤ 2 ∧
      (1 : Source ℤ 2) ∉ hankelIdeal ℤ 2 := by
  refine ⟨conic_ideal_isHomogeneous ℤ, cubic_ideal_isHomogeneous ℤ,
    conic_minor_ne_zero ℤ,
    (conic_minor_isHomogeneous ℤ).totalDegree (conic_minor_ne_zero ℤ),
    minor_mem ℤ 2 conicColumns, ?_⟩
  intro hmem
  have hzero := hankelIdeal_le_ker ℤ 2 hmem
  change rncMap ℤ 2 1 = 0 at hzero
  exact one_ne_zero (by simpa only [map_one] using hzero)

private theorem binary_conic_two_supported_terms :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 3) (ZMod 2)) (hankelIdeal (ZMod 2) 2) ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 4) (ZMod 2)) (hankelIdeal (ZMod 2) 3) ∧
      outerExponent 2 conicColumns ≠ innerExponent 2 conicColumns ∧
      (hankelMinor (ZMod 2) 2 conicColumns).coeff (innerExponent 2 conicColumns) = 1 ∧
      outerExponent 2 conicColumns ∈ (hankelMinor (ZMod 2) 2 conicColumns).support ∧
      innerExponent 2 conicColumns ∈ (hankelMinor (ZMod 2) 2 conicColumns).support ∧
      hankelMinor (ZMod 2) 2 conicColumns ≠ 0 := by
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hinner : (hankelMinor (ZMod 2) 2 conicColumns).coeff
      (innerExponent 2 conicColumns) = 1 :=
    (conic_minor_coefficients (ZMod 2)).2.trans hneg
  refine ⟨conic_ideal_isHomogeneous (ZMod 2), cubic_ideal_isHomogeneous (ZMod 2),
    conic_exponents_distinct, hinner, ?_, ?_, conic_minor_ne_zero (ZMod 2)⟩
  · rw [mem_support_iff, (conic_minor_coefficients (ZMod 2)).1]
    exact one_ne_zero
  · rw [mem_support_iff, hinner]
    exact one_ne_zero

private theorem mod_four_nilpotent_quadratic :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 3) (ZMod 4)) (hankelIdeal (ZMod 4) 2) ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 4) (ZMod 4)) (hankelIdeal (ZMod 4) 3) ∧
      (C (2 : ZMod 4) * hankelMinor (ZMod 4) 2 conicColumns).IsHomogeneous 2 ∧
      C (2 : ZMod 4) * hankelMinor (ZMod 4) 2 conicColumns ∈ hankelIdeal (ZMod 4) 2 ∧
      C (2 : ZMod 4) * hankelMinor (ZMod 4) 2 conicColumns ≠ 0 ∧
      (C (2 : ZMod 4) * hankelMinor (ZMod 4) 2 conicColumns) ^ 2 = 0 := by
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨conic_ideal_isHomogeneous (ZMod 4), cubic_ideal_isHomogeneous (ZMod 4),
    (conic_minor_isHomogeneous (ZMod 4)).C_mul 2,
    Ideal.mul_mem_left _ _ (minor_mem (ZMod 4) 2 conicColumns), ?_, ?_⟩
  · intro hzero
    have hcoeff := conic_scaled_outer_coefficient (ZMod 4) 2
    rw [hzero] at hcoeff
    exact hne (by simpa using hcoeff.symm)
  · rw [mul_pow, ← map_pow, hsq, map_zero, zero_mul]

private theorem integer_product_quadratic_zero_divisor :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin 3) (ℤ × ℤ)) (hankelIdeal (ℤ × ℤ) 2) ∧
      Ideal.IsHomogeneous (homogeneousSubmodule (Fin 4) (ℤ × ℤ)) (hankelIdeal (ℤ × ℤ) 3) ∧
      (C ((1, 0) : ℤ × ℤ) * hankelMinor (ℤ × ℤ) 2 conicColumns).IsHomogeneous 2 ∧
      C ((1, 0) : ℤ × ℤ) * hankelMinor (ℤ × ℤ) 2 conicColumns ∈ hankelIdeal (ℤ × ℤ) 2 ∧
      C ((1, 0) : ℤ × ℤ) * hankelMinor (ℤ × ℤ) 2 conicColumns ≠ 0 ∧
      (C ((0, 1) : ℤ × ℤ) : Source (ℤ × ℤ) 2) ≠ 0 ∧
      C ((0, 1) : ℤ × ℤ) *
        (C ((1, 0) : ℤ × ℤ) * hankelMinor (ℤ × ℤ) 2 conicColumns) = 0 := by
  have hleft : ((1, 0) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.fst h)
  have hright : ((0, 1) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have hprod : ((0, 1) : ℤ × ℤ) * (1, 0) = 0 := by ext <;> simp
  refine ⟨conic_ideal_isHomogeneous (ℤ × ℤ), cubic_ideal_isHomogeneous (ℤ × ℤ),
    (conic_minor_isHomogeneous (ℤ × ℤ)).C_mul (1, 0),
    Ideal.mul_mem_left _ _ (minor_mem (ℤ × ℤ) 2 conicColumns), ?_, ?_, ?_⟩
  · intro hzero
    have hcoeff := conic_scaled_outer_coefficient (ℤ × ℤ) (1, 0)
    rw [hzero] at hcoeff
    exact hleft (by simpa using hcoeff.symm)
  · exact fun hzero => hright (C_eq_zero.mp hzero)
  · rw [← mul_assoc, ← map_mul, hprod, map_zero, zero_mul]

private theorem zero_coefficients_ideal_homogeneous (n : ℕ) :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) (ZMod 1))
      (hankelIdeal (ZMod 1) n) := by
  have hbot : hankelIdeal (ZMod 1) n = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro f _
    exact Ideal.mem_bot.mpr (Subsingleton.elim f 0)
  rw [hbot]
  exact Ideal.IsHomogeneous.bot _

private theorem zero_coefficients_polynomial_all_degrees (n d : ℕ)
    (f : Source (ZMod 1) n) : f = 0 ∧ f.IsHomogeneous d ∧ f.totalDegree = 0 := by
  have hzero : f = 0 := Subsingleton.elim _ _
  refine ⟨hzero, ?_, ?_⟩
  · rw [hzero]
    exact isHomogeneous_zero _ _ d
  · rw [hzero, totalDegree_zero]

private theorem zero_coefficients_minor_label_two (n : ℕ) (p : MinorIndex n) :
    hankelMinor (ZMod 1) n p = 0 ∧
      (hankelMinor (ZMod 1) n p).IsHomogeneous 2 ∧
      (hankelMinor (ZMod 1) n p).totalDegree = 0 :=
  zero_coefficients_polynomial_all_degrees n 2 _

private theorem conic_mixed_components_mem (R : Type u) [CommRing R] (d : ℕ) :
    homogeneousComponent d
      (hankelMinor R 2 conicColumns + X 0 * hankelMinor R 2 conicColumns) ∈
        hankelIdeal R 2 := by
  have hp : hankelMinor R 2 conicColumns + X 0 * hankelMinor R 2 conicColumns ∈
      hankelIdeal R 2 :=
    (hankelIdeal R 2).add_mem (minor_mem R 2 conicColumns)
      (Ideal.mul_mem_left _ _ (minor_mem R 2 conicColumns))
  exact homogeneousComponent_mem_of_mem (conic_ideal_isHomogeneous R) hp d

private theorem conic_mixed_componentwise_member (R : Type u) [CommRing R] :
    hankelMinor R 2 conicColumns + X 0 * hankelMinor R 2 conicColumns ∈
      hankelIdeal R 2 := by
  apply (mem_iff_homogeneousComponent_mem (conic_ideal_isHomogeneous R) _).mpr
  exact conic_mixed_components_mem R

private theorem integer_conic_quadratic_component_nonzero :
    homogeneousComponent 2
      (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) =
        hankelMinor ℤ 2 conicColumns ∧
      homogeneousComponent 2
        (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) ≠ 0 := by
  have hg := conic_minor_isHomogeneous ℤ
  have hthree : (X 0 * hankelMinor ℤ 2 conicColumns).IsHomogeneous 3 :=
    (isHomogeneous_X ℤ (0 : Fin 3)).mul hg
  have hcomponent : homogeneousComponent 2
      (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) =
        hankelMinor ℤ 2 conicColumns := by
    rw [map_add, homogeneousComponent_of_mem hg, homogeneousComponent_of_mem hthree]
    simp
  refine ⟨hcomponent, ?_⟩
  rw [hcomponent]
  exact conic_minor_ne_zero ℤ

private theorem integer_degree_zero_mixed_not_homogeneous :
    ¬ ∃ d, (X 0 + 1 : Source ℤ 0).IsHomogeneous d := by
  rintro ⟨d, hd⟩
  have hconstant : (X 0 + 1 : Source ℤ 0).coeff 0 = 1 := by
    simp [coeff_X]
  have hlinear : (X 0 + 1 : Source ℤ 0).coeff (Finsupp.single 0 1) = 1 := by
    have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
    simp [coeff_one, Ne.symm hs]
  by_cases hdegree : d = 0
  · subst d
    have hcoeff := hd.coeff_eq_zero (d := Finsupp.single (0 : Fin 1) 1) (by simp)
    rw [hlinear] at hcoeff
    exact one_ne_zero hcoeff
  · have hcoeff := hd.coeff_eq_zero (d := 0) (by simpa using Ne.symm hdegree)
    rw [hconstant] at hcoeff
    exact one_ne_zero hcoeff

private theorem integer_degree_zero_parametrization_kernel_not_homogeneous :
    ¬ Ideal.IsHomogeneous (homogeneousSubmodule (Fin 1) ℤ)
      (RingHom.ker (rncMap ℤ 0)) := by
  intro hkernel
  have hf : (X 0 - 1 : Source ℤ 0) ∈ RingHom.ker (rncMap ℤ 0) := by
    change rncMap ℤ 0 (X 0 - 1) = 0
    simp [rncMap_X, coordinateExponent]
  have hcomponent : homogeneousComponent 0 (X 0 - 1 : Source ℤ 0) = -1 := by
    simp [homogeneousComponent_zero, coeff_X]
  have hmem := homogeneousComponent_mem_of_mem hkernel hf 0
  rw [hcomponent] at hmem
  change rncMap ℤ 0 (-1) = 0 at hmem
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : Target ℤ) ≠ 0))
    (by simpa only [map_neg, map_one] using hmem)

#print axioms conicColumns
#print axioms cubicFirstColumns
#print axioms cubicOuterColumns
#print axioms cubicLastColumns
#print axioms degree_zero_one_variable_bottom_homogeneous
#print axioms degree_one_two_variable_bottom_homogeneous
#print axioms conic_columns_exhaustive
#print axioms cubic_columns_exhaustive
#print axioms conic_minor_eq
#print axioms cubic_minors_eq
#print axioms conic_ideal_eq_span
#print axioms conic_minor_isHomogeneous
#print axioms conic_ideal_isHomogeneous
#print axioms cubic_minors_isHomogeneous
#print axioms cubic_ideal_isHomogeneous
#print axioms conic_exponents_distinct
#print axioms conic_minor_coefficients
#print axioms conic_minor_ne_zero
#print axioms conic_scaled_outer_coefficient
#print axioms integer_conic_and_cubic_homogeneous_nonzero
#print axioms binary_conic_two_supported_terms
#print axioms mod_four_nilpotent_quadratic
#print axioms integer_product_quadratic_zero_divisor
#print axioms zero_coefficients_ideal_homogeneous
#print axioms zero_coefficients_polynomial_all_degrees
#print axioms zero_coefficients_minor_label_two
#print axioms conic_mixed_components_mem
#print axioms conic_mixed_componentwise_member
#print axioms integer_conic_quadratic_component_nonzero
#print axioms integer_degree_zero_mixed_not_homogeneous
#print axioms integer_degree_zero_parametrization_kernel_not_homogeneous

end

end ToricIdeals.RationalNormalCurve.HomogeneityModels
