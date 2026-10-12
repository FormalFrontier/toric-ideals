/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals.RationalNormalCurve.Homogeneous

/-!
# Homogeneous-component clients of the Hankel ideal

The homogeneity theorem for the original Hankel ideal gives component membership
in every degree over arbitrary commutative coefficient rings. For the conic,
`g = X₀X₂ - X₁²` gives the member `g + X₀*g`; Mathlib's componentwise membership
criterion recovers its membership from its homogeneous components. Over the
integers, its quadratic component is the nonzero minor `g` and lies in the ideal.

The standard source grading is selected locally. These are private tests, not
new ideal or grading constructions; no quotient grading or Hilbert claim is made.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and its
  `Homogeneous` module, supply the Hankel presentation, membership and
  standard-graded ideal homogeneity.
* Mathlib contributors, `Mathlib.RingTheory.MvPolynomial.Homogeneous`, supply
  homogeneous components and the component-membership criteria.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.HomogeneityClient

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private def conicColumns : MinorIndex 2 := ⟨(0, 1), by decide⟩

private theorem hankel_member_components (R : Type u) [CommRing R] (n : ℕ)
    (f : Source R n) (hf : f ∈ hankelIdeal R n) :
    ∀ d, homogeneousComponent d f ∈ hankelIdeal R n :=
  homogeneousComponent_mem_of_mem (hankelIdeal_isHomogeneous R n) hf

private theorem conic_mixed_components_mem (R : Type u) [CommRing R] :
    ∀ d, homogeneousComponent d
      (hankelMinor R 2 conicColumns + X 0 * hankelMinor R 2 conicColumns) ∈
        hankelIdeal R 2 := by
  have hg := minor_mem R 2 conicColumns
  exact homogeneousComponent_mem_of_mem (hankelIdeal_isHomogeneous R 2)
    ((hankelIdeal R 2).add_mem hg (Ideal.mul_mem_left _ _ hg))

private theorem conic_mixed_componentwise_member (R : Type u) [CommRing R] :
    hankelMinor R 2 conicColumns + X 0 * hankelMinor R 2 conicColumns ∈
      hankelIdeal R 2 :=
  (mem_iff_homogeneousComponent_mem (hankelIdeal_isHomogeneous R 2) _).mpr
    (conic_mixed_components_mem R)

private theorem integer_conic_quadratic_component_nonzero_member :
    homogeneousComponent 2
      (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) =
        hankelMinor ℤ 2 conicColumns ∧
      homogeneousComponent 2
        (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) ≠ 0 ∧
      homogeneousComponent 2
        (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) ∈
          hankelIdeal ℤ 2 := by
  have hg : (hankelMinor ℤ 2 conicColumns).IsHomogeneous 2 := by
    change (X 0 * X 2 - X 1 * X 1 : Source ℤ 2).IsHomogeneous 2
    exact ((isHomogeneous_X ℤ (0 : Fin 3)).mul (isHomogeneous_X ℤ 2)).sub
      ((isHomogeneous_X ℤ (1 : Fin 3)).mul (isHomogeneous_X ℤ 1))
  have hthree : (X 0 * hankelMinor ℤ 2 conicColumns).IsHomogeneous 3 :=
    (isHomogeneous_X ℤ (0 : Fin 3)).mul hg
  have hcomponent : homogeneousComponent 2
      (hankelMinor ℤ 2 conicColumns + X 0 * hankelMinor ℤ 2 conicColumns) =
        hankelMinor ℤ 2 conicColumns := by
    rw [map_add, homogeneousComponent_of_mem hg, homogeneousComponent_of_mem hthree]
    simp
  have hexponents : outerExponent 2 conicColumns ≠ innerExponent 2 conicColumns := by
    intro h
    have henergy := inner_energy_lt_outer_energy 2 conicColumns
    rw [h] at henergy
    exact (lt_irrefl _) henergy
  have hcoeff : (hankelMinor ℤ 2 conicColumns).coeff
      (outerExponent 2 conicColumns) = 1 := by
    rw [← monomial_outer_sub_inner ℤ 2 conicColumns, coeff_sub]
    simp [Ne.symm hexponents]
  refine ⟨hcomponent, ?_, ?_⟩
  · intro hzero
    rw [hcomponent] at hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  · exact homogeneousComponent_mem_of_mem (hankelIdeal_isHomogeneous ℤ 2)
      (conic_mixed_componentwise_member ℤ) 2

#print axioms conicColumns
#print axioms hankel_member_components
#print axioms conic_mixed_components_mem
#print axioms conic_mixed_componentwise_member
#print axioms integer_conic_quadratic_component_nonzero_member

end

end ToricIdeals.RationalNormalCurve.HomogeneityClient
