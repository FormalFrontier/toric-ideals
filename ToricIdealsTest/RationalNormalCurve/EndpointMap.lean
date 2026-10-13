/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals

/-!
# Endpoint-map coefficient and boundary examples

Private examples use the coefficient and endpoint evaluation API over the
integers in degrees zero through three. They retain nonzero coefficient
classes and nontrivial integer Hankel quotients. A product with `ZMod 4`
retains a nonzero square-zero coefficient, while `ZMod 1` supplies the zero
coefficient-ring boundary.

The constant-class argument follows the kernel-containment reasoning in
`ToricIdeals.RationalNormalCurve` and its coefficient-ring examples by
Formal Frontier Agents. No example uses the integral, finite or injective
endpoint-map theorems.
-/

open MvPolynomial
open ToricIdeals.RationalNormalCurve

namespace ToricIdealsTest.RationalNormalCurve.EndpointMap

noncomputable section

universe u

private theorem constant_class_ne_zero {R : Type u} [CommRing R]
    (n : ℕ) (r : R) (hr : r ≠ 0) :
    Ideal.Quotient.mk (hankelIdeal R n) (C r) ≠ 0 := by
  have hconstant : rncMap R n (C r) = (C r : Target R) := by
    rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
    change AddMonoidAlgebra.mapDomain (rncExponent n)
        (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  intro hzero
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hker := hankelIdeal_le_ker R n hmem
  change rncMap R n (C r) = 0 at hker
  rw [hconstant] at hker
  exact hr (MvPolynomial.C_eq_zero.mp hker)

private theorem integer_evaluation (n : ℕ) :
    endpointMap (R := ℤ) n
        (X (0 : Fin 2) * X 1 + C 7 * X 0 + C 3) =
      Ideal.Quotient.mk (hankelIdeal ℤ n)
        (X (0 : Fin (n + 1)) * X (Fin.last n) + C 7 * X 0 + C 3) := by
  simp only [map_add, map_mul, endpointMap_X_zero, endpointMap_X_one,
    endpointMap_C]

private theorem integer_degree_zero :
    hankelIdeal ℤ 0 = ⊥ ∧
      endpointMap (R := ℤ) 0 (X (0 : Fin 2)) =
        endpointMap (R := ℤ) 0 (X (1 : Fin 2)) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      endpointMap (R := ℤ) 0 (C 7) ≠ 0 := by
  refine ⟨hankelIdeal_zero ℤ, ?_, ?_, ?_⟩
  · simp only [endpointMap_X_zero, endpointMap_X_one]
    rfl
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact MvPolynomial.X_ne_zero (0 : Fin 1) hmem
  · rw [endpointMap_C]
    exact constant_class_ne_zero 0 (7 : ℤ) (by decide)

private theorem integer_degree_one :
    1 ≤ (1 : ℕ) ∧ hankelIdeal ℤ 1 = ⊥ ∧
      IsDomain (Source ℤ 1 ⧸ hankelIdeal ℤ 1) ∧
      endpointMap (R := ℤ) 1 (C 7) ≠ 0 ∧
      endpointMap (R := ℤ) 1 (X (0 : Fin 2) + X 1 + C 7) =
        Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2) + X 1 + C 7) := by
  refine ⟨by decide, hankelIdeal_one ℤ, quotient_isDomain ℤ 1 (by decide), ?_, ?_⟩
  · rw [endpointMap_C]
    exact constant_class_ne_zero 1 (7 : ℤ) (by decide)
  · simp only [map_add, endpointMap_X_zero, endpointMap_X_one, endpointMap_C]
    rfl

private theorem integer_degrees_two_three :
    1 ≤ (2 : ℕ) ∧ 1 ≤ (3 : ℕ) ∧
      IsDomain (Source ℤ 2 ⧸ hankelIdeal ℤ 2) ∧
      IsDomain (Source ℤ 3 ⧸ hankelIdeal ℤ 3) ∧
      endpointMap (R := ℤ) 2 (C 7) ≠ 0 ∧
      endpointMap (R := ℤ) 3 (C 7) ≠ 0 ∧
      endpointMap (R := ℤ) 2 (X (0 : Fin 2) * X 1 + C 7 * X 0 + C 3) =
        Ideal.Quotient.mk (hankelIdeal ℤ 2)
          (X (0 : Fin 3) * X (Fin.last 2) + C 7 * X 0 + C 3) ∧
      endpointMap (R := ℤ) 3 (X (0 : Fin 2) * X 1 + C 7 * X 0 + C 3) =
        Ideal.Quotient.mk (hankelIdeal ℤ 3)
          (X (0 : Fin 4) * X (Fin.last 3) + C 7 * X 0 + C 3) := by
  refine ⟨by decide, by decide, quotient_isDomain ℤ 2 (by decide),
    quotient_isDomain ℤ 3 (by decide), ?_, ?_, integer_evaluation 2,
    integer_evaluation 3⟩
  · rw [endpointMap_C]
    exact constant_class_ne_zero 2 (7 : ℤ) (by decide)
  · rw [endpointMap_C]
    exact constant_class_ne_zero 3 (7 : ℤ) (by decide)

private theorem nilpotent_product_coefficients :
    endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) ≠ 0 ∧
      endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) *
        endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) = 0 ∧
      ¬ IsDomain (Source (ZMod 4 × ℤ) 2 ⧸ hankelIdeal (ZMod 4 × ℤ) 2) := by
  have hr : ((2, 0) : ZMod 4 × ℤ) ≠ 0 := by
    intro h
    exact (by decide : (2 : ZMod 4) ≠ 0) (congrArg Prod.fst h)
  have hrmul : ((2, 0) : ZMod 4 × ℤ) * (2, 0) = 0 := by decide
  have hnonzero : endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) ≠ 0 := by
    rw [endpointMap_C]
    exact constant_class_ne_zero 2 (2, 0) hr
  have hsquare : endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) *
      endpointMap (R := ZMod 4 × ℤ) 2 (C (2, 0)) = 0 := by
    calc
      _ = endpointMap (R := ZMod 4 × ℤ) 2 (C (((2, 0) : ZMod 4 × ℤ) * (2, 0))) := by
        simp only [map_mul]
      _ = 0 := by rw [hrmul, map_zero, map_zero]
  refine ⟨hnonzero, hsquare, ?_⟩
  intro hdomain
  let := hdomain
  exact (mul_eq_zero.mp hsquare).elim hnonzero hnonzero

private theorem zero_ring_boundary (n : ℕ) :
    (1 : ZMod 1) = 0 ∧
      (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 ∧
      endpointMap (R := ZMod 1) n (X (0 : Fin 2) + X 1 + C 7) = 0 := by
  have hsource : (1 : Source (ZMod 1) n) = 0 := Subsingleton.elim _ _
  have hunit : (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) n)) hsource
  have hpoly : (X (0 : Fin 2) + X 1 + C 7 : MvPolynomial (Fin 2) (ZMod 1)) = 0 :=
    Subsingleton.elim _ _
  refine ⟨by decide, hunit, ?_⟩
  simpa only [map_zero] using congrArg (endpointMap (R := ZMod 1) n) hpoly

end

end ToricIdealsTest.RationalNormalCurve.EndpointMap
