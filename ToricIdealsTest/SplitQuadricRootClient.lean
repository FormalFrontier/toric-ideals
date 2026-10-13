/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals

/-!
# Root-import clients for the split quadric

Polynomial classes, the universal morphism, the range equivalence, and chart
maps are used through an ordinary import of the library root. The two chart
models have independent universes and independently specified algebra actions.
-/

noncomputable section

universe u v s t

namespace ToricIdealsTest.SplitQuadricRootClient

open SplitQuadric

variable (A : Type u) [CommRing A]

private theorem class_eq_zero_iff (p : SplitQuadric.Polynomial A) :
    quotientMap A p = 0 ↔ theta A p = 0 := by
  rw [← phi_quotientMap A p]
  exact ⟨fun h => by rw [h, map_zero], fun h => phi_injective A (by simpa using h)⟩

private theorem kernel_criterion (p : SplitQuadric.Polynomial A) :
    p ∈ relationIdeal A ↔ theta A p = 0 := by
  rw [← kernel_theta A]
  exact RingHom.mem_ker

private theorem relation_in_range :
    rangeEquiv A (w A) * rangeEquiv A (z A) =
      rangeEquiv A (x A) * rangeEquiv A (y A) := by
  rw [← map_mul, ← map_mul]
  exact congrArg (rangeEquiv A) (sub_eq_zero.mp (coordinate_relation A))

private theorem lift_on_coefficients {S : Type v} [CommRing S] [Algebra A S]
    (values : Fin 4 → S) (h : values 0 * values 3 - values 1 * values 2 = 0)
    (a : A) : lift A values h (coefficientMap A a) = algebraMap A S a := by
  simp

private theorem universal_morphism_unique {S : Type v} [CommRing S] [Algebra A S]
    (f : CoordinateRing A →ₐ[A] S) :
    f = lift A (fun i => f (coordinate A i))
      (by simpa only [map_sub, map_mul, map_zero] using
        congrArg f (coordinate_relation A)) := by
  apply lift_unique A
  intro i
  rfl

section Chart

variable (LQ : Type s) [CommRing LQ]
  [Algebra (CoordinateRing A) LQ] [Algebra A LQ]
  [IsLocalization.Away (w A) LQ]
  (LB : Type t) [CommRing LB]
  [Algebra (ParameterPolynomial A) LB] [Algebra A LB]
  [IsScalarTower A (ParameterPolynomial A) LB] [IsLocalization.Away (W A) LB]

-- The backward computation needs no scalar tower through the quadric.
private theorem backward_ratio :
    chartBackward A LQ LB (algebraMap (ParameterPolynomial A) LB (T A)) =
      algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A) := by
  rw [chartBackward_algebraMap, inversePolynomial_T]

variable [IsScalarTower A (CoordinateRing A) LQ]

private theorem chart_left_inverse (q : LQ) :
    chartBackward A LQ LB (chartForward A LQ LB q) = q := by
  have h := congrArg (fun f : LQ →ₐ[A] LQ => f q)
    (chartBackward_comp_chartForward A LQ LB)
  simpa using h

private theorem chart_right_inverse (b : LB) :
    chartForward A LQ LB (chartBackward A LQ LB b) = b := by
  have h := congrArg (fun f : LB →ₐ[A] LB => f b)
    (chartForward_comp_chartBackward A LQ LB)
  simpa using h

private theorem chart_equivalence_square (q : CoordinateRing A) :
    chartEquiv A LQ LB (algebraMap (CoordinateRing A) LQ q) =
      algebraMap (ParameterPolynomial A) LB (phi A q) := by
  rw [chartEquiv_apply, chartForward_algebraMap]

end Chart

private theorem canonical_chart_coordinate :
    canonicalChartEquiv A
        (algebraMap (CoordinateRing A) (Localization.Away (w A)) (w A)) =
      algebraMap (ParameterPolynomial A) (Localization.Away (W A)) (W A) := by
  exact (chartEquiv_generators A _ _).1

private theorem domain_detected_by_coefficients [IsDomain (CoordinateRing A)] : IsDomain A :=
  (coordinateRing_isDomain_iff A).mp inferInstance

private theorem prime_detected_by_coefficients (h : (relationIdeal A).IsPrime) : IsDomain A :=
  (relationIdeal_isPrime_iff A).mp h

end ToricIdealsTest.SplitQuadricRootClient
