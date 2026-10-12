/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Weight
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Tactic
public import ToricIdeals.SplitQuadric.Exponents

/-!
# Natural exponent examples for a split quadric

For `(w, x, y, z) ↦ (W, WT, Y, YT)`, the exponent map sends
`(a, b, c, d)` to `(a + b, c + d, b + d)`. Replacing `k = min a d`
copies of `wz` by `xy` yields `(a - k, b + k, c + k, d - k)`.
The examples below compute this replacement and a total selector on natural
exponents, including both directions of the minimum and an exponent outside
`{(u, v, t) | t ≤ u + v}`. They also show that reduced exponents are not
closed under addition and that the selector is not additive.

The independent model below constructs its additive exponent map using
`Finsupp.weight`. Its quotient by the equal-image congruence uses Mathlib's
first isomorphism theorem for additive monoids, without choosing reduced
representatives. A separate group of examples uses the public definitions
`ToricIdeals.SplitQuadric.exponentMap`, `reduce`, `normal`, and `Reduced`
through their coordinate, single-exponent, and reducedness laws.

## Limitations

These are concrete natural-number calculations, not a classification of all
fibers or a polynomial-kernel theorem. Natural subtraction makes the selector
total, but it need not select a preimage outside the cone. The independent
model's definitions and the tuple constructors are private to this example
module; the separate API examples use `ToricIdeals.SplitQuadric.Exponents`.
No coefficient ring or domain is involved.

## References

* Mathlib, `Finsupp.equivFunOnFinite` and `Finsupp.weight`.
* Mathlib, `AddCon.quotientKerEquivRange`.
-/

noncomputable section

private def sourceTuple (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c, d]

private def targetTuple (u v t : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![u, v, t]

private def coordinateExponent : Fin 4 → Fin 3 →₀ ℕ :=
  ![targetTuple 1 0 0, targetTuple 1 0 1, targetTuple 0 1 0, targetTuple 0 1 1]

private def exponentMap : (Fin 4 →₀ ℕ) →+ (Fin 3 →₀ ℕ) :=
  Finsupp.weight coordinateExponent

private def reduce (m : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  let k := min (m 0) (m 3)
  sourceTuple (m 0 - k) (m 1 + k) (m 2 + k) (m 3 - k)

private def normal (n : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  let b := min (n 0) (n 2)
  let d := n 2 - b
  sourceTuple (n 0 - b) b (n 1 - d) d

private def w : Fin 4 →₀ ℕ := Finsupp.single 0 1
private def x : Fin 4 →₀ ℕ := Finsupp.single 1 1
private def y : Fin 4 →₀ ℕ := Finsupp.single 2 1
private def z : Fin 4 →₀ ℕ := Finsupp.single 3 1

-- The relation compares distinct exponents, each with two positive coordinates.
private theorem wz_xy_positive_coordinates : 0 < (w + z) 0 ∧ 0 < (w + z) 3 ∧
    0 < (x + y) 1 ∧ 0 < (x + y) 2 := by
  norm_num [w, x, y, z]

private theorem wz_ne_xy : w + z ≠ x + y := by
  intro h
  have h₀ := congrArg (fun m : Fin 4 →₀ ℕ => m 0) h
  norm_num [w, x, y, z] at h₀

private theorem wz_xy_nonzero : w + z ≠ 0 ∧ x + y ≠ 0 := by
  constructor
  · intro h
    have h₀ := congrArg (fun m : Fin 4 →₀ ℕ => m 0) h
    norm_num [w, z] at h₀
  · intro h
    have h₁ := congrArg (fun m : Fin 4 →₀ ℕ => m 1) h
    norm_num [x, y] at h₁

private theorem image_wz : exponentMap (w + z) = targetTuple 1 1 1 := by
  ext i
  fin_cases i <;>
    simp [exponentMap, w, z, Finsupp.weight_single, coordinateExponent, targetTuple]

private theorem image_xy : exponentMap (x + y) = targetTuple 1 1 1 := by
  ext i
  fin_cases i <;>
    simp [exponentMap, x, y, Finsupp.weight_single, coordinateExponent, targetTuple]

private theorem reduce_wz : reduce (w + z) = x + y := by
  ext i
  fin_cases i <;> norm_num [reduce, sourceTuple, w, x, y, z]

private theorem reduce_xy : reduce (x + y) = x + y := by
  ext i
  fin_cases i <;> norm_num [reduce, sourceTuple, x, y]

private theorem wz_xy_equal_image_distinct_equal_reduction : exponentMap (w + z) = exponentMap (x + y) ∧
    w + z ≠ x + y ∧ reduce (w + z) = reduce (x + y) :=
  ⟨image_wz.trans image_xy.symm, wz_ne_xy, reduce_wz.trans reduce_xy.symm⟩

-- A mixed exponent with a < d, so the w exponent disappears.
private theorem mixed_left :
    exponentMap (sourceTuple 5 2 3 7) = targetTuple 7 10 9 ∧
    reduce (sourceTuple 5 2 3 7) = sourceTuple 0 7 8 2 ∧
    normal (targetTuple 7 10 9) = sourceTuple 0 7 8 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;>
      norm_num [exponentMap, Finsupp.weight_eq_sum, Fin.sum_univ_succ,
        Finsupp.smul_apply, coordinateExponent, sourceTuple, targetTuple]
  · ext i
    fin_cases i <;> norm_num [reduce, sourceTuple]
  · ext i
    fin_cases i <;> norm_num [normal, sourceTuple, targetTuple]

private theorem normalization_mixed_left_eq_reduction : normal (exponentMap (sourceTuple 5 2 3 7)) =
    reduce (sourceTuple 5 2 3 7) := by
  rw [mixed_left.1, mixed_left.2.1, mixed_left.2.2]

-- A mixed exponent with d < a, so the z exponent disappears.
private theorem mixed_right :
    exponentMap (sourceTuple 7 2 3 5) = targetTuple 9 8 7 ∧
    reduce (sourceTuple 7 2 3 5) = sourceTuple 2 7 8 0 ∧
    normal (targetTuple 9 8 7) = sourceTuple 2 7 8 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;>
      norm_num [exponentMap, Finsupp.weight_eq_sum, Fin.sum_univ_succ,
        Finsupp.smul_apply, coordinateExponent, sourceTuple, targetTuple]
  · ext i
    fin_cases i <;> norm_num [reduce, sourceTuple]
  · ext i
    fin_cases i <;> norm_num [normal, sourceTuple, targetTuple]

private theorem normalization_mixed_right_eq_reduction : normal (exponentMap (sourceTuple 7 2 3 5)) =
    reduce (sourceTuple 7 2 3 5) := by
  rw [mixed_right.1, mixed_right.2.1, mixed_right.2.2]

-- Outside the cone, truncating the requested y exponent prevents a right inverse.
private def tAlone : Fin 3 →₀ ℕ := Finsupp.single 2 1

private theorem selector_boundary_tAlone_outside_cone : ¬ tAlone 2 ≤ tAlone 0 + tAlone 1 := by
  norm_num [tAlone]

private theorem normal_tAlone : normal tAlone = z := by
  ext i
  fin_cases i <;> norm_num [normal, sourceTuple, tAlone, z]

private theorem image_normal_tAlone : exponentMap (normal tAlone) = targetTuple 0 1 1 := by
  rw [normal_tAlone]
  ext i
  fin_cases i <;>
    simp [exponentMap, z, Finsupp.weight_single, coordinateExponent, targetTuple]

private theorem selector_boundary_tAlone_not_preimage : exponentMap (normal tAlone) ≠ tAlone := by
  rw [image_normal_tAlone]
  intro h
  have h₁ := congrArg (fun n : Fin 3 →₀ ℕ => n 1) h
  norm_num [targetTuple, tAlone] at h₁

-- Each summand is reduced; their sum is not.
private theorem reduced_coordinates_w_z_sum_not_reduced : (w 0 = 0 ∨ w 3 = 0) ∧ (z 0 = 0 ∨ z 3 = 0) ∧
    ¬ ((w + z) 0 = 0 ∨ (w + z) 3 = 0) := by
  norm_num [w, z]

private theorem normal_image_w : normal (exponentMap w) = w := by
  ext i
  fin_cases i <;>
    simp [normal, exponentMap, w, Finsupp.weight_single, coordinateExponent,
      sourceTuple, targetTuple]

private theorem normal_image_z : normal (exponentMap z) = z := by
  ext i
  fin_cases i <;>
    simp [normal, exponentMap, z, Finsupp.weight_single, coordinateExponent,
      sourceTuple, targetTuple]

private theorem normal_image_sum : normal (exponentMap w + exponentMap z) = x + y := by
  rw [← map_add, image_wz]
  ext i
  fin_cases i <;> norm_num [normal, sourceTuple, targetTuple, x, y]

private theorem exponentMap_w_z_eq_x_y : exponentMap w + exponentMap z = exponentMap x + exponentMap y := by
  rw [← map_add, ← map_add, image_wz, image_xy]

private theorem normalization_w_z_not_additive : normal (exponentMap w + exponentMap z) ≠
    normal (exponentMap w) + normal (exponentMap z) := by
  rw [normal_image_sum, normal_image_w, normal_image_z]
  exact Ne.symm wz_ne_xy

-- Zero and the three edges t = 0, t = u, and t = u + v.
private theorem exponentMap_zero_eq_zero : exponentMap 0 = 0 := map_zero exponentMap

private theorem reduce_zero_eq_zero : reduce 0 = 0 := by
  ext i
  fin_cases i <;> simp [reduce, sourceTuple]

private theorem normal_zero_eq_zero : normal 0 = 0 := by
  ext i
  fin_cases i <;> simp [normal, sourceTuple]

private theorem normalization_boundary_t_zero : normal (targetTuple 3 4 0) = sourceTuple 3 0 4 0 := by
  ext i
  fin_cases i <;> norm_num [normal, sourceTuple, targetTuple]

private theorem normalization_boundary_t_eq_u : normal (targetTuple 3 4 3) = sourceTuple 0 3 4 0 := by
  ext i
  fin_cases i <;> norm_num [normal, sourceTuple, targetTuple]

private theorem normalization_boundary_t_eq_u_add_v : normal (targetTuple 3 4 7) = sourceTuple 0 3 0 4 := by
  ext i
  fin_cases i <;> norm_num [normal, sourceTuple, targetTuple]

-- The coefficient-free quotient-to-image construction is a Mathlib client.
private def quotientEquivImage :
    (AddCon.ker exponentMap).Quotient ≃+ AddMonoidHom.mrange exponentMap :=
  AddCon.quotientKerEquivRange exponentMap

private theorem quotient_wz_eq_xy : ((w + z : Fin 4 →₀ ℕ) : (AddCon.ker exponentMap).Quotient) =
    ((x + y : Fin 4 →₀ ℕ) : (AddCon.ker exponentMap).Quotient) := by
  apply (AddCon.ker exponentMap).eq.mpr
  exact image_wz.trans image_xy.symm

private theorem quotientEquivImage_wz_eq_targetTuple : (quotientEquivImage
      ((w + z : Fin 4 →₀ ℕ) : (AddCon.ker exponentMap).Quotient) : Fin 3 →₀ ℕ) =
    targetTuple 1 1 1 := by
  change exponentMap (w + z) = targetTuple 1 1 1
  exact image_wz

-- Examples using the split-quadric exponent API, separate from the independent model.

private theorem parametrized_w :
    ToricIdeals.SplitQuadric.exponentMap w = targetTuple 1 0 0 := by
  simp only [w, ToricIdeals.SplitQuadric.exponentMap_single_zero]
  ext i
  fin_cases i <;> simp only [Finsupp.single_apply] <;> rfl

private theorem parametrized_z :
    ToricIdeals.SplitQuadric.exponentMap z = targetTuple 0 1 1 := by
  simp only [z, ToricIdeals.SplitQuadric.exponentMap_single_three]
  ext i
  fin_cases i <;> simp only [Finsupp.add_apply, Finsupp.single_apply] <;> rfl

private theorem parametrized_wz :
    ToricIdeals.SplitQuadric.exponentMap (w + z) = targetTuple 1 1 1 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.exponentMap_apply_zero (w + z)).trans (by
      norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.exponentMap_apply_one (w + z)).trans (by
      norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.exponentMap_apply_two (w + z)).trans (by
      norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem parametrized_xy :
    ToricIdeals.SplitQuadric.exponentMap (x + y) = targetTuple 1 1 1 := by
  simp only [map_add, x, y, ToricIdeals.SplitQuadric.exponentMap_single_one,
    ToricIdeals.SplitQuadric.exponentMap_single_two]
  ext i
  fin_cases i <;> simp only [Finsupp.add_apply, Finsupp.single_apply] <;> rfl

namespace ToricIdealsTest.SplitQuadric

/-- The monomials `wz` and `xy` have the same exponent after parametrization. -/
public theorem exponentMap_wz_eq_xy :
    ToricIdeals.SplitQuadric.exponentMap
        (Finsupp.single 0 1 + Finsupp.single 3 1) =
      ToricIdeals.SplitQuadric.exponentMap
        (Finsupp.single 1 1 + Finsupp.single 2 1) :=
  parametrized_wz.trans parametrized_xy.symm

end ToricIdealsTest.SplitQuadric

-- The same nonzero image has two distinct nonzero preimages.
private theorem exponentMap_wz_xy_distinct_nonzero_preimages : ToricIdeals.SplitQuadric.exponentMap (w + z) =
      ToricIdeals.SplitQuadric.exponentMap (x + y) ∧
    w + z ≠ x + y ∧ w + z ≠ 0 ∧ x + y ≠ 0 ∧
    ToricIdeals.SplitQuadric.exponentMap (w + z) ≠ 0 := by
  refine ⟨parametrized_wz.trans parametrized_xy.symm, wz_ne_xy, ?_, ?_, ?_⟩
  · intro h
    have h₀ := congrArg (fun m : Fin 4 →₀ ℕ => m 0) h
    norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply, Finsupp.zero_apply,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] at h₀
  · intro h
    have h₁ := congrArg (fun m : Fin 4 →₀ ℕ => m 1) h
    norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply, Finsupp.zero_apply,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] at h₁
  · rw [parametrized_wz]
    intro h
    have h₀ := congrArg (fun n : Fin 3 →₀ ℕ => n 0) h
    change (1 : ℕ) = 0 at h₀
    omega

private theorem replacement_wz : ToricIdeals.SplitQuadric.reduce (w + z) = x + y := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.reduce_apply_zero (w + z)).trans (by
      norm_num only [w, x, y, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_one (w + z)).trans (by
      norm_num only [w, x, y, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_two (w + z)).trans (by
      norm_num only [w, x, y, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_three (w + z)).trans (by
      norm_num only [w, x, y, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem replacement_xy : ToricIdeals.SplitQuadric.reduce (x + y) = x + y := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.reduce_apply_zero (x + y)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_one (x + y)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_two (x + y)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_three (x + y)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem reduce_wz_eq_reduce_xy : ToricIdeals.SplitQuadric.reduce (w + z) =
    ToricIdeals.SplitQuadric.reduce (x + y) :=
  replacement_wz.trans replacement_xy.symm

private theorem reduce_wz_xy_reduced : ToricIdeals.SplitQuadric.Reduced (ToricIdeals.SplitQuadric.reduce (w + z)) ∧
    ToricIdeals.SplitQuadric.Reduced (ToricIdeals.SplitQuadric.reduce (x + y)) := by
  rw [replacement_wz, replacement_xy]
  constructor <;>
    rw [ToricIdeals.SplitQuadric.reduced_iff] <;>
    left <;> simp only [x, y, Finsupp.add_apply, Finsupp.single_apply] <;> rfl

-- Both directions of the minimum occur for exponents with four positive entries.
private theorem parametrization_left :
    ToricIdeals.SplitQuadric.exponentMap (sourceTuple 5 2 3 7) = targetTuple 7 10 9 ∧
    ToricIdeals.SplitQuadric.reduce (sourceTuple 5 2 3 7) = sourceTuple 0 7 8 2 ∧
    ToricIdeals.SplitQuadric.normal (targetTuple 7 10 9) = sourceTuple 0 7 8 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_zero (sourceTuple 5 2 3 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_one (sourceTuple 5 2 3 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_two (sourceTuple 5 2 3 7)).trans (by rfl)
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.reduce_apply_zero (sourceTuple 5 2 3 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_one (sourceTuple 5 2 3 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_two (sourceTuple 5 2 3 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_three (sourceTuple 5 2 3 7)).trans (by rfl)
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 7 10 9)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 7 10 9)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 7 10 9)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 7 10 9)).trans (by rfl)

private theorem parametrization_right :
    ToricIdeals.SplitQuadric.exponentMap (sourceTuple 7 2 3 5) = targetTuple 9 8 7 ∧
    ToricIdeals.SplitQuadric.reduce (sourceTuple 7 2 3 5) = sourceTuple 2 7 8 0 ∧
    ToricIdeals.SplitQuadric.normal (targetTuple 9 8 7) = sourceTuple 2 7 8 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_zero (sourceTuple 7 2 3 5)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_one (sourceTuple 7 2 3 5)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.exponentMap_apply_two (sourceTuple 7 2 3 5)).trans (by rfl)
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.reduce_apply_zero (sourceTuple 7 2 3 5)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_one (sourceTuple 7 2 3 5)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_two (sourceTuple 7 2 3 5)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.reduce_apply_three (sourceTuple 7 2 3 5)).trans (by rfl)
  · ext i
    fin_cases i
    · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 9 8 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 9 8 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 9 8 7)).trans (by rfl)
    · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 9 8 7)).trans (by rfl)

private theorem selector_mixed_left_eq_reduce : ToricIdeals.SplitQuadric.normal
      (ToricIdeals.SplitQuadric.exponentMap (sourceTuple 5 2 3 7)) =
    ToricIdeals.SplitQuadric.reduce (sourceTuple 5 2 3 7) := by
  rw [parametrization_left.1, parametrization_left.2.1, parametrization_left.2.2]

private theorem selector_mixed_right_eq_reduce : ToricIdeals.SplitQuadric.normal
      (ToricIdeals.SplitQuadric.exponentMap (sourceTuple 7 2 3 5)) =
    ToricIdeals.SplitQuadric.reduce (sourceTuple 7 2 3 5) := by
  rw [parametrization_right.1, parametrization_right.2.1, parametrization_right.2.2]

private theorem reduce_normal_mixed_tuples_reduced :
    ToricIdeals.SplitQuadric.Reduced
      (ToricIdeals.SplitQuadric.reduce (sourceTuple 5 2 3 7)) ∧
    ToricIdeals.SplitQuadric.Reduced
      (ToricIdeals.SplitQuadric.normal (targetTuple 7 10 9)) ∧
    ToricIdeals.SplitQuadric.Reduced
      (ToricIdeals.SplitQuadric.reduce (sourceTuple 7 2 3 5)) ∧
    ToricIdeals.SplitQuadric.Reduced
      (ToricIdeals.SplitQuadric.normal (targetTuple 9 8 7)) := by
  rw [parametrization_left.2.1, parametrization_left.2.2,
    parametrization_right.2.1, parametrization_right.2.2]
  exact ⟨(ToricIdeals.SplitQuadric.reduced_iff _).2 (Or.inl rfl),
    (ToricIdeals.SplitQuadric.reduced_iff _).2 (Or.inl rfl),
    (ToricIdeals.SplitQuadric.reduced_iff _).2 (Or.inr rfl),
    (ToricIdeals.SplitQuadric.reduced_iff _).2 (Or.inr rfl)⟩

-- Reduced summands can have a sum divisible by wz.
private theorem reduced_w_z_sum_not_reduced : ToricIdeals.SplitQuadric.Reduced w ∧ ToricIdeals.SplitQuadric.Reduced z ∧
    ¬ ToricIdeals.SplitQuadric.Reduced (w + z) := by
  refine ⟨(ToricIdeals.SplitQuadric.reduced_iff w).2 (Or.inr ?_),
    (ToricIdeals.SplitQuadric.reduced_iff z).2 (Or.inl ?_), ?_⟩
  · simp only [w, Finsupp.single_apply] ; rfl
  · simp only [z, Finsupp.single_apply] ; rfl
  · intro h
    have h' := (ToricIdeals.SplitQuadric.reduced_iff (w + z)).1 h
    rcases h' with h₀ | h₃
    · norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] at h₀
    · norm_num only [w, z, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] at h₃

-- The exponent of T alone is outside the cone and is sent to the exponent of z.
private theorem selector_tAlone : ToricIdeals.SplitQuadric.normal tAlone = z := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero tAlone).trans (by
      norm_num only [tAlone, z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one tAlone).trans (by
      norm_num only [tAlone, z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two tAlone).trans (by
      norm_num only [tAlone, z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three tAlone).trans (by
      norm_num only [tAlone, z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem selector_boundary_tAlone_not_right_inverse : ¬ tAlone 2 ≤ tAlone 0 + tAlone 1 ∧
    ToricIdeals.SplitQuadric.normal tAlone = z ∧
    ToricIdeals.SplitQuadric.exponentMap (ToricIdeals.SplitQuadric.normal tAlone) =
      targetTuple 0 1 1 ∧
    ToricIdeals.SplitQuadric.exponentMap (ToricIdeals.SplitQuadric.normal tAlone) ≠
      tAlone := by
  refine ⟨?_, selector_tAlone, ?_, ?_⟩
  · norm_num only [tAlone, Finsupp.single_apply,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte]
  · rw [selector_tAlone]
    exact parametrized_z
  · rw [selector_tAlone, parametrized_z]
    intro h
    have h₁ := congrArg (fun n : Fin 3 →₀ ℕ => n 1) h
    change (1 : ℕ) = tAlone 1 at h₁
    norm_num only [tAlone, Finsupp.single_apply,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] at h₁

private theorem selector_image_w :
    ToricIdeals.SplitQuadric.normal (ToricIdeals.SplitQuadric.exponentMap w) = w := by
  rw [parametrized_w]
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 1 0 0)).trans (by
      norm_num only [w, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 1 0 0)).trans (by
      norm_num only [w, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 1 0 0)).trans (by
      norm_num only [w, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 1 0 0)).trans (by
      norm_num only [w, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem selector_image_z :
    ToricIdeals.SplitQuadric.normal (ToricIdeals.SplitQuadric.exponentMap z) = z := by
  rw [parametrized_z]
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 0 1 1)).trans (by
      norm_num only [z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 0 1 1)).trans (by
      norm_num only [z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 0 1 1)).trans (by
      norm_num only [z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 0 1 1)).trans (by
      norm_num only [z, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem selector_image_sum :
    ToricIdeals.SplitQuadric.normal
      (ToricIdeals.SplitQuadric.exponentMap w + ToricIdeals.SplitQuadric.exponentMap z) =
      x + y := by
  rw [← map_add, parametrized_wz]
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 1 1 1)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 1 1 1)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 1 1 1)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 1 1 1)).trans (by
      norm_num only [x, y, Finsupp.add_apply, Finsupp.single_apply,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte] ; rfl)

private theorem selector_w_z_not_additive : ToricIdeals.SplitQuadric.normal
      (ToricIdeals.SplitQuadric.exponentMap w + ToricIdeals.SplitQuadric.exponentMap z) ≠
    ToricIdeals.SplitQuadric.normal (ToricIdeals.SplitQuadric.exponentMap w) +
      ToricIdeals.SplitQuadric.normal (ToricIdeals.SplitQuadric.exponentMap z) := by
  rw [selector_image_sum, selector_image_w, selector_image_z]
  exact Ne.symm wz_ne_xy

-- Zero and the cone edges t = 0, t = u, and t = u + v.
private theorem parametrization_zero_eq_zero : ToricIdeals.SplitQuadric.exponentMap 0 = 0 :=
  map_zero ToricIdeals.SplitQuadric.exponentMap

private theorem replacement_zero_eq_zero : ToricIdeals.SplitQuadric.reduce 0 = 0 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.reduce_apply_zero 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_one 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_two 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.reduce_apply_three 0).trans (by rfl)

private theorem selector_zero_eq_zero : ToricIdeals.SplitQuadric.normal 0 = 0 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two 0).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three 0).trans (by rfl)

private theorem reduced_zero_exponent : ToricIdeals.SplitQuadric.Reduced 0 := by
  rw [ToricIdeals.SplitQuadric.reduced_iff]
  exact Or.inl rfl

private theorem selector_boundary_t_zero : ToricIdeals.SplitQuadric.normal (targetTuple 3 4 0) = sourceTuple 3 0 4 0 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 3 4 0)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 3 4 0)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 3 4 0)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 3 4 0)).trans (by rfl)

private theorem selector_boundary_t_eq_u : ToricIdeals.SplitQuadric.normal (targetTuple 3 4 3) = sourceTuple 0 3 4 0 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 3 4 3)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 3 4 3)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 3 4 3)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 3 4 3)).trans (by rfl)

private theorem selector_boundary_t_eq_u_add_v : ToricIdeals.SplitQuadric.normal (targetTuple 3 4 7) = sourceTuple 0 3 0 4 := by
  ext i
  fin_cases i
  · exact (ToricIdeals.SplitQuadric.normal_apply_zero (targetTuple 3 4 7)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_one (targetTuple 3 4 7)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_two (targetTuple 3 4 7)).trans (by rfl)
  · exact (ToricIdeals.SplitQuadric.normal_apply_three (targetTuple 3 4 7)).trans (by rfl)

-- The fiber of (7, 10, 9) contains (5, 2, 3, 7); its reduction is (0, 7, 8, 2).
-- Obtain reducedness and preservation of the image from the general theorems,
-- reusing the coordinate calculations above only to identify these two tuples.
private theorem reduced_left_fiber :
    ToricIdeals.SplitQuadric.Reduced (sourceTuple 0 7 8 2) ∧
    ToricIdeals.SplitQuadric.exponentMap (sourceTuple 0 7 8 2) = targetTuple 7 10 9 := by
  constructor
  · have h := ToricIdeals.SplitQuadric.reduce_reduced (sourceTuple 5 2 3 7)
    rwa [parametrization_left.2.1] at h
  · rw [← parametrization_left.2.1, ToricIdeals.SplitQuadric.exponentMap_reduce]
    exact parametrization_left.1

private theorem mixed_image_bound :
    (targetTuple 7 10 9) 2 ≤ (targetTuple 7 10 9) 0 + (targetTuple 7 10 9) 1 := by
  exact (by decide : (9 : ℕ) ≤ 7 + 10)

-- The nonzero reduced tuple is fixed by reduction and by selection above its
-- image. A second reduction of the mixed input removes no further factors.
private theorem reduce_fixed_reduced_mixed_left :
    ToricIdeals.SplitQuadric.exponentMap (sourceTuple 0 7 8 2) = targetTuple 7 10 9 ∧
    ToricIdeals.SplitQuadric.Reduced (sourceTuple 0 7 8 2) ∧
    ToricIdeals.SplitQuadric.reduce (sourceTuple 0 7 8 2) = sourceTuple 0 7 8 2 ∧
    ToricIdeals.SplitQuadric.reduce
      (ToricIdeals.SplitQuadric.reduce (sourceTuple 5 2 3 7)) = sourceTuple 0 7 8 2 ∧
    ToricIdeals.SplitQuadric.normal
      (ToricIdeals.SplitQuadric.exponentMap (sourceTuple 0 7 8 2)) = sourceTuple 0 7 8 2 := by
  have hfixed := (ToricIdeals.SplitQuadric.reduce_eq_self_iff (sourceTuple 0 7 8 2)).2
    reduced_left_fiber.1
  refine ⟨reduced_left_fiber.2, reduced_left_fiber.1, hfixed, ?_, ?_⟩
  · exact (ToricIdeals.SplitQuadric.reduce_reduce (sourceTuple 5 2 3 7)).trans
      parametrization_left.2.1
  · exact (ToricIdeals.SplitQuadric.normal_exponentMap (sourceTuple 0 7 8 2)).trans hfixed

-- The distinct exponents wz and xy lie in one fiber. The fiber criterion
-- identifies their reductions, while selection over the common image gives xy.
private theorem fiber_wz_xy_same_reduction_selected_xy : w + z ≠ x + y ∧
    ToricIdeals.SplitQuadric.reduce (w + z) = ToricIdeals.SplitQuadric.reduce (x + y) ∧
    ToricIdeals.SplitQuadric.normal (targetTuple 1 1 1) = x + y := by
  refine ⟨wz_ne_xy, ?_, ?_⟩
  · exact (ToricIdeals.SplitQuadric.reduce_eq_reduce_iff (w + z) (x + y)).2
      (parametrized_wz.trans parametrized_xy.symm)
  · have h := ToricIdeals.SplitQuadric.normal_exponentMap (w + z)
    rwa [parametrized_wz, replacement_wz] at h

-- On the mixed target, the selector is a reduced preimage. Uniqueness among
-- reduced exponents identifies it with the concrete tuple already in this fiber.
private theorem selector_mixed_left_unique_reduced_preimage :
    ToricIdeals.SplitQuadric.Reduced
      (ToricIdeals.SplitQuadric.normal (targetTuple 7 10 9)) ∧
    ToricIdeals.SplitQuadric.exponentMap
      (ToricIdeals.SplitQuadric.normal (targetTuple 7 10 9)) = targetTuple 7 10 9 ∧
    ToricIdeals.SplitQuadric.normal (targetTuple 7 10 9) = sourceTuple 0 7 8 2 := by
  have hnormal := ToricIdeals.SplitQuadric.normal_reduced (targetTuple 7 10 9)
  have hpreimage :=
    ToricIdeals.SplitQuadric.exponentMap_normal (targetTuple 7 10 9) mixed_image_bound
  exact ⟨hnormal, hpreimage,
    ToricIdeals.SplitQuadric.eq_of_reduced_of_exponentMap_eq
      hnormal reduced_left_fiber.1 (hpreimage.trans reduced_left_fiber.2.symm)⟩

-- The bound 9 ≤ 7 + 10 gives range membership and a unique reduced preimage.
-- In contrast, T alone is (0, 0, 1), with 1 > 0 + 0: it is not in the range
-- and has no unique reduced preimage. Its selected exponent z is nevertheless
-- reduced, but cannot map back to T alone.
private theorem selector_boundary_mixed_target_and_tAlone_range :
    targetTuple 7 10 9 ∈ AddMonoidHom.mrange ToricIdeals.SplitQuadric.exponentMap ∧
    (∃! m : Fin 4 →₀ ℕ, ToricIdeals.SplitQuadric.Reduced m ∧
      ToricIdeals.SplitQuadric.exponentMap m = targetTuple 7 10 9) ∧
    tAlone ∉ AddMonoidHom.mrange ToricIdeals.SplitQuadric.exponentMap ∧
    ¬ (∃! m : Fin 4 →₀ ℕ, ToricIdeals.SplitQuadric.Reduced m ∧
      ToricIdeals.SplitQuadric.exponentMap m = tAlone) ∧
    ToricIdeals.SplitQuadric.Reduced z ∧
    ToricIdeals.SplitQuadric.exponentMap (ToricIdeals.SplitQuadric.normal tAlone) ≠
      tAlone := by
  have hout : ¬ tAlone 2 ≤ tAlone 0 + tAlone 1 := by
    norm_num only [tAlone, Finsupp.single_apply,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, ↓reduceIte]
  have hnot : tAlone ∉ AddMonoidHom.mrange ToricIdeals.SplitQuadric.exponentMap := by
    intro h
    exact hout ((ToricIdeals.SplitQuadric.mem_mrange_iff tAlone).1 h)
  refine ⟨(ToricIdeals.SplitQuadric.mem_mrange_iff (targetTuple 7 10 9)).2
      mixed_image_bound,
    (ToricIdeals.SplitQuadric.existsUnique_reduced_preimage_iff (targetTuple 7 10 9)).2
      mixed_image_bound, hnot, ?_, ?_, ?_⟩
  · intro h
    exact hout ((ToricIdeals.SplitQuadric.existsUnique_reduced_preimage_iff tAlone).1 h)
  · rw [← selector_tAlone]
    exact ToricIdeals.SplitQuadric.normal_reduced tAlone
  · intro h
    exact hnot (AddMonoidHom.mem_mrange.mpr
      ⟨ToricIdeals.SplitQuadric.normal tAlone, h⟩)
