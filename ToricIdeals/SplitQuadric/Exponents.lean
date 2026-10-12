/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Weight

import Mathlib.Tactic.FinCases

/-!
# Exponents of the split quadric parametrization

For the substitution `(w, x, y, z) ↦ (W, WT, Y, YT)`, the exponent map is
`(a, b, c, d) ↦ (a + b, c + d, b + d)`. Exponents are represented by
`Fin 4 →₀ ℕ` and `Fin 3 →₀ ℕ`, as in multivariate polynomial rings.

Removing `k = min a d` copies of `wz` and inserting `k` copies of `xy` gives
`(a - k, b + k, c + k, d - k)`. A reduced exponent has `a = 0` or `d = 0`.
The image cone is `t ≤ u + v`, and each exponent in this cone has a unique
reduced preimage. The total function `normal` selects this preimage on the
cone; outside it, natural subtraction truncates and no right-inverse assertion
is made.

## Limitations

This module concerns only natural-number exponents, not coefficients, ideals,
polynomial kernels or quotient rings. The reduced exponents are not asserted
to form an additive submonoid, and neither reduction nor the selector is
asserted to be additive.

## References

* Earlier Formal Frontier work on split-quadric exponent normal forms.
* Mathlib's `Finsupp.weight` constructs the additive map from its four columns.
* Mathlib's `Finsupp.equivFunOnFinite` supplies the finite-coordinate constructor.
-/

@[expose] public section

noncomputable section

namespace ToricIdeals.SplitQuadric

/-- The additive exponent map `(a, b, c, d) ↦ (a + b, c + d, b + d)` for
`(w, x, y, z) ↦ (W, WT, Y, YT)`. -/
def exponentMap : (Fin 4 →₀ ℕ) →+ (Fin 3 →₀ ℕ) :=
  Finsupp.weight
    ![Finsupp.single 0 1,
      Finsupp.single 0 1 + Finsupp.single 2 1,
      Finsupp.single 1 1,
      Finsupp.single 1 1 + Finsupp.single 2 1]

/-- The exponent of `W` after parametrization. -/
@[simp]
theorem exponentMap_apply_zero (m : Fin 4 →₀ ℕ) :
    exponentMap m 0 = m 0 + m 1 := by
  simp [exponentMap, Finsupp.weight_eq_sum, Fin.sum_univ_succ, smul_eq_mul]

/-- The exponent of `Y` after parametrization. -/
@[simp]
theorem exponentMap_apply_one (m : Fin 4 →₀ ℕ) :
    exponentMap m 1 = m 2 + m 3 := by
  simp [exponentMap, Finsupp.weight_eq_sum, Fin.sum_univ_succ, smul_eq_mul]

/-- The exponent of `T` after parametrization. -/
@[simp]
theorem exponentMap_apply_two (m : Fin 4 →₀ ℕ) :
    exponentMap m 2 = m 1 + m 3 := by
  simp [exponentMap, Finsupp.weight_eq_sum, Fin.sum_univ_succ, smul_eq_mul]

/-- A power of `w` maps to the same power of `W`. -/
@[simp]
theorem exponentMap_single_zero (k : ℕ) :
    exponentMap (Finsupp.single 0 k) = Finsupp.single 0 k := by
  simp [exponentMap, Finsupp.weight_single, smul_eq_mul]

/-- A power of `x` maps to the corresponding powers of `W` and `T`. -/
@[simp]
theorem exponentMap_single_one (k : ℕ) :
    exponentMap (Finsupp.single 1 k) = Finsupp.single 0 k + Finsupp.single 2 k := by
  simp [exponentMap, Finsupp.weight_single, smul_add, smul_eq_mul]

/-- A power of `y` maps to the same power of `Y`. -/
@[simp]
theorem exponentMap_single_two (k : ℕ) :
    exponentMap (Finsupp.single 2 k) = Finsupp.single 1 k := by
  simp [exponentMap, Finsupp.weight_single, smul_eq_mul]

/-- A power of `z` maps to the corresponding powers of `Y` and `T`. -/
@[simp]
theorem exponentMap_single_three (k : ℕ) :
    exponentMap (Finsupp.single 3 k) = Finsupp.single 1 k + Finsupp.single 2 k := by
  simp [exponentMap, Finsupp.weight_single, smul_add, smul_eq_mul]

/-- Replace as many copies of `wz` by `xy` as possible. -/
def reduce (m : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  let k := min (m 0) (m 3)
  Finsupp.equivFunOnFinite.symm ![m 0 - k, m 1 + k, m 2 + k, m 3 - k]

/-- An exponent is reduced when its monomial contains no factor `wz`. -/
def Reduced (m : Fin 4 →₀ ℕ) : Prop :=
  m 0 = 0 ∨ m 3 = 0

/-- Reducedness is the vanishing of the `w` or the `z` exponent. -/
@[simp]
theorem reduced_iff (m : Fin 4 →₀ ℕ) : Reduced m ↔ m 0 = 0 ∨ m 3 = 0 := Iff.rfl

/-- The remaining exponent of `w`. -/
@[simp]
theorem reduce_apply_zero (m : Fin 4 →₀ ℕ) :
    reduce m 0 = m 0 - min (m 0) (m 3) := rfl

/-- The resulting exponent of `x`. -/
@[simp]
theorem reduce_apply_one (m : Fin 4 →₀ ℕ) :
    reduce m 1 = m 1 + min (m 0) (m 3) := rfl

/-- The resulting exponent of `y`. -/
@[simp]
theorem reduce_apply_two (m : Fin 4 →₀ ℕ) :
    reduce m 2 = m 2 + min (m 0) (m 3) := rfl

/-- The remaining exponent of `z`. -/
@[simp]
theorem reduce_apply_three (m : Fin 4 →₀ ℕ) :
    reduce m 3 = m 3 - min (m 0) (m 3) := rfl

/-- A total exponent selector, reduced everywhere and a preimage on `t ≤ u + v`.
Outside this cone, natural subtraction truncates; the selector is not a global
section of `exponentMap`. -/
def normal (n : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  let b := min (n 0) (n 2)
  let d := n 2 - b
  Finsupp.equivFunOnFinite.symm ![n 0 - b, b, n 1 - d, d]

/-- The selected exponent of `w`. -/
@[simp]
theorem normal_apply_zero (n : Fin 3 →₀ ℕ) :
    normal n 0 = n 0 - min (n 0) (n 2) := rfl

/-- The selected exponent of `x`. -/
@[simp]
theorem normal_apply_one (n : Fin 3 →₀ ℕ) :
    normal n 1 = min (n 0) (n 2) := rfl

/-- The selected exponent of `y`. -/
@[simp]
theorem normal_apply_two (n : Fin 3 →₀ ℕ) :
    normal n 2 = n 1 - (n 2 - min (n 0) (n 2)) := rfl

/-- The selected exponent of `z`. -/
@[simp]
theorem normal_apply_three (n : Fin 3 →₀ ℕ) :
    normal n 3 = n 2 - min (n 0) (n 2) := rfl

/-- Replacing `wz` by `xy` preserves the image exponent. -/
@[simp]
theorem exponentMap_reduce (m : Fin 4 →₀ ℕ) :
    exponentMap (reduce m) = exponentMap m := by
  apply Finsupp.ext
  intro i
  fin_cases i
  · refine (exponentMap_apply_zero (reduce m)).trans
      (Eq.trans ?_ (exponentMap_apply_zero m).symm)
    rw [reduce_apply_zero, reduce_apply_one, add_comm (m 1) (min (m 0) (m 3)),
      ← add_assoc, Nat.sub_add_cancel (min_le_left (m 0) (m 3))]
  · refine (exponentMap_apply_one (reduce m)).trans
      (Eq.trans ?_ (exponentMap_apply_one m).symm)
    rw [reduce_apply_two, reduce_apply_three, add_assoc,
      Nat.add_sub_of_le (min_le_right (m 0) (m 3))]
  · refine (exponentMap_apply_two (reduce m)).trans
      (Eq.trans ?_ (exponentMap_apply_two m).symm)
    rw [reduce_apply_one, reduce_apply_three, add_assoc,
      Nat.add_sub_of_le (min_le_right (m 0) (m 3))]

/-- Reduction leaves no factor `wz`. -/
theorem reduce_reduced (m : Fin 4 →₀ ℕ) : Reduced (reduce m) := by
  rw [reduced_iff, reduce_apply_zero, reduce_apply_three]
  rcases le_total (m 0) (m 3) with h | h
  · left
    rw [min_eq_left h, Nat.sub_self]
  · right
    rw [min_eq_right h, Nat.sub_self]

/-- Two reduced exponents with the same image exponent are equal. -/
theorem eq_of_reduced_of_exponentMap_eq {m n : Fin 4 →₀ ℕ}
    (hm : Reduced m) (hn : Reduced n) (h : exponentMap m = exponentMap n) : m = n := by
  have h0 : m 0 + m 1 = n 0 + n 1 := by
    simpa only [exponentMap_apply_zero] using
      congrArg (fun p : Fin 3 →₀ ℕ => p 0) h
  have h1 : m 2 + m 3 = n 2 + n 3 := by
    simpa only [exponentMap_apply_one] using
      congrArg (fun p : Fin 3 →₀ ℕ => p 1) h
  have h2 : m 1 + m 3 = n 1 + n 3 := by
    simpa only [exponentMap_apply_two] using
      congrArg (fun p : Fin 3 →₀ ℕ => p 2) h
  obtain ⟨hmn0, hmn1, hmn2, hmn3⟩ :
      m 0 = n 0 ∧ m 1 = n 1 ∧ m 2 = n 2 ∧ m 3 = n 3 := by
    rcases (reduced_iff m).mp hm with hm | hm <;>
      rcases (reduced_iff n).mp hn with hn | hn <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  apply Finsupp.ext
  exact Fin.cases hmn0
    (Fin.cases hmn1 (Fin.cases hmn2 (Fin.cases hmn3 (fun i => i.elim0))))

/-- Reduction fixes an exponent exactly when it is reduced. -/
@[simp]
theorem reduce_eq_self_iff (m : Fin 4 →₀ ℕ) : reduce m = m ↔ Reduced m := by
  constructor
  · intro h
    rw [← h]
    exact reduce_reduced m
  · intro hm
    have hk : min (m 0) (m 3) = 0 := by
      rcases (reduced_iff m).mp hm with h | h
      · simp only [h, Nat.zero_min]
      · simp only [h, Nat.min_zero]
    apply Finsupp.ext
    intro i
    fin_cases i
    · exact (reduce_apply_zero m).trans (by rw [hk, Nat.sub_zero]; rfl)
    · exact (reduce_apply_one m).trans (by rw [hk, Nat.add_zero]; rfl)
    · exact (reduce_apply_two m).trans (by rw [hk, Nat.add_zero]; rfl)
    · exact (reduce_apply_three m).trans (by rw [hk, Nat.sub_zero]; rfl)

/-- Reduction is idempotent. -/
@[simp]
theorem reduce_reduce (m : Fin 4 →₀ ℕ) : reduce (reduce m) = reduce m := by
  exact (reduce_eq_self_iff (reduce m)).2 (reduce_reduced m)

/-- Two exponents have the same reduction exactly when they have the same image. -/
theorem reduce_eq_reduce_iff (m n : Fin 4 →₀ ℕ) :
    reduce m = reduce n ↔ exponentMap m = exponentMap n := by
  constructor
  · intro h
    simpa only [exponentMap_reduce] using congrArg exponentMap h
  · intro h
    apply eq_of_reduced_of_exponentMap_eq (reduce_reduced m) (reduce_reduced n)
    simpa only [exponentMap_reduce] using h

/-- The selector is reduced even outside the image cone. -/
theorem normal_reduced (n : Fin 3 →₀ ℕ) : Reduced (normal n) := by
  rw [reduced_iff]
  rcases le_total (n 0) (n 2) with h | h
  · left
    simp only [normal_apply_zero, min_eq_left h, Nat.sub_self]
  · right
    simp only [normal_apply_three, min_eq_right h, Nat.sub_self]

/-- On the image cone, the selected exponent is a preimage. The bound is needed
because the requested `z` exponent otherwise can exceed the `Y` exponent. -/
theorem exponentMap_normal (n : Fin 3 →₀ ℕ) (hn : n 2 ≤ n 0 + n 1) :
    exponentMap (normal n) = n := by
  have hd : n 2 - min (n 0) (n 2) ≤ n 1 := by
    rcases le_total (n 0) (n 2) with h | h
    · rw [min_eq_left h]
      exact Nat.sub_le_iff_le_add'.2 hn
    · rw [min_eq_right h, Nat.sub_self]
      exact Nat.zero_le _
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact (exponentMap_apply_zero (normal n)).trans (by
      rw [normal_apply_zero, normal_apply_one]
      exact Nat.sub_add_cancel (min_le_left (n 0) (n 2)))
  · exact (exponentMap_apply_one (normal n)).trans (by
      rw [normal_apply_two, normal_apply_three]
      exact Nat.sub_add_cancel hd)
  · exact (exponentMap_apply_two (normal n)).trans (by
      rw [normal_apply_one, normal_apply_three]
      exact Nat.add_sub_of_le (min_le_right (n 0) (n 2)))

/-- Selecting an exponent above an image exponent agrees with reduction. -/
@[simp]
theorem normal_exponentMap (m : Fin 4 →₀ ℕ) :
    normal (exponentMap m) = reduce m := by
  have hcone : exponentMap m 2 ≤ exponentMap m 0 + exponentMap m 1 := by
    simpa only [exponentMap_apply_zero, exponentMap_apply_one, exponentMap_apply_two] using
      Nat.add_le_add (Nat.le_add_left (m 1) (m 0)) (Nat.le_add_left (m 3) (m 2))
  exact eq_of_reduced_of_exponentMap_eq (normal_reduced _) (reduce_reduced m)
    ((exponentMap_normal _ hcone).trans (exponentMap_reduce m).symm)

/-- The range of the exponent map is exactly the cone `t ≤ u + v`. -/
theorem mem_mrange_iff (n : Fin 3 →₀ ℕ) :
    n ∈ AddMonoidHom.mrange exponentMap ↔ n 2 ≤ n 0 + n 1 := by
  rw [AddMonoidHom.mem_mrange]
  constructor
  · rintro ⟨m, h⟩
    have h0 := congrArg (fun q : Fin 3 →₀ ℕ ↦ q 0) h
    have h1 := congrArg (fun q : Fin 3 →₀ ℕ ↦ q 1) h
    have h2 := congrArg (fun q : Fin 3 →₀ ℕ ↦ q 2) h
    simp only [exponentMap_apply_zero] at h0
    simp only [exponentMap_apply_one] at h1
    simp only [exponentMap_apply_two] at h2
    omega
  · intro hn
    exact ⟨normal n, exponentMap_normal n hn⟩

/-- A target exponent has a unique reduced preimage exactly when it satisfies
`n 2 ≤ n 0 + n 1`. The bound excludes, for example, the exponent of `T` alone. -/
theorem existsUnique_reduced_preimage_iff (n : Fin 3 →₀ ℕ) :
    (∃! m : Fin 4 →₀ ℕ, Reduced m ∧ exponentMap m = n) ↔ n 2 ≤ n 0 + n 1 := by
  constructor
  · rintro ⟨m, ⟨_, h⟩, _⟩
    exact (mem_mrange_iff n).1 (AddMonoidHom.mem_mrange.mpr ⟨m, h⟩)
  · intro hn
    refine ⟨normal n, ⟨normal_reduced n, exponentMap_normal n hn⟩, ?_⟩
    intro m hm
    exact eq_of_reduced_of_exponentMap_eq hm.1 (normal_reduced n)
      (hm.2.trans (exponentMap_normal n hn).symm)

end ToricIdeals.SplitQuadric
