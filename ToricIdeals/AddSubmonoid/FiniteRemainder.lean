/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Data.Finsupp.Interval
import Mathlib.Tactic

/-!
# Finite remainders for relative roots of exponent monoids

For a finitely generated additive submonoid of natural exponent vectors, every
root that is also a difference of monoid elements is a monoid translate of one
of finitely many such roots. The variable type is arbitrary.

The proof divides the coefficients of a positive multiple by its multiplier.
The quotients give the monoid translate, and the remainders put the remaining
exponent in the finite interval bounded by the sum of the generators. Keeping
the difference witness ensures that this remaining exponent is relative to
the original monoid, rather than merely in its ambient root closure.

## References

The proof uses Mathlib's finite-generation API by Riccardo Brasca, the closure
coefficient representation by Andrew Yang, and the finite intervals of finitely
supported functions by Yaël Dillies.
-/

@[expose] public section

namespace AddSubmonoid

universe v

variable {σ : Type v}

/-- A finitely generated exponent monoid has finitely many relative root
remainders: every exponent that is both a difference of monoid elements and a
root of a positive multiple is a monoid element plus one of these remainders.
The remainders satisfy both conditions themselves. -/
theorem exists_finset_relative_root_remainder
    (S : AddSubmonoid (σ →₀ ℕ)) (hS : S.FG) :
    ∃ E : Finset (σ →₀ ℕ),
      (∀ e ∈ E,
        (∃ b, b ∈ S ∧ b + e ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • e ∈ S) ∧
      ∀ n : σ →₀ ℕ,
        ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
        ∃ s, s ∈ S ∧ ∃ e, e ∈ E ∧ n = s + e := by
  classical
  obtain ⟨F, hF⟩ := hS
  let bound : σ →₀ ℕ := ∑ i : F, i.val
  let E := (Finset.Icc 0 bound).filter fun e =>
    (∃ b, b ∈ S ∧ b + e ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • e ∈ S
  refine ⟨E, ?_, ?_⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro n hn
    obtain ⟨b, hb, hbn⟩ := hn.1
    obtain ⟨k, hk, hkn⟩ := hn.2
    have hkn' : k • n ∈ closure (F : Set (σ →₀ ℕ)) := by
      rwa [hF]
    obtain ⟨a, ha⟩ := mem_closure_finset'.mp hkn'
    let q : σ →₀ ℕ := ∑ i : F, (a i / k) • i.val
    let r : σ →₀ ℕ := ∑ i : F, (a i % k) • i.val
    have hgen (i : F) : i.val ∈ S := by
      rw [← hF]
      exact subset_closure i.property
    have hq : q ∈ S :=
      S.sum_mem fun i _ => S.nsmul_mem (hgen i) _
    have hr : r ∈ S :=
      S.sum_mem fun i _ => S.nsmul_mem (hgen i) _
    have hsplit : k • n = k • q + r := by
      rw [ha]
      dsimp [q, r]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, ← add_smul, Nat.div_add_mod]
    have hqn : q ≤ n := by
      intro j
      have hj := congrArg (fun z : σ →₀ ℕ => z j) hsplit
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hj
      by_contra h
      have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) hk
      omega
    let e := n - q
    have hne : n = q + e := (add_tsub_cancel_of_le hqn).symm
    have her : k • e = r := by
      apply add_left_cancel (a := k • q)
      calc
        k • q + k • e = k • (q + e) := (nsmul_add _ _ _).symm
        _ = k • n := congrArg (fun z : σ →₀ ℕ => k • z) hne.symm
        _ = k • q + r := hsplit
    have hrbound : r ≤ k • bound := by
      intro j
      simp only [r, bound, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul_right (i.val j) (Nat.le_of_lt (Nat.mod_lt (a i) hk))
    have hebound : e ≤ bound := by
      intro j
      have hj := hrbound j
      rw [← her] at hj
      simp only [Finsupp.smul_apply, smul_eq_mul] at hj
      by_contra h
      have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) hk
      omega
    have he : e ∈ E := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨bot_le, hebound⟩, ?_⟩
      refine ⟨⟨b + q, S.add_mem hb hq, ?_⟩, k, hk, ?_⟩
      · simpa only [add_assoc, ← hne] using hbn
      · rwa [her]
    exact ⟨q, hq, e, he, hne⟩

end AddSubmonoid
