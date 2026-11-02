/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite additive translate covers in the natural numbers

A nonzero additive submonoid of the natural numbers covers every subset by
finitely many translates whose representatives belong to that subset. For a
submonoid target, the only other possibility is the zero submonoid.
-/

@[expose] public section

open scoped Pointwise

namespace AddSubmonoid

/-- A subset of the natural numbers has a finite cover by additive translates
of a submonoid, with representatives in the subset, exactly when the submonoid
is nonzero or the subset is finite. -/
theorem exists_finite_subset_add_iff (S : AddSubmonoid ℕ) (U : Set ℕ) :
    (∃ E : Set ℕ, E.Finite ∧ E ⊆ U ∧ U ⊆ (S : Set ℕ) + E) ↔
      S ≠ ⊥ ∨ U.Finite := by
  classical
  constructor
  · rintro ⟨E, hE, _, hcover⟩
    by_cases hS : S = ⊥
    · right
      apply hE.subset
      intro n hn
      obtain ⟨s, hs, e, he, hse⟩ := Set.mem_add.mp (hcover hn)
      have hs0 : s = 0 := (eq_bot_iff_forall S).mp hS s hs
      rw [hs0, zero_add] at hse
      exact hse ▸ he
    · exact Or.inl hS
  · rintro (hS | hU)
    · obtain ⟨m, hm, hm0⟩ := S.bot_or_exists_ne_zero.resolve_left hS
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      -- Use the least member of each occupied residue class, not the raw remainder.
      let E : Set ℕ := {e | e ∈ U ∧ ∀ u ∈ U, u % m = e % m → e ≤ u}
      have hE : E.Finite := by
        refine Set.Finite.of_injOn
          (f := fun e : ℕ => e % m) (t := {r : ℕ | r < m})
          (fun e _ => Nat.mod_lt e hmpos) ?_ (Set.finite_lt_nat m)
        intro e he u hu hmod
        exact le_antisymm (he.2 u hu.1 hmod.symm) (hu.2 e he.1 hmod)
      refine ⟨E, hE, fun e he => he.1, ?_⟩
      intro n hn
      have hex : ∃ e : ℕ, e ∈ U ∧ e % m = n % m := ⟨n, hn, rfl⟩
      let e := Nat.find hex
      have he : e ∈ U ∧ e % m = n % m := Nat.find_spec hex
      have hen : e ≤ n := Nat.find_min' hex ⟨hn, rfl⟩
      have heE : e ∈ E := by
        refine ⟨he.1, ?_⟩
        intro u hu hue
        exact Nat.find_min' hex ⟨hu, hue.trans he.2⟩
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add (n := m) hen).mp he.2
      refine Set.mem_add.mpr ⟨k * m, ?_, e, heE, ?_⟩
      · simpa only [SetLike.mem_coe, Nat.nsmul_eq_mul] using S.nsmul_mem hm k
      · calc
          k * m + e = e + m * k := by rw [add_comm, mul_comm k m]
          _ = n := hk.symm
    · refine ⟨U, hU, Set.Subset.rfl, ?_⟩
      intro n hn
      exact Set.mem_add.mpr ⟨0, S.zero_mem, n, hn, zero_add n⟩

/-- An additive submonoid of the natural numbers has a finite cover by
translates of another submonoid, with representatives in the target, exactly
when the translating submonoid is nonzero or the target is the zero submonoid.
No containment between the two submonoids is required. -/
theorem exists_finite_subset_add_submonoid_iff (S T : AddSubmonoid ℕ) :
    (∃ E : Set ℕ, E.Finite ∧ E ⊆ (T : Set ℕ) ∧
      (T : Set ℕ) ⊆ (S : Set ℕ) + E) ↔
      S ≠ ⊥ ∨ T = ⊥ := by
  rw [exists_finite_subset_add_iff]
  constructor
  · rintro (hS | hT)
    · exact Or.inl hS
    · right
      apply (eq_bot_iff_forall T).mpr
      intro m hm
      by_contra hm0
      have hinf : (T : Set ℕ).Infinite :=
        Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k * m)
          (mul_left_injective₀ hm0) fun k => by
            simpa only [SetLike.mem_coe, Nat.nsmul_eq_mul] using T.nsmul_mem hm k
      exact hinf hT
  · rintro (hS | rfl)
    · exact Or.inl hS
    · exact Or.inr (by simpa only [coe_bot] using Set.finite_singleton 0)

end AddSubmonoid
