/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Arithmetic recognition of the gcd of an additive submonoid

For an arbitrary additive submonoid `S` of `ℕ`, its gcd is the unique natural number
whose multiples contain `S` and have only finitely many omissions from `S`.
These are relative gaps: the complement of `S` in all of `ℕ` need not be finite.
The zero submonoid has gcd zero and no relative gaps.

## Main results

* `Nat.setGcd_eq_iff_finite_gaps` recognizes the gcd from containment and finite relative gaps.
* `Nat.existsUnique_dvd_and_finite_gaps` gives the resulting unique-existence statement.

## References

The forward implication uses Mathlib's conductor theorem in
`Mathlib.NumberTheory.FrobeniusNumber`, with its natural-span/additive-submonoid interface.
The converse compares consecutive large multiples, following the adjacent-member divisibility
argument in Mathlib's `exists_frobeniusNumber_iff`.
-/

@[expose] public section

namespace Nat

/-- The gcd of an additive submonoid of `ℕ` is characterized by containing all its elements
among its multiples and having only finitely many missing multiples. This includes gcd zero. -/
theorem setGcd_eq_iff_finite_gaps (S : AddSubmonoid ℕ) (d : ℕ) :
    setGcd (S : Set ℕ) = d ↔
      (∀ n ∈ S, d ∣ n) ∧ {n : ℕ | d ∣ n ∧ n ∉ S}.Finite := by
  constructor
  · rintro rfl
    refine ⟨fun _ hn ↦ setGcd_dvd_of_mem hn, ?_⟩
    have h := finite_setOfPred_setGcd_dvd_and_mem_span (S : Set ℕ)
    change {n : ℕ | setGcd (S : Set ℕ) ∣ n ∧
      n ∉ (Submodule.span ℕ (S : Set ℕ)).toAddSubmonoid}.Finite at h
    simpa only [Submodule.span_nat_eq] using h
  · rintro ⟨hdiv, hfinite⟩
    refine dvd_antisymm ?_ (dvd_setGcd_iff.mpr hdiv)
    by_cases hd : d = 0
    · subst d
      exact dvd_zero _
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨N, hN⟩ := hfinite.bddAbove
    have hmem (n : ℕ) (hn : N < n) (hdn : d ∣ n) : n ∈ S := by
      by_contra hnot
      exact (Nat.not_lt_of_ge (hN ⟨hdn, hnot⟩)) hn
    have hlarge : N < (N + 1) * d :=
      lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_mul_of_pos_right (N + 1) hdpos)
    have hmultiple : d ∣ (N + 1) * d := ⟨N + 1, Nat.mul_comm _ _⟩
    have hfirst := setGcd_dvd_of_mem (hmem _ hlarge hmultiple)
    have hsecond := setGcd_dvd_of_mem
      (hmem ((N + 1) * d + d) (by omega) (dvd_add hmultiple dvd_rfl))
    exact (Nat.dvd_add_iff_right hfirst).mpr hsecond

/-- Every additive submonoid of `ℕ` has a unique arithmetic step whose multiples contain it
and have only finitely many omissions from it. No positivity or finite-generation assumption
is required. -/
theorem existsUnique_dvd_and_finite_gaps (S : AddSubmonoid ℕ) :
    ∃! d : ℕ, (∀ n ∈ S, d ∣ n) ∧ {n : ℕ | d ∣ n ∧ n ∉ S}.Finite := by
  refine ⟨setGcd (S : Set ℕ), (setGcd_eq_iff_finite_gaps S _).mp rfl, ?_⟩
  intro d hd
  exact ((setGcd_eq_iff_finite_gaps S d).mpr hd).symm

end Nat
