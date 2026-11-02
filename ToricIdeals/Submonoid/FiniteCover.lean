/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Choose

/-!
# Uniform exponents from finite translate covers

Let `S` and `T` be submonoids of a cancellative commutative monoid. If
`T ⊆ S * E` for a finite set `E ⊆ T`, the single positive exponent
`E.ncard.factorial` sends every element of `T` into `S`. No inclusion between
`S` and `T` is required.

The additive counterpart gives `E.ncard.factorial • t ∈ S` for every `t ∈ T`
when `T ⊆ S + E` for a finite set `E ⊆ T`. Pointwise positive-power and
positive-multiple membership statements are also available.
-/

@[expose] public section

open scoped Pointwise

universe v

namespace Submonoid

/-- A finite left translate cover of `T` by `S`, with remainders in `T`,
gives the uniform positive exponent `E.ncard.factorial` for membership in `S`.
The submonoids need not be comparable. -/
@[to_additive AddSubmonoid.factorial_nsmul_mem_of_finite_cover
  /-- A finite left additive translate cover of `T` by `S`, with remainders
  in `T`, gives the uniform positive natural-number multiplier
  `E.ncard.factorial` for membership in `S`. The additive submonoids need
  not be comparable. -/]
theorem pow_factorial_mem_of_finite_cover
    {M : Type v} [CancelCommMonoid M]
    {S T : Submonoid M} {E : Set M}
    (hE : E.Finite) (hET : E ⊆ (T : Set M))
    (hcover : (T : Set M) ⊆ (S : Set M) * E)
    {t : M} (ht : t ∈ T) :
    t ^ E.ncard.factorial ∈ S := by
  classical
  let : Fintype E := hE.fintype
  have hstep : ∀ e : E, ∃ s ∈ S, ∃ e' : E, (e : M) * t = s * (e' : M) := by
    intro e
    obtain ⟨s, hs, e', he', h⟩ :=
      Set.mem_mul.mp (hcover (T.mul_mem (hET e.property) ht))
    exact ⟨s, hs, ⟨e', he'⟩, h.symm⟩
  choose w hw f hf using hstep
  -- Accumulate weights from every starting remainder, including points on a later cycle.
  have hiter : ∀ (k : ℕ) (e : E), ∃ s ∈ S,
      (e : M) * t ^ k = s * (f^[k] e : M) := by
    intro k
    induction k with
    | zero =>
      intro e
      exact ⟨1, S.one_mem, by simp⟩
    | succ k ih =>
      intro e
      obtain ⟨s, hs, h⟩ := ih (f e)
      refine ⟨w e * s, S.mul_mem (hw e) hs, ?_⟩
      calc
        (e : M) * t ^ (k + 1) = ((e : M) * t) * t ^ k := by
          rw [pow_succ', mul_assoc]
        _ = w e * ((f e : M) * t ^ k) := by rw [hf e, mul_assoc]
        _ = (w e * s) * (f^[k] (f e) : M) := by rw [h, mul_assoc]
        _ = (w e * s) * (f^[k + 1] e : M) := by
          rw [Function.iterate_succ_apply]
  obtain ⟨_, _, e, he, _⟩ := Set.mem_mul.mp (hcover T.one_mem)
  let e₀ : E := ⟨e, he⟩
  obtain ⟨i, j, hij, hrep⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem
      (fun k : ℕ => (f^[k] e₀).property) hE
  -- Repetition gives a positive period at the repeated point, not necessarily at e₀.
  have hcycle : (f^[j - i] (f^[i] e₀) : M) = (f^[i] e₀ : M) := by
    rw [← Function.iterate_add_apply f (j - i) i e₀, Nat.sub_add_cancel hij.le]
    exact hrep.symm
  have hperiodic : f^[i] e₀ ∈ Function.periodicPts f :=
    Function.mk_mem_periodicPts (f := f) (Nat.sub_pos_of_lt hij) (Subtype.ext hcycle)
  have hfactorial : Function.IsPeriodicPt f E.ncard.factorial (f^[i] e₀) := by
    simpa only [Set.fintypeCard_eq_ncard] using
      (Function.isPeriodicPt_factorial_card_of_mem_periodicPts (f := f) hperiodic)
  obtain ⟨s, hs, h⟩ := hiter E.ncard.factorial (f^[i] e₀)
  rw [hfactorial.eq, mul_comm s] at h
  exact (mul_left_cancel h).symm ▸ hs

/-- A finite left translate cover of `T` by `S`, with remainders in `T`,
forces every element of `T` to have a positive power in `S`. The submonoids
need not be comparable. -/
@[to_additive
  /-- A finite left additive translate cover of `T` by `S`, with remainders
  in `T`, forces every element of `T` to have a positive natural-number
  multiple in `S`. The additive submonoids need not be comparable. -/]
theorem exists_pow_mem_of_finite_cover
    {M : Type v} [CancelCommMonoid M]
    {S T : Submonoid M} {E : Set M}
    (hE : E.Finite) (hET : E ⊆ (T : Set M))
    (hcover : (T : Set M) ⊆ (S : Set M) * E)
    {t : M} (ht : t ∈ T) :
    ∃ n : ℕ, 0 < n ∧ t ^ n ∈ S := by
  exact ⟨E.ncard.factorial, Nat.factorial_pos _,
    pow_factorial_mem_of_finite_cover hE hET hcover ht⟩

end Submonoid
