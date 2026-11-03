/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.MonomialTotalQuotient
public import Mathlib.Data.ZMod.Basic

/-!
# Regular fractions over non-domain coefficients

These examples retain a nonzero nilpotent coefficient in the constant case,
keep the even-power target smaller than the ambient polynomial ring, and
recover `X` from the cusp fraction `X³ / X²`. The zero ring also admits a
regular zero denominator.
-/

@[expose] public section

noncomputable section

open nonZeroDivisors

namespace Polynomial

private theorem coeff_two_ne_zero (P : Subalgebra (ZMod 4) ((ZMod 4)[X])) :
    algebraMap (ZMod 4) P 2 ≠ 0 := by
  intro h
  have hc := congrArg (fun p : P => (p : (ZMod 4)[X]).coeff 0) h
  change (C (2 : ZMod 4)).coeff 0 = (0 : (ZMod 4)[X]).coeff 0 at hc
  have htwo : (2 : ZMod 4) = 0 := by simpa using hc
  exact (by decide : (2 : ZMod 4) ≠ 0) htwo

section Constants

local notation "R" => ZMod 4
local notation "S" => (⊥ : AddSubmonoid ℕ)
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples (Nat.setGcd (S : Set ℕ)) =>
    (X : R[X]) ^ (s : ℕ))
local notation "QA" => FractionRing A
local notation "QB" => FractionRing B

/-- The nonzero square-zero coefficient is retained, but is not a regular denominator. -/
theorem zmod_four_constant_regular_fraction :
    algebraMap R A 2 ∉ A⁰ ∧
      fractionRingEquivAdjoinXPowSetGcd («R» := R) S
          (algebraMap A QA (algebraMap R A 2)) =
        algebraMap B QB (algebraMap R B 2) ∧
      algebraMap B QB (algebraMap R B 2) ≠ 0 ∧
      (algebraMap B QB (algebraMap R B 2)) ^ 2 = 0 := by
  have htwo : (2 : R) * 2 = 0 := by decide
  have hzero : algebraMap R A 2 * algebraMap R A 2 = 0 := by
    rw [← map_mul, htwo, map_zero]
  refine ⟨fun h => coeff_two_ne_zero A (h.1 _ hzero),
    fractionRingEquivAdjoinXPowSetGcd_coeff («R» := R) S 2, ?_, ?_⟩
  · intro h
    apply coeff_two_ne_zero B
    apply IsFractionRing.injective B QB
    simpa only [map_zero] using h
  · rw [pow_two, ← map_mul, ← map_mul, htwo, map_zero, map_zero]

end Constants

section EvenPowers

local notation "R" => ZMod 4
local notation "S" => AddSubmonoid.multiples (2 : ℕ)
local notation "d" => Nat.setGcd (S : Set ℕ)
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples d => (X : R[X]) ^ (s : ℕ))

/-- The even-power gcd target is the same proper subalgebra, not the ambient polynomial ring. -/
theorem zmod_four_even_power_target : B = A ∧ (X : R[X]) ∉ B := by
  have : Nontrivial R := ⟨⟨0, 1, by decide⟩⟩
  have hd : d = 2 := by
    apply Nat.dvd_antisymm
    · apply Nat.setGcd_dvd_of_mem
      exact (AddSubmonoid.mem_multiples_iff 2 2).mpr ⟨1, by simp⟩
    · apply Nat.dvd_setGcd_iff.mpr
      intro n hn
      obtain ⟨k, hk⟩ := (AddSubmonoid.mem_multiples_iff n 2).mp hn
      exact ⟨k, by simpa [nsmul_eq_mul, Nat.mul_comm] using hk.symm⟩
  refine ⟨by rw [hd], ?_⟩
  intro hX
  have h1 : 1 ∈ AddSubmonoid.multiples d :=
    (X_pow_mem_adjoin_X_pow_iff («R» := R) (AddSubmonoid.multiples d) 1).mp
      (by simpa using hX)
  obtain ⟨k, hk⟩ := (AddSubmonoid.mem_multiples_iff 1 d).mp h1
  have hdvd : d ∣ 1 := ⟨k, by simpa [nsmul_eq_mul, Nat.mul_comm] using hk.symm⟩
  rw [hd] at hdvd
  exact (by decide : ¬ (2 : ℕ) ∣ 1) hdvd

end EvenPowers

section Cusp

local notation "R" => ZMod 4
local notation "S" => AddSubmonoid.closure ({2, 3} : Set ℕ)
local notation "d" => Nat.setGcd (S : Set ℕ)
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples d => (X : R[X]) ^ (s : ℕ))
local notation "QA" => FractionRing A
local notation "QB" => FractionRing B

/-- The proper cusp inclusion recovers `X` from the regular fraction `X³ / X²` over `ZMod 4`. -/
theorem zmod_four_cusp_regular_fraction : ∃ a : A, ∃ s : A⁰, ∃ x : B,
    (a : R[X]) = X ^ 3 ∧ ((s : A) : R[X]) = X ^ 2 ∧ (x : R[X]) = X ∧
      (X : R[X]) ∉ A ∧
      fractionRingEquivAdjoinXPowSetGcd («R» := R) S (IsLocalization.mk' QA a s) =
        algebraMap B QB x := by
  have : Nontrivial R := ⟨⟨0, 1, by decide⟩⟩
  have h2 : 2 ∈ S := AddSubmonoid.subset_closure (by simp)
  have h3 : 3 ∈ S := AddSubmonoid.subset_closure (by simp)
  have hd : d = 1 := by
    apply Nat.dvd_antisymm
    · have h := Nat.dvd_gcd (Nat.setGcd_dvd_of_mem h2) (Nat.setGcd_dvd_of_mem h3)
      exact (show Nat.gcd 2 3 = 1 by decide) ▸ h
    · exact one_dvd _
  let a2 : A := ⟨X ^ 2, Algebra.subset_adjoin ⟨⟨2, h2⟩, rfl⟩⟩
  let a3 : A := ⟨X ^ 3, Algebra.subset_adjoin ⟨⟨3, h3⟩, rfl⟩⟩
  have hreg : IsRegular ((X : R[X]) ^ 2) := (monic_X_pow 2).isRegular
  have hpoly : (X : R[X]) ^ 2 ∈ (R[X])⁰ :=
    ⟨fun p hp => hreg.1 (by simpa using hp), fun p hp => hreg.2 (by simpa using hp)⟩
  have ha2 : a2 ∈ A⁰ :=
    mem_nonZeroDivisors_of_injective (f := (A).val) Subtype.val_injective hpoly
  have h1 : 1 ∈ AddSubmonoid.multiples d := by
    rw [hd]
    exact (AddSubmonoid.mem_multiples_iff 1 1).mpr ⟨1, by simp⟩
  have hx : (X : R[X]) ∈ B := by
    simpa using (Algebra.subset_adjoin ⟨⟨1, h1⟩, rfl⟩ : (X : R[X]) ^ 1 ∈ B)
  let x : B := ⟨X, hx⟩
  refine ⟨a3, ⟨a2, ha2⟩, x, rfl, rfl, rfl, ?_, ?_⟩
  · intro hX
    have hn : 1 ∈ S :=
      (X_pow_mem_adjoin_X_pow_iff («R» := R) S 1).mp (by simpa using hX)
    have hne : (1 : ℕ) ≠ 1 := by
      apply AddSubmonoid.closure_induction (motive := fun n _ => n ≠ 1) ?_ (by decide) ?_ hn
      · intro n hn
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl <;> decide
      · intro a b _ _ ha hb
        omega
    exact hne rfl
  · rw [fractionRingEquivAdjoinXPowSetGcd_mk']
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change (X : R[X]) ^ 3 = X * X ^ 2
    exact (pow_succ (X : R[X]) 2).trans (mul_comm _ _)

end Cusp

section Trivial

local notation "R" => ZMod 1
local notation "S" => (⊥ : AddSubmonoid ℕ)
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples (Nat.setGcd (S : Set ℕ)) =>
    (X : R[X]) ^ (s : ℕ))
local notation "QA" => FractionRing A

/-- Zero is a regular denominator over the zero coefficient ring. -/
theorem zmod_one_regular_zero_denominator : ∃ s : A⁰, (s : A) = 0 ∧
    fractionRingEquivAdjoinXPowSetGcd («R» := R) S (IsLocalization.mk' QA 0 s) = 0 := by
  have hz : (0 : A) ∈ A⁰ :=
    ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  refine ⟨⟨0, hz⟩, rfl, ?_⟩
  rw [fractionRingEquivAdjoinXPowSetGcd_mk']
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  simp

end Trivial

end Polynomial
