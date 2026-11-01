/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.MonomialSubalgebra
public import ToricIdeals.NumberTheory.FrobeniusNumber
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Canonical fraction fields of natural-number monomial subalgebras

The existing monomial subalgebra for `S` and that for the multiples of `Nat.setGcd S`
have the same fraction field through their actual inclusion. The comparison is specifically
`IsFractionRing.map` between their own `FractionRing` types, and it respects coefficients.
No normality assumption on the coefficient domain is needed, and gcd zero is included.

The exponent argument reuses `Nat.setGcd_eq_iff_finite_gaps`. The fraction-field construction,
its compatibility and the field-range generation argument are existing Mathlib interfaces.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] (S : AddSubmonoid ℕ)

local notation "A" =>
  Algebra.adjoin R (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "D" => AddSubmonoid.multiples (Nat.setGcd (S : Set ℕ))
local notation "B" =>
  Algebra.adjoin R (Set.range fun s : D => (X : R[X]) ^ (s : ℕ))

/-- The actual inclusion into the gcd monomial subalgebra induces a bijection of the two
own fraction fields, fixing the coefficient images. Only a coefficient domain is assumed.
The existential choice is an inclusion *proof*, not a choice of field isomorphism. -/
theorem exists_bijective_fractionRingMap_adjoin_X_pow_setGcd :
    ∃ h : A ≤ B,
      let φ := IsFractionRing.map (K := FractionRing A) (L := FractionRing B)
        (j := (Subalgebra.inclusion h).toRingHom) (Subalgebra.inclusion_injective h)
      Function.Bijective φ ∧ ∀ r : R,
        φ (algebraMap A (FractionRing A) (algebraMap R A r)) =
          algebraMap B (FractionRing B) (algebraMap R B r) := by
  let d := Nat.setGcd (S : Set ℕ)
  have h : A ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    apply (X_pow_mem_adjoin_X_pow_iff D (s : ℕ)).2
    apply (AddSubmonoid.mem_multiples_iff (s : ℕ) d).2
    obtain ⟨n, hn⟩ := Nat.setGcd_dvd_of_mem s.property
    exact ⟨n, by simpa [d, nsmul_eq_mul, Nat.mul_comm] using hn.symm⟩
  refine ⟨h, ?_⟩
  let : Algebra A B := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let α := algebraMap A (FractionRing A)
  let β := algebraMap B (FractionRing B)
  let φ := IsFractionRing.map (K := FractionRing A) (L := FractionRing B)
    (j := (Subalgebra.inclusion h).toRingHom) (Subalgebra.inclusion_injective h)
  change Function.Bijective φ ∧ ∀ r : R,
    φ (α (algebraMap R A r)) = β (algebraMap R B r)
  have hmap (a : A) : φ (α a) = β ((Subalgebra.inclusion h) a) := by
    exact IsLocalization.map_eq _ a
  have hcoeff (r : R) : φ (α (algebraMap R A r)) = β (algebraMap R B r) := by
    rw [hmap, AlgHom.commutes]
  refine ⟨⟨φ.injective, ?_⟩, hcoeff⟩
  obtain ⟨b, hb, hbd⟩ : ∃ b : ℕ, b ∈ S ∧ b + d ∈ S := by
    by_cases hd : d = 0
    · exact ⟨0, S.zero_mem, by simpa only [hd, Nat.zero_add] using S.zero_mem⟩
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hfinite := ((Nat.setGcd_eq_iff_finite_gaps S d).mp rfl).2
    obtain ⟨N, hN⟩ := hfinite.bddAbove
    have hmem (n : ℕ) (hn : N < n) (hdn : d ∣ n) : n ∈ S := by
      by_contra hnot
      exact (Nat.not_lt_of_ge (hN ⟨hdn, hnot⟩)) hn
    have hlarge : N < (N + 1) * d :=
      lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_mul_of_pos_right (N + 1) hdpos)
    have hmultiple : d ∣ (N + 1) * d := ⟨N + 1, Nat.mul_comm _ _⟩
    exact ⟨(N + 1) * d, hmem _ hlarge hmultiple,
      hmem _ (by omega) (dvd_add hmultiple dvd_rfl)⟩
  let xb : A := ⟨(X : R[X]) ^ b, (X_pow_mem_adjoin_X_pow_iff S b).2 hb⟩
  let xbd : A := ⟨(X : R[X]) ^ (b + d), (X_pow_mem_adjoin_X_pow_iff S (b + d)).2 hbd⟩
  have hdmem : d ∈ D := (AddSubmonoid.mem_multiples_iff d d).2 ⟨1, one_nsmul d⟩
  let xd : B := ⟨(X : R[X]) ^ d, (X_pow_mem_adjoin_X_pow_iff D d).2 hdmem⟩
  have hden : β ((Subalgebra.inclusion h) xb) ≠ 0 := by
    intro hz
    have hi : (Subalgebra.inclusion h) xb = 0 :=
      (IsFractionRing.injective B (FractionRing B)) (by simpa only [map_zero] using hz)
    have hx : xb = 0 := (Subalgebra.inclusion_injective h)
      (by simpa only [map_zero] using hi)
    have hx' : (X : R[X]) ^ b = 0 := congrArg (fun z : A => (z : R[X])) hx
    exact (pow_ne_zero b X_ne_zero) hx'
  have hxd : β xd ∈ φ.fieldRange := by
    refine ⟨α xbd / α xb, ?_⟩
    rw [map_div₀, hmap, hmap, div_eq_iff hden, ← map_mul]
    congr 1
    apply Subtype.ext
    change (X : R[X]) ^ (b + d) = (X : R[X]) ^ d * (X : R[X]) ^ b
    rw [pow_add, mul_comm]
  have hB (q : R[X]) (hq : q ∈ B) : β ⟨q, hq⟩ ∈ φ.fieldRange := by
    induction hq using Algebra.adjoin_induction with
    | mem q hq =>
      rcases hq with ⟨s, rfl⟩
      obtain ⟨n, hn⟩ := (AddSubmonoid.mem_multiples_iff (s : ℕ) d).mp s.property
      convert (φ.fieldRange).pow_mem hxd n using 1
      rw [← map_pow]
      congr 1
      apply Subtype.ext
      change (X : R[X]) ^ (s : ℕ) = ((X : R[X]) ^ d) ^ n
      rw [← pow_mul]
      congr 1
      simpa [nsmul_eq_mul, Nat.mul_comm] using hn.symm
    | algebraMap r =>
      change β (algebraMap R B r) ∈ φ.fieldRange
      exact ⟨α (algebraMap R A r), hcoeff r⟩
    | add p q hp hq ihp ihq =>
      change β ((⟨p, hp⟩ : B) + ⟨q, hq⟩) ∈ φ.fieldRange
      simpa only [map_add] using (φ.fieldRange).add_mem ihp ihq
    | mul p q hp hq ihp ihq =>
      change β ((⟨p, hp⟩ : B) * ⟨q, hq⟩) ∈ φ.fieldRange
      simpa only [map_mul] using (φ.fieldRange).mul_mem ihp ihq
  have htop : φ.fieldRange = ⊤ := by
    apply top_unique
    rw [← IsFractionRing.closure_range_algebraMap B (FractionRing B)]
    apply Subfield.closure_le.2
    rintro _ ⟨q, rfl⟩
    exact hB q.val q.property
  intro y
  have hy : y ∈ φ.fieldRange := by rw [htop]; trivial
  exact hy

end Polynomial
