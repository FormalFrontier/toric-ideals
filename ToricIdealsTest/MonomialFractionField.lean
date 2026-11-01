/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.MonomialFractionField

/-!
# Controls for the canonical gcd fraction-field comparison

The universal control fixes the actual map on both the monomial algebra and coefficients,
not merely the existence of an abstract field isomorphism. The arithmetic controls distinguish
the constant, even-exponent and cusp cases. All coefficient domains are permitted.
-/

public section

open Polynomial

namespace MonomialFractionFieldTests

section

variable {R : Type*} [CommRing R] [IsDomain R] (S : AddSubmonoid ℕ)

local notation "A" =>
  Algebra.adjoin R (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "D" => AddSubmonoid.multiples (Nat.setGcd (S : Set ℕ))
local notation "B" =>
  Algebra.adjoin R (Set.range fun s : D => (X : R[X]) ^ (s : ℕ))

/-- The equivalence is induced by the actual inclusion and fixes both base and
coefficient images. -/
theorem canonicalComparison :
    ∃ h : A ≤ B, ∃ e : FractionRing A ≃+* FractionRing B,
      e.toRingHom = IsFractionRing.map (K := FractionRing A) (L := FractionRing B)
        (j := (Subalgebra.inclusion h).toRingHom) (Subalgebra.inclusion_injective h) ∧
      (∀ a : A, e (algebraMap A (FractionRing A) a) =
        algebraMap B (FractionRing B) ((Subalgebra.inclusion h) a)) ∧
      ∀ r : R, e (algebraMap A (FractionRing A) (algebraMap R A r)) =
        algebraMap B (FractionRing B) (algebraMap R B r) := by
  obtain ⟨h, hbij, hcoeff⟩ := exists_bijective_fractionRingMap_adjoin_X_pow_setGcd (R := R) S
  let φ := IsFractionRing.map (K := FractionRing A) (L := FractionRing B)
    (j := (Subalgebra.inclusion h).toRingHom) (Subalgebra.inclusion_injective h)
  refine ⟨h, RingEquiv.ofBijective φ hbij, rfl, ?_, hcoeff⟩
  intro a
  change φ (algebraMap A (FractionRing A) a) =
    algebraMap B (FractionRing B) ((Subalgebra.inclusion h) a)
  exact IsLocalization.map_eq _ a

example (h : A ≤ B) :
    let _ : Algebra A B := (Subalgebra.inclusion h).toRingHom.toAlgebra
    algebraMap A B = (Subalgebra.inclusion h).toRingHom := by
  rfl

end

example : Nat.setGcd ((⊥ : AddSubmonoid ℕ) : Set ℕ) = 0 := by
  apply (Nat.setGcd_eq_iff_finite_gaps (⊥ : AddSubmonoid ℕ) 0).mpr
  exact ⟨by simp, by simp⟩

example : Nat.setGcd ((AddSubmonoid.multiples 2 : AddSubmonoid ℕ) : Set ℕ) = 2 := by
  apply Nat.dvd_antisymm
  · exact Nat.setGcd_dvd_of_mem ((AddSubmonoid.mem_multiples_iff 2 2).2 ⟨1, by simp⟩)
  · apply Nat.dvd_setGcd_iff.mpr
    intro n hn
    obtain ⟨k, hk⟩ := (AddSubmonoid.mem_multiples_iff n 2).mp hn
    exact ⟨k, by simpa [nsmul_eq_mul, Nat.mul_comm] using hk.symm⟩

example : Nat.setGcd
    ((AddSubmonoid.closure ({2, 3} : Set ℕ) : AddSubmonoid ℕ) : Set ℕ) = 1 := by
  let S : AddSubmonoid ℕ := AddSubmonoid.closure ({2, 3} : Set ℕ)
  change Nat.setGcd (S : Set ℕ) = 1
  have htwo : 2 ∈ S := AddSubmonoid.subset_closure (by simp)
  have hthree : 3 ∈ S := AddSubmonoid.subset_closure (by simp)
  apply Nat.dvd_one.mp
  exact (Nat.dvd_add_iff_right (Nat.setGcd_dvd_of_mem htwo)).mpr
    (by simpa using Nat.setGcd_dvd_of_mem hthree)

end MonomialFractionFieldTests
