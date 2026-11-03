/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.MonomialFinite
public import ToricIdeals.Polynomial.MonomialFractionField
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Total quotient rings of monomial subalgebras

For an additive submonoid `S` of `ℕ`, the inclusion of its monomial subalgebra
into the monomial subalgebra at `Nat.setGcd S` preserves regular denominators.
A common regular monomial clears elements of the larger subalgebra, including
simultaneously the numerator and denominator of a fraction.

The coefficient ring need not be a domain or nontrivial. The zero gcd gives
constant polynomials, and a positive gcd does not identify its monomial
subalgebra with the ambient polynomial ring.

## References

The exponent witness uses Mathlib's eventual-membership theorem for additive
submonoids of `ℕ` (Alex Zhao, Daniel Buth, Sebastian Meier and Junyan Xu).
Regularity uses Mathlib's cancellation theorem for monic polynomials. The
subalgebras, support characterization and coefficient-preserving inclusion are
those of `MonomialSubalgebra` and `MonomialFinite`.
-/

@[expose] public section

noncomputable section

universe u

namespace Polynomial

open nonZeroDivisors

section Semiring

variable {R : Type u} [CommSemiring R] (S : AddSubmonoid ℕ)

local notation "A" => Algebra.adjoin R (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "d" => Nat.setGcd (S : Set ℕ)
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples d => (X : R[X]) ^ (s : ℕ))

/-- One monomial from the exponent subalgebra sends every polynomial in its
gcd extension back to the exponent subalgebra. -/
theorem exists_X_pow_mul_mem_adjoin_X_pow_setGcd :
    ∃ c : ℕ, c ∈ S ∧ ∀ p : R[X], p ∈ B → (X : R[X]) ^ c * p ∈ A := by
  obtain ⟨c, hc, hshift⟩ : ∃ c : ℕ, c ∈ S ∧
      ∀ n : ℕ, n ∈ AddSubmonoid.multiples d → c + n ∈ S := by
    by_cases hd : d = 0
    · refine ⟨0, S.zero_mem, ?_⟩
      intro n hn
      obtain ⟨k, hk⟩ := (AddSubmonoid.mem_multiples_iff n d).mp hn
      have hn0 : n = 0 := by simpa [hd] using hk.symm
      simp [hn0]
    · obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (S : Set ℕ)
      have hclosure : AddSubmonoid.closure (S : Set ℕ) ≤ S :=
        AddSubmonoid.closure_le.mpr (fun _ h => h)
      have hge : N ≤ d * N := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right N (Nat.one_le_iff_ne_zero.mpr hd)
      have hdiv : d ∣ d * N := ⟨N, rfl⟩
      refine ⟨d * N, hclosure (hN _ hge hdiv), ?_⟩
      intro n hn
      obtain ⟨k, hk⟩ := (AddSubmonoid.mem_multiples_iff n d).mp hn
      have hdn : d ∣ n :=
        ⟨k, by simpa [nsmul_eq_mul, Nat.mul_comm] using hk.symm⟩
      exact hclosure (hN _ (hge.trans (Nat.le_add_right _ _)) (dvd_add hdiv hdn))
  refine ⟨c, hc, ?_⟩
  intro p hp
  rw [← p.sum_monomial_eq, sum_def, Finset.mul_sum]
  apply Subalgebra.sum_mem
  intro n hn
  have hnB : n ∈ AddSubmonoid.multiples d := by
    by_contra h
    exact (mem_support_iff.mp hn) ((mem_adjoin_X_pow_iff _ _).mp hp n h)
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_add]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin ⟨⟨c + n, hshift n hnB⟩, rfl⟩)

private theorem adjoin_X_pow_setGcd_inclusion_injective :
    Function.Injective
      (Subalgebra.inclusion (adjoin_X_pow_le_adjoin_X_pow_setGcd (R := R) S)) :=
  Subalgebra.inclusion_injective _

end Semiring

section Ring

variable {R : Type u} [CommRing R] (S : AddSubmonoid ℕ)

local notation "A" => Algebra.adjoin R (Set.range fun s : S => (X : R[X]) ^ (s : ℕ))
local notation "d" => Nat.setGcd (S : Set ℕ)
local notation "B" => Algebra.adjoin R
  (Set.range fun s : AddSubmonoid.multiples d => (X : R[X]) ^ (s : ℕ))
local notation "j" => Subalgebra.inclusion
  (adjoin_X_pow_le_adjoin_X_pow_setGcd (R := R) S)

private theorem exists_regular_clearing_adjoin_X_pow_setGcd :
    ∃ w : A, w ∈ A⁰ ∧ j w ∈ B⁰ ∧ ∀ b : B, ∃ a : A, j a = j w * b := by
  obtain ⟨c, hc, hclear⟩ := exists_X_pow_mul_mem_adjoin_X_pow_setGcd (R := R) S
  let w : A := ⟨X ^ c, Algebra.subset_adjoin ⟨⟨c, hc⟩, rfl⟩⟩
  have hwreg : IsRegular ((X : R[X]) ^ c) := (monic_X_pow c).isRegular
  have hwpoly : (X : R[X]) ^ c ∈ (R[X])⁰ :=
    ⟨fun q hq => hwreg.1 (by simpa using hq),
      fun q hq => hwreg.2 (by simpa using hq)⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · exact mem_nonZeroDivisors_of_injective (f := (A).val) Subtype.val_injective hwpoly
  · exact mem_nonZeroDivisors_of_injective (f := (B).val) Subtype.val_injective hwpoly
  · intro b
    exact ⟨⟨X ^ c * (b : R[X]), hclear (b : R[X]) b.property⟩, Subtype.ext rfl⟩

/-- The inclusion into the gcd monomial subalgebra preserves regular
 denominators, without a coefficient-domain hypothesis. -/
theorem inclusion_mem_nonZeroDivisors_adjoin_X_pow_setGcd
    (a : A) (ha : a ∈ A⁰) : j a ∈ B⁰ := by
  obtain ⟨w, hw, hjw, hclear⟩ := exists_regular_clearing_adjoin_X_pow_setGcd (R := R) S
  have hj : Function.Injective (j : A → B) :=
    adjoin_X_pow_setGcd_inclusion_injective (R := R) S
  have hcancel : ∀ b : B, j a * b = 0 → b = 0 := by
    intro b hab
    obtain ⟨c, hc⟩ := hclear b
    have hac : a * c = 0 := by
      apply hj
      rw [map_mul, map_zero, hc]
      calc
        j a * (j w * b) = j w * (j a * b) := by ac_rfl
        _ = 0 := by rw [hab, mul_zero]
    have hc0 : c = 0 := ha.1 c hac
    apply hjw.1 b
    rw [← hc, hc0, map_zero]
  exact ⟨hcancel, fun b hab => hcancel b (by simpa [mul_comm] using hab)⟩

/-- A single regular element clears a numerator and a regular denominator
 simultaneously; the cleared denominator remains regular. -/
theorem exists_regular_common_denominator_adjoin_X_pow_setGcd (b : B) (v : B⁰) :
    ∃ w : A⁰, j (w : A) ∈ B⁰ ∧ ∃ a c : A,
      j a = j (w : A) * b ∧ j c = j (w : A) * (v : B) ∧ c ∈ A⁰ := by
  obtain ⟨w, hw, hjw, hclear⟩ := exists_regular_clearing_adjoin_X_pow_setGcd (R := R) S
  obtain ⟨a, ha⟩ := hclear b
  obtain ⟨c, hc⟩ := hclear v
  refine ⟨⟨w, hw⟩, hjw, a, c, ha, hc, ?_⟩
  apply mem_nonZeroDivisors_of_injective (f := j)
    (adjoin_X_pow_setGcd_inclusion_injective (R := R) S)
  rw [hc]
  exact (nonZeroDivisors B).mul_mem hjw v.property

local notation "QA" => FractionRing A
local notation "QB" => FractionRing B

local instance : IsScalarTower R A QA :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance : IsScalarTower R B QB :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The action induced by the gcd inclusion and localization of its target. -/
instance instAlgebraAdjoinXPowSetGcdFractionRing : Algebra A QB :=
  ((algebraMap B QB).comp (j).toRingHom).toAlgebra

/-- The induced action agrees with the coefficient action on the total quotient ring. -/
instance instIsScalarTowerAdjoinXPowSetGcdFractionRing : IsScalarTower R A QB :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The structure map is the composite of the existing inclusion and localization. -/
theorem algebraMap_adjoin_X_pow_setGcd_fractionRing (a : A) :
    algebraMap A QB a = algebraMap B QB (j a) := rfl

/-- The source total quotient ring has the coefficient map through its original subalgebra. -/
theorem algebraMap_coeff_adjoin_X_pow_fractionRing (r : R) :
    algebraMap R QA r = algebraMap A QA (algebraMap R A r) := rfl

/-- The target total quotient ring has the coefficient map through its original subalgebra. -/
theorem algebraMap_coeff_adjoin_X_pow_setGcd_fractionRing (r : R) :
    algebraMap R QB r = algebraMap B QB (algebraMap R B r) := rfl

/-- The inclusion-composite action has the same coefficient map as the target action.
The coefficient square through the original subalgebras is
`algebraMap_adjoin_X_pow_setGcd_coeff`. -/
theorem algebraMap_coeff_adjoin_X_pow_setGcd_fractionRing_via_source (r : R) :
    algebraMap R QB r = algebraMap A QB (algebraMap R A r) := rfl

/-- The inclusion-induced action on the total quotient ring is multiplication
by the image of the included polynomial. -/
theorem smul_adjoin_X_pow_setGcd_fractionRing (a : A) (z : QB) :
    a • z = algebraMap B QB (j a) * z := by
  rw [Algebra.smul_def, algebraMap_adjoin_X_pow_setGcd_fractionRing]

/-- The total quotient ring of the gcd monomial subalgebra is also the total
quotient ring of the exponent subalgebra, for the inclusion-composite action. -/
instance isFractionRing_adjoin_X_pow_setGcd : IsFractionRing A QB := by
  have hB := (isLocalization_iff B⁰ QB).mp (inferInstance : IsLocalization B⁰ QB)
  refine (isLocalization_iff A⁰ QB).mpr ⟨?_, ?_, ?_⟩
  · intro a
    change IsUnit (algebraMap B QB (j (a : A)))
    exact hB.1 ⟨j (a : A),
      inclusion_mem_nonZeroDivisors_adjoin_X_pow_setGcd (R := R) S a a.property⟩
  · intro z
    obtain ⟨⟨b, v⟩, hz⟩ := hB.2.1 z
    obtain ⟨w, _, a, c, ha, hc, hcreg⟩ :=
      exists_regular_common_denominator_adjoin_X_pow_setGcd (R := R) S b v
    refine ⟨(a, ⟨c, hcreg⟩), ?_⟩
    change z * algebraMap B QB (j c) = algebraMap B QB (j a)
    rw [hc, map_mul]
    calc
      z * (algebraMap B QB (j (w : A)) * algebraMap B QB (v : B)) =
          algebraMap B QB (j (w : A)) * (z * algebraMap B QB (v : B)) := by ac_rfl
      _ = algebraMap B QB (j (w : A)) * algebraMap B QB b := by rw [hz]
      _ = algebraMap B QB (j a) := by rw [ha, map_mul]
  · intro a b hab
    have habB : j a = j b := (IsFractionRing.injective B QB) hab
    have habA : a = b := adjoin_X_pow_setGcd_inclusion_injective (R := R) S habB
    exact ⟨1, by rw [habA]⟩

/-- The canonical coefficient-algebra equivalence between the total quotient
rings of an exponent subalgebra and its gcd monomial subalgebra. -/
def fractionRingEquivAdjoinXPowSetGcd : QA ≃ₐ[R] QB :=
  (IsLocalization.algEquiv A⁰ QA QB).restrictScalars R

/-- The canonical equivalence extends the same polynomial inclusion. -/
@[simp]
theorem fractionRingEquivAdjoinXPowSetGcd_algebraMap (a : A) :
    fractionRingEquivAdjoinXPowSetGcd (R := R) S (algebraMap A QA a) =
      algebraMap B QB (j a) := by
  change (IsLocalization.algEquiv A⁰ QA QB) (algebraMap A QA a) = algebraMap A QB a
  exact (IsLocalization.algEquiv A⁰ QA QB).commutes a

/-- The inclusion square fixes coefficients, with both coefficient maps
factoring through their original polynomial subalgebras. -/
theorem fractionRingEquivAdjoinXPowSetGcd_coeff (r : R) :
    fractionRingEquivAdjoinXPowSetGcd (R := R) S
        (algebraMap A QA (algebraMap R A r)) =
      algebraMap B QB (algebraMap R B r) := by
  rw [fractionRingEquivAdjoinXPowSetGcd_algebraMap]
  rfl

/-- A regular fraction is sent to the fraction of the included numerator
and denominator; no coefficient-domain assumption is used. -/
@[simp]
theorem fractionRingEquivAdjoinXPowSetGcd_mk' (a : A) (s : A⁰) :
    fractionRingEquivAdjoinXPowSetGcd (R := R) S (IsLocalization.mk' QA a s) =
      IsLocalization.mk' QB (j a)
        ⟨j (s : A),
          inclusion_mem_nonZeroDivisors_adjoin_X_pow_setGcd (R := R) S s s.property⟩ := by
  let v : B⁰ := ⟨j (s : A),
    inclusion_mem_nonZeroDivisors_adjoin_X_pow_setGcd (R := R) S s s.property⟩
  change fractionRingEquivAdjoinXPowSetGcd (R := R) S (IsLocalization.mk' QA a s) =
    IsLocalization.mk' QB (j a) v
  have hleft :
      fractionRingEquivAdjoinXPowSetGcd (R := R) S (IsLocalization.mk' QA a s) *
          algebraMap B QB (v : B) = algebraMap B QB (j a) := by
    have h := congrArg (fractionRingEquivAdjoinXPowSetGcd (R := R) S)
      (IsLocalization.mk'_spec QA a s)
    simpa only [map_mul, fractionRingEquivAdjoinXPowSetGcd_algebraMap] using h
  have hB := (isLocalization_iff B⁰ QB).mp (inferInstance : IsLocalization B⁰ QB)
  obtain ⟨u, hu⟩ := hB.1 v
  have hmul :
      fractionRingEquivAdjoinXPowSetGcd (R := R) S (IsLocalization.mk' QA a s) * (u : QB) =
        IsLocalization.mk' QB (j a) v * (u : QB) := by
    rw [hu]
    exact hleft.trans (IsLocalization.mk'_spec QB (j a) v).symm
  have hcancel := congrArg (fun z : QB => z * ↑(u⁻¹)) hmul
  simpa [mul_assoc] using hcancel

/-- Over domain coefficients, the equivalence agrees with the fraction-field map
for every proof of the same inclusion. In particular it is the map in
`exists_bijective_fractionRingMap_adjoin_X_pow_setGcd`. -/
theorem fractionRingEquivAdjoinXPowSetGcd_toRingHom [IsDomain R] (h : A ≤ B) :
    (fractionRingEquivAdjoinXPowSetGcd (R := R) S).toRingEquiv.toRingHom =
      IsFractionRing.map (K := QA) (L := QB)
        («j» := (Subalgebra.inclusion h).toRingHom) (Subalgebra.inclusion_injective h) := by
  apply IsLocalization.ringHom_ext A⁰
  calc
    _ = (algebraMap B QB).comp (j).toRingHom := by
      ext a
      exact fractionRingEquivAdjoinXPowSetGcd_algebraMap (R := R) S a
    _ = _ := by
      simpa only [IsFractionRing.map] using
        (IsLocalization.map_comp (S := QA) (Q := QB) (g := (j).toRingHom)
          (show A⁰ ≤ (B⁰).comap (j).toRingHom from
            fun a ha => inclusion_mem_nonZeroDivisors_adjoin_X_pow_setGcd (R := R) S a ha)).symm

end Ring

end Polynomial
