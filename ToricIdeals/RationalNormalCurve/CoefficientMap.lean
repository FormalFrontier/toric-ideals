/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve
public import ToricIdeals.RationalNormalCurve.Augmentation

/-!
# Coefficient-map criteria for full Hankel quotients

Changing coefficients preserves the Hankel ideal. The induced stock quotient
map is injective, respectively surjective, exactly when the coefficient map is.
The statements concern the full quotients, for every `n`, including zero.

The injection criterion uses the positive-degree Hankel kernel theorem and
Mathlib's commutation of coefficient change with additive monoid algebra
exponent maps. At degree zero the Hankel ideal is bottom, so polynomial
coefficient injection applies directly. The converses use the coefficient
augmentation; surjectivity is induced by Mathlib's surjectivity theorems for
polynomial and ideal quotient maps.
-/

@[expose] public section

universe u v

namespace ToricIdeals.RationalNormalCurve

/-- Coefficient change on the full Hankel quotient reflects and preserves
injectivity, over arbitrary commutative rings and for every `n`. -/
theorem coefficient_quotientMap_injective_iff
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) :
    Function.Injective
      (Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
        ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)) ↔
      Function.Injective φ := by
  constructor
  · intro h r s hrs
    have hC : Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r) =
        Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C s) := by
      apply h
      simpa only [Ideal.quotientMap_mk, MvPolynomial.map_C] using
        congrArg (fun t => Ideal.Quotient.mk (hankelIdeal S n) (MvPolynomial.C t)) hrs
    simpa only [quotientAugmentation_mk, MvPolynomial.constantCoeff_C] using
      congrArg (quotientAugmentation R n) hC
  · intro hφ
    apply Ideal.quotientMap_injective'
    intro p hp
    change MvPolynomial.map φ p ∈ hankelIdeal S n at hp
    by_cases hn : n = 0
    · subst n
      rw [hankelIdeal_zero, Submodule.mem_bot] at hp ⊢
      exact MvPolynomial.map_injective φ hφ (by simpa only [map_zero] using hp)
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [hankelIdeal_eq_ker R n hn']
      apply RingHom.mem_ker.mpr
      apply MvPolynomial.map_injective φ hφ
      rw [map_zero]
      rw [hankelIdeal_eq_ker S n hn'] at hp
      have hcomm :
          (MvPolynomial.map φ : Target R →+* Target S).comp (rncMap R n) =
            (rncMap S n).comp (MvPolynomial.map φ) :=
        AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom φ (rncExponent n)
      exact (DFunLike.congr_fun hcomm p).trans (RingHom.mem_ker.mp hp)

/-- Coefficient change on the full Hankel quotient reflects and preserves
surjectivity, over arbitrary commutative rings and for every `n`. -/
theorem coefficient_quotientMap_surjective_iff
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) :
    Function.Surjective
      (Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
        ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)) ↔
      Function.Surjective φ := by
  constructor
  · intro h s
    obtain ⟨q, hq⟩ := h (Ideal.Quotient.mk (hankelIdeal S n) (MvPolynomial.C s))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    simpa only [Ideal.quotientMap_mk, quotientAugmentation_mk,
      MvPolynomial.constantCoeff_map, MvPolynomial.constantCoeff_C] using
      congrArg (quotientAugmentation S n) hq
  · intro hφ
    exact Ideal.quotientMap_surjective (MvPolynomial.map_surjective φ hφ)

end ToricIdeals.RationalNormalCurve
