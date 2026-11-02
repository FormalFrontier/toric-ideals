/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.AddSubmonoid.FiniteRemainder
public import ToricIdeals.MvPolynomial.MonomialNormalization
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Module-finite relative root extensions of monomial subalgebras

A finitely generated exponent monoid has a module-finite relative root extension
with arbitrary commutative semiring coefficients. The action is the canonical
inclusion, as forced by its scalar tower with the ambient polynomial algebra.

The finite generators are coefficient-one monomials in a finite remainder set.
No finite-variable or Noetherian coefficient hypothesis is needed. Over an
integrally closed coefficient domain, the existing own-fraction normalization
image comparison upgrades to an algebra equivalence over the original monomial
subalgebra, so its own normalization is finite as well.

## References

This uses the coefficient-free finite remainder theorem, Mathlib's monomial API
by Johannes Hölzl, Johan Commelin and Mario Carneiro, the subalgebra/span API by
Kenny Lau and Yury Kudryashov, scalar towers by Kenny Lau and Anne Baanen, and
module finiteness by Johan Commelin and contributors.
The normalization consequence reuses `MonomialNormalization` and its canonical
fraction-ring lift, rather than a new integral-closure construction.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v}

private theorem relative_root_zero (S : AddSubmonoid (σ →₀ ℕ)) :
    (∃ b, b ∈ S ∧ b + 0 ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • (0 : σ →₀ ℕ) ∈ S := by
  exact ⟨⟨0, S.zero_mem, by simp⟩, 1, by decide, by simp⟩

private theorem relative_root_add (S : AddSubmonoid (σ →₀ ℕ))
    {n m : σ →₀ ℕ}
    (hn : (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S)
    (hm : (∃ b, b ∈ S ∧ b + m ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • m ∈ S) :
    (∃ b, b ∈ S ∧ b + (n + m) ∈ S) ∧
      ∃ k : ℕ, 0 < k ∧ k • (n + m) ∈ S := by
  obtain ⟨⟨b, hb, hbn⟩, k, hk, hkn⟩ := hn
  obtain ⟨⟨c, hc, hcm⟩, l, hl, hlm⟩ := hm
  refine ⟨⟨b + c, S.add_mem hb hc, ?_⟩, k * l, Nat.mul_pos hk hl, ?_⟩
  · convert S.add_mem hbn hcm using 1; ac_rfl
  · rw [nsmul_add]
    exact S.add_mem (by simpa [smul_smul, Nat.mul_comm] using S.nsmul_mem hkn l)
      (by simpa [smul_smul] using S.nsmul_mem hlm k)

section Semiring

variable [CommSemiring R] (S : AddSubmonoid (σ →₀ ℕ))

local notation "P" => MvPolynomial σ R
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
local notation "B" => Algebra.adjoin R
  (Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial (n : σ →₀ ℕ) (1 : R))

/-- The relative-root monomial adjoin of a finitely generated exponent monoid
is finite over its original monomial adjoin. The scalar tower with the ambient
polynomial algebra fixes the algebra map and action to canonical inclusion. -/
theorem moduleFinite_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] (hS : S.FG) : Module.Finite A B := by
  classical
  let G : Set P := Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial n.val (1 : R)
  have hGmul {p q : P} (hp : p ∈ G) (hq : q ∈ G) : p * q ∈ G := by
    obtain ⟨n, rfl⟩ := hp
    obtain ⟨m, rfl⟩ := hq
    exact ⟨⟨n.val + m.val, relative_root_add S n.property m.property⟩, by simp⟩
  have hG1 : (1 : P) ∈ G := ⟨⟨0, relative_root_zero S⟩, by simp⟩
  have hclosure : (Submonoid.closure G : Set P) ⊆ G := by
    intro p hp
    induction hp using Submonoid.closure_induction with
    | mem p hp => exact hp
    | one => exact hG1
    | mul p q _ _ hp hq => exact hGmul hp hq
  have hspan : (B).toSubmodule = Submodule.span R G :=
    Algebra.adjoin_eq_span_of_subset R fun _ hp => Submodule.subset_span (hclosure hp)
  obtain ⟨E, hE, hcover⟩ := S.exists_finset_relative_root_remainder hS
  let g : E → B := fun e =>
    ⟨monomial e.val 1, Algebra.subset_adjoin ⟨⟨e.val, hE e.val e.property⟩, rfl⟩⟩
  let F : Finset B := Finset.univ.image g
  let U : Submodule A B := Submodule.span A (F : Set B)
  have hcoe_smul (a : A) (b : B) :
      ((a • b : B) : P) = (a : P) * (b : P) := by
    change (IsScalarTower.toAlgHom A B P) (a • b) = _
    rw [map_smul, Algebra.smul_def]
    rfl
  have hmono (n : σ →₀ ℕ)
      (hn : (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) :
      (⟨monomial n 1, Algebra.subset_adjoin ⟨⟨n, hn⟩, rfl⟩⟩ : B) ∈ U := by
    obtain ⟨s, hs, e, he, hne⟩ := hcover n hn
    let a : A := ⟨monomial s 1, Algebra.subset_adjoin ⟨⟨s, hs⟩, rfl⟩⟩
    have hg : g ⟨e, he⟩ ∈ U := Submodule.subset_span
      (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩)
    have h := U.smul_mem a hg
    convert h using 1
    apply Subtype.ext
    rw [hcoe_smul]
    change monomial n 1 = monomial s 1 * monomial e 1
    simp [hne]
  have hU (p : P) (hp : p ∈ Submodule.span R G) :
      ∃ hpB : p ∈ B, (⟨p, hpB⟩ : B) ∈ U := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨n, rfl⟩ := hp
      exact ⟨Algebra.subset_adjoin ⟨n, rfl⟩, hmono n.val n.property⟩
    | zero => exact ⟨(B).zero_mem, U.zero_mem⟩
    | add p q _ _ hp hq =>
      obtain ⟨hpB, hpU⟩ := hp
      obtain ⟨hqB, hqU⟩ := hq
      exact ⟨(B).add_mem hpB hqB, U.add_mem hpU hqU⟩
    | smul c p _ hp =>
      obtain ⟨hpB, hpU⟩ := hp
      refine ⟨(B).smul_mem hpB c, ?_⟩
      have h := U.smul_mem (algebraMap R A c) hpU
      convert h using 1
      apply Subtype.ext
      rw [hcoe_smul]
      exact Algebra.smul_def c p
  have htop : U = ⊤ := by
    apply top_unique
    intro b _
    have hb : (b : P) ∈ Submodule.span R G := by
      rw [← hspan]
      exact b.property
    obtain ⟨_, h⟩ := hU b.val hb
    exact h
  exact Module.Finite.of_fg_top ⟨F, htop⟩

end Semiring

section Ring

variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- The normalization of a finitely generated monomial subalgebra in its own
fraction field is finite over that subalgebra, for an integrally closed domain
of coefficients. The action is the stock algebra action on integral closure. -/
theorem moduleFinite_integralClosure_adjoin_monomial
    (S : AddSubmonoid (σ →₀ ℕ)) (hS : S.FG) :
    let A := Algebra.adjoin R
      (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
    Module.Finite A (integralClosure A (FractionRing A)) := by
  classical
  let P := MvPolynomial σ R
  let A := Algebra.adjoin R
    (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
  let B := Algebra.adjoin R
    (Set.range fun n : {n : σ →₀ ℕ //
      (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
        monomial n.val (1 : R))
  let FA := FractionRing A
  let FP := FractionRing P
  let D := integralClosure A FA
  change Module.Finite A D
  have hAB : A ≤ B := by
    apply Algebra.adjoin_le
    rintro _ ⟨s, rfl⟩
    apply Algebra.subset_adjoin
    refine ⟨⟨s.val, ⟨⟨0, S.zero_mem, ?_⟩, 1, by decide, ?_⟩⟩, rfl⟩
    · simpa only [zero_add] using s.property
    · simpa only [one_nsmul] using s.property
  let : Algebra A B := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  have : IsScalarTower A B P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite A B := moduleFinite_adjoin_monomial_relative_root S hS
  let ιP := IsScalarTower.toAlgHom R P FP
  let θ := IsFractionRing.liftAlgHom (K := FA) (g := ιP.comp A.val)
    ((IsFractionRing.injective P FP).comp Subtype.val_injective)
  have hι : Function.Injective ιP := IsFractionRing.injective P FP
  have himage : (D.restrictScalars R).map θ = B.map ιP :=
    map_integralClosure_adjoin_monomial S
  let eD := Subalgebra.equivMapOfInjective (D.restrictScalars R) θ θ.injective
  let eEq := Subalgebra.equivOfEq _ _ himage
  let eB := Subalgebra.equivMapOfInjective B ιP hι
  let eR := (eD.trans eEq).trans eB.symm
  have heR (x : D) : ιP ((eR x : B) : P) = θ (x : FA) := by
    change ιP ((eB.symm (eEq (eD x)) : B) : P) = θ (x : FA)
    calc
      _ = ((eB (eB.symm (eEq (eD x)))) : FP) := rfl
      _ = (eEq (eD x) : FP) := congrArg Subtype.val (eB.apply_symm_apply _)
      _ = θ (x : FA) := rfl
  have hθ (a : A) : θ (algebraMap A FA a) = ιP (a : P) := by
    exact (IsFractionRing.liftAlgHom_apply (R := R) (A := A) (K := FA)
      (g := ιP.comp A.val)
      ((IsFractionRing.injective P FP).comp Subtype.val_injective)
      (algebraMap A FA a)).trans
        (IsFractionRing.lift_algebraMap (A := A) (K := FA)
          (g := (ιP.comp A.val).toRingHom)
          ((IsFractionRing.injective P FP).comp Subtype.val_injective) a)
  let eRing : D ≃+* B := eR.toRingEquiv
  have hsquare (a : A) :
      eRing (algebraMap A D a) = algebraMap A B a := by
    apply Subtype.ext
    apply hι
    exact (heR (algebraMap A D a)).trans (hθ a)
  let eA : D ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := eRing) hsquare
  exact Module.Finite.equiv eA.symm.toLinearEquiv

end Ring

end MvPolynomial
