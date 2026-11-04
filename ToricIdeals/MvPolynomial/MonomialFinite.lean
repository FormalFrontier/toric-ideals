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
subalgebra, so its own normalization is finite as well. This comparison is
available without finite generation. The generator-span description also proves
whole-algebra clearing by a fixed monomial conductor over commutative semirings.

## References

This uses the coefficient-free finite remainder theorem, Mathlib's monomial API
by Johannes Hölzl, Johan Commelin and Mario Carneiro, the subalgebra/span API by
Kenny Lau and Yury Kudryashov, scalar towers by Kenny Lau and Anne Baanen, and
module finiteness by Johan Commelin and contributors.
The normalization consequence reuses `MonomialNormalization` and its canonical
fraction-ring lift, rather than a new integral-closure construction.
-/

-- Keep the normalization implementation private; its computation lemmas are public.
public section

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

-- Keep the ambient subalgebras abstract in this coercion proof.
private theorem algebraMap_eq_inclusion_of_tower
    {K Q : Type*} [CommSemiring K] [CommSemiring Q] [Algebra K Q]
    (U V : Subalgebra K Q) [Algebra U V] [IsScalarTower U V Q]
    (hUV : U ≤ V) (a : U) : algebraMap U V a = Subalgebra.inclusion hUV a := by
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply U V Q a).symm

section Semiring

variable [CommSemiring R] (S : AddSubmonoid (σ →₀ ℕ))

local notation "P" => MvPolynomial σ R
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
local notation "B" => Algebra.adjoin R
  (Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial (n : σ →₀ ℕ) (1 : R))

/-- Every original monomial belongs to its relative-root extension. -/
theorem adjoin_monomial_le_adjoin_monomial_relative_root : A ≤ B := by
  apply Algebra.adjoin_le
  rintro _ ⟨s, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨⟨s.val, ⟨⟨0, S.zero_mem, ?_⟩, 1, by decide, ?_⟩⟩, rfl⟩
  · simpa only [zero_add] using s.property
  · simpa only [one_nsmul] using s.property

/-- The ambient scalar tower forces the original-algebra map to be inclusion. -/
@[simp]
theorem coe_algebraMap_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    ((algebraMap A B a : B) : P) = (a : P) :=
  (IsScalarTower.algebraMap_apply A B P a).symm

/-- The given original-algebra map agrees with the coefficient-algebra inclusion. -/
theorem algebraMap_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    algebraMap A B a =
      Subalgebra.inclusion
        (adjoin_monomial_le_adjoin_monomial_relative_root (R := R) S) a :=
  algebraMap_eq_inclusion_of_tower A B
    (adjoin_monomial_le_adjoin_monomial_relative_root (R := R) S) a

/-- The forced inclusion is compatible with the coefficient scalar tower. -/
theorem isScalarTower_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] : IsScalarTower R A B := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  apply Subtype.ext
  rw [coe_algebraMap_adjoin_monomial_relative_root]
  rfl

/-- The ambient scalar tower fixes scalar multiplication to polynomial multiplication. -/
@[simp]
theorem coe_smul_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] (a : A) (b : B) :
    ((a • b : B) : P) = (a : P) * (b : P) := by
  change (IsScalarTower.toAlgHom A B P) (a • b) = _
  rw [map_smul, Algebra.smul_def]
  rfl

/-- The relative-root monomial algebra is the coefficient span of its generating
monomials. This description works also for zero coefficients. -/
theorem adjoin_monomial_relative_root_toSubmodule :
    (B).toSubmodule = Submodule.span R
      (Set.range fun n : {n : σ →₀ ℕ //
        (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
          monomial n.val (1 : R)) := by
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
  exact Algebra.adjoin_eq_span_of_subset R fun _ hp =>
    Submodule.subset_span (hclosure hp)

/-- A fixed coefficient-one conductor monomial clears every polynomial in the
relative-root monomial algebra, with its original coefficients unchanged. -/
theorem mul_mem_adjoin_monomial_of_relative_root_conductor (c : S)
    (hc : ∀ n : σ →₀ ℕ,
      ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
      (c : σ →₀ ℕ) + n ∈ S) (p : B) :
    monomial (c : σ →₀ ℕ) (1 : R) * (p : P) ∈ A := by
  have hp : (p : P) ∈ Submodule.span R
      (Set.range fun n : {n : σ →₀ ℕ //
        (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
          monomial n.val (1 : R)) := by
    rw [← adjoin_monomial_relative_root_toSubmodule (R := R) S]
    exact p.property
  generalize (p : P) = q at hp ⊢
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n, rfl⟩ := hp
    simpa using (Algebra.subset_adjoin
      ⟨⟨(c : σ →₀ ℕ) + n.val, hc n.val n.property⟩, rfl⟩ :
        monomial ((c : σ →₀ ℕ) + n.val) (1 : R) ∈ A)
  | zero => simp
  | add p q _ _ hp hq => simpa only [mul_add] using (A).add_mem hp hq
  | smul r p _ hp =>
    simpa only [mul_smul_comm] using (A).smul_mem hp r

/-- The relative-root monomial adjoin of a finitely generated exponent monoid
is finite over its original monomial adjoin. The scalar tower with the ambient
polynomial algebra fixes the algebra map and action to canonical inclusion. -/
theorem moduleFinite_adjoin_monomial_relative_root
    [Algebra A B] [IsScalarTower A B P] (hS : S.FG) : Module.Finite A B := by
  classical
  let G : Set P := Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial n.val (1 : R)
  have hspan : (B).toSubmodule = Submodule.span R G :=
    adjoin_monomial_relative_root_toSubmodule S
  obtain ⟨E, hE, hcover⟩ := S.exists_finset_relative_root_remainder hS
  let g : E → B := fun e =>
    ⟨monomial e.val 1, Algebra.subset_adjoin ⟨⟨e.val, hE e.val e.property⟩, rfl⟩⟩
  let F : Finset B := Finset.univ.image g
  let U : Submodule A B := Submodule.span A (F : Set B)
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
    rw [coe_smul_adjoin_monomial_relative_root]
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
      rw [coe_smul_adjoin_monomial_relative_root]
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

variable (S : AddSubmonoid (σ →₀ ℕ))

local notation "P" => MvPolynomial σ R
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
local notation "B" => Algebra.adjoin R
  (Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial (n : σ →₀ ℕ) (1 : R))
local notation "FA" => FractionRing A
local notation "FP" => FractionRing P
local notation "D" => integralClosure A FA
local notation "ιP" => IsScalarTower.toAlgHom R P FP
local notation "θ" => IsFractionRing.liftAlgHom (K := FA)
  (g := AlgHom.comp ιP (Subalgebra.val A))
  (fun _ _ h => Subtype.val_injective (IsFractionRing.injective P FP h))

private noncomputable def normalizationComparison : D ≃ₐ[R] B := by
  let P' := MvPolynomial σ R
  let A' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
  let B' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun n : {n : σ →₀ ℕ //
      (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
        monomial n.val (1 : R))
  let FA' := FractionRing A'
  let FP' := FractionRing P'
  let D' := integralClosure A' FA'
  change D' ≃ₐ[R] B'
  let ιP' := IsScalarTower.toAlgHom R P' FP'
  let θ' := IsFractionRing.liftAlgHom (K := FA') (g := ιP'.comp A'.val)
    ((IsFractionRing.injective P' FP').comp Subtype.val_injective)
  have hι : Function.Injective ιP' := IsFractionRing.injective P' FP'
  have himage : (D'.restrictScalars R).map θ' = B'.map ιP' :=
    map_integralClosure_adjoin_monomial S
  let eD := Subalgebra.equivMapOfInjective (D'.restrictScalars R) θ' θ'.injective
  let eEq := Subalgebra.equivOfEq _ _ himage
  let eB := Subalgebra.equivMapOfInjective B' ιP' hι
  exact (eD.trans eEq).trans eB.symm

private theorem normalizationComparison_coe (d : D) :
    ιP ((normalizationComparison (R := R) S d : B) : P) = θ (d : FA) := by
  let P' := MvPolynomial σ R
  let A' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
  let B' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun n : {n : σ →₀ ℕ //
      (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
        monomial n.val (1 : R))
  let FA' := FractionRing A'
  let FP' := FractionRing P'
  let D' := integralClosure A' FA'
  let ιP' := IsScalarTower.toAlgHom R P' FP'
  let θ' := IsFractionRing.liftAlgHom (K := FA') (g := ιP'.comp A'.val)
    ((IsFractionRing.injective P' FP').comp Subtype.val_injective)
  have hι : Function.Injective ιP' := IsFractionRing.injective P' FP'
  have himage : (D'.restrictScalars R).map θ' = B'.map ιP' :=
    map_integralClosure_adjoin_monomial S
  let eD := Subalgebra.equivMapOfInjective (D'.restrictScalars R) θ' θ'.injective
  let eEq := Subalgebra.equivOfEq _ _ himage
  let eB := Subalgebra.equivMapOfInjective B' ιP' hι
  change ιP' ((eB.symm (eEq (eD d)) : B') : P') = θ' (d : FA')
  calc
    _ = ((eB (eB.symm (eEq (eD d)))) : FP') := rfl
    _ = (eEq (eD d) : FP') := congrArg Subtype.val (eB.apply_symm_apply _)
    _ = θ' (d : FA') := rfl

/-- The own-fraction normalization is the relative-root monomial algebra, as
an algebra over the original monomial algebra. The ambient scalar tower fixes
its action to inclusion. No finite-generation assumption is needed. -/
noncomputable def integralClosureAdjoinMonomialEquiv
    [Algebra A B] [IsScalarTower A B P] : D ≃ₐ[A] B := by
  apply AlgEquiv.ofRingEquiv (f := (normalizationComparison (R := R) S).toRingEquiv)
  intro a
  apply Subtype.ext
  apply IsFractionRing.injective P FP
  calc
    ιP ((normalizationComparison (R := R) S (algebraMap A D a) : B) : P) =
        θ (algebraMap A FA a) := normalizationComparison_coe (R := R) S _
    _ = ιP (a : P) := by
      exact (IsFractionRing.liftAlgHom_apply (R := R) (K := FA)
        (g := AlgHom.comp ιP (Subalgebra.val A))
        ((IsFractionRing.injective P FP).comp Subtype.val_injective)
        (algebraMap A FA a)).trans
          (IsFractionRing.lift_algebraMap (K := FA)
            (g := (AlgHom.comp ιP (Subalgebra.val A)).toRingHom)
            ((IsFractionRing.injective P FP).comp Subtype.val_injective) a)
    _ = ιP ((algebraMap A B a : B) : P) := by
      congr 1
      exact IsScalarTower.algebraMap_apply A B P a

/-- The normalization equivalence commutes with the canonical embedding into
the ambient polynomial fraction ring. -/
theorem integralClosureAdjoinMonomialEquiv_coe
    [Algebra A B] [IsScalarTower A B P] (d : D) :
    ιP ((integralClosureAdjoinMonomialEquiv (R := R) S d : B) : P) = θ (d : FA) :=
  normalizationComparison_coe (R := R) S d

/-- The normalization equivalence preserves the given original-algebra map. -/
theorem integralClosureAdjoinMonomialEquiv_algebraMap
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    integralClosureAdjoinMonomialEquiv (R := R) S (algebraMap A D a) = algebraMap A B a :=
  (integralClosureAdjoinMonomialEquiv (R := R) S).commutes a

/-- The inverse comparison also preserves the original-algebra base map. -/
theorem integralClosureAdjoinMonomialEquiv_symm_algebraMap
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    (integralClosureAdjoinMonomialEquiv (R := R) S).symm (algebraMap A B a) =
      algebraMap A D a :=
  (integralClosureAdjoinMonomialEquiv (R := R) S).symm.commutes a

/-- The inverse normalization comparison has the same canonical fraction square. -/
theorem integralClosureAdjoinMonomialEquiv_symm_coe
    [Algebra A B] [IsScalarTower A B P] (b : B) :
    θ (((integralClosureAdjoinMonomialEquiv (R := R) S).symm b : D) : FA) = ιP (b : P) := by
  calc
    _ = ιP ((integralClosureAdjoinMonomialEquiv (R := R) S
        ((integralClosureAdjoinMonomialEquiv (R := R) S).symm b) : B) : P) :=
      (integralClosureAdjoinMonomialEquiv_coe (R := R) S _).symm
    _ = ιP (b : P) :=
      congrArg (fun b' : B => ιP (b' : P))
        ((integralClosureAdjoinMonomialEquiv (R := R) S).apply_symm_apply b)

/-- The canonical ambient fraction square uniquely specifies the comparison. -/
theorem integralClosureAdjoinMonomialEquiv_unique
    [Algebra A B] [IsScalarTower A B P] (f : D →ₐ[A] B)
    (hf : ∀ d, ιP ((f d : B) : P) = θ (d : FA)) :
    f = (integralClosureAdjoinMonomialEquiv (R := R) S).toAlgHom := by
  apply AlgHom.ext
  intro d
  apply Subtype.ext
  apply IsFractionRing.injective P FP
  exact (hf d).trans (integralClosureAdjoinMonomialEquiv_coe (R := R) S d).symm

/-- The normalization of a finitely generated monomial subalgebra in its own
fraction field is finite over that subalgebra, for an integrally closed domain
of coefficients. The action is the stock algebra action on integral closure. -/
theorem moduleFinite_integralClosure_adjoin_monomial (hS : S.FG) :
    Module.Finite A D := by
  let P' := MvPolynomial σ R
  let A' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
  let B' : Subalgebra R P' := Algebra.adjoin R
    (Set.range fun n : {n : σ →₀ ℕ //
      (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
        monomial n.val (1 : R))
  let D' := integralClosure A' (FractionRing A')
  change Module.Finite A' D'
  let hAB : A' ≤ B' := adjoin_monomial_le_adjoin_monomial_relative_root (R := R) S
  let : Algebra A' B' := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let : IsScalarTower A' B' P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite A' B' := moduleFinite_adjoin_monomial_relative_root (R := R) S hS
  let e : D' ≃ₐ[A'] B' := integralClosureAdjoinMonomialEquiv (R := R) S
  exact Module.Finite.of_surjective e.symm.toAlgHom.toLinearMap e.symm.surjective

end Ring

end MvPolynomial
