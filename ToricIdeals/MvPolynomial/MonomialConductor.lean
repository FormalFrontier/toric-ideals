/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MvPolynomial.MonomialFinite
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Monomial conductors and principal localization

A conductor for the relative difference-and-root exponents clears their entire
monomial algebra. Inverting the same coefficient-one conductor monomial therefore
identifies the original algebra and its relative-root extension. For normal domain
coefficients it also identifies the original algebra with its own normalization
after this localization. Coefficients and variables have independent universes.

The general localization comparison needs only a commutative semiring, including
the zero semiring. Finite generation supplies a conductor but is not needed once
a fixed conductor is given. Normalization is in the original algebra's own fraction
ring, not in the ambient polynomial fraction ring.

## References

The exponent conductor uses the finite remainder argument in
`ToricIdeals.AddSubmonoid.FiniteRemainder`. The whole-algebra clearing and
normalization comparisons reuse `MonomialFinite` and `MonomialNormalization`.
The localization maps and their universal properties are Mathlib's, due to
Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston and Anne Baanen;
algebra-equivalence promotion uses the API of Kenny Lau and Yury Kudryashov.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v}
variable (S : AddSubmonoid (σ →₀ ℕ))

local notation "P" => MvPolynomial σ R
local notation "A" => Algebra.adjoin R
  (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))
local notation "B" => Algebra.adjoin R
  (Set.range fun n : {n : σ →₀ ℕ //
    (∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S} =>
      monomial (n : σ →₀ ℕ) (1 : R))

section Semiring

variable [CommSemiring R]

variable (c : S)
local notation "xA" => (Subtype.mk (monomial (c : σ →₀ ℕ) (1 : R))
  (Algebra.subset_adjoin (Set.mem_range_self c)) : A)
local notation "xB" => algebraMap A B xA
local notation "LA" => Localization.Away xA
local notation "LB" => Localization.Away xB

variable (hc : ∀ n : σ →₀ ℕ,
  ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
  (c : σ →₀ ℕ) + n ∈ S)

/-- Inverting a fixed conductor monomial identifies the original monomial algebra
and its relative-root extension, through the canonical localized inclusion. -/
def adjoinMonomialLocalizationEquiv
    [Algebra A B] [IsScalarTower A B P] : LA ≃ₐ[A] LB := by
  let : IsLocalization.Away ((Algebra.ofId A B) xA) LB := by
    simpa only [Algebra.ofId_apply] using (inferInstance : IsLocalization.Away xB LB)
  refine AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ (R := A) LA LB (Algebra.ofId A B) xA) ⟨?_, ?_⟩
  · apply IsLocalization.Away.mapₐ_injective_of_injective
      (R := A) («A» := A) («B» := B) (Aₚ := LA) (Bₚ := LB) (f := Algebra.ofId A B) xA
    intro a b hab
    apply Subtype.ext
    simpa only [Algebra.ofId_apply, coe_algebraMap_adjoin_monomial_relative_root] using
      congrArg (fun z : B => (z : P)) hab
  · change Function.Surjective (Localization.awayMap (algebraMap A B) xA)
    apply Localization.awayMap_surjective_iff.mpr
    intro b
    refine ⟨⟨monomial (c : σ →₀ ℕ) 1 * (b : P),
      mul_mem_adjoin_monomial_of_relative_root_conductor S c hc b⟩, 1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subalgebra.coe_mul, coe_algebraMap_adjoin_monomial_relative_root]

/-- The forward homomorphism is the stock localized inclusion. -/
@[simp]
theorem adjoinMonomialLocalizationEquiv_toAlgHom
    [Algebra A B] [IsScalarTower A B P] :
    (adjoinMonomialLocalizationEquiv (R := R) S c hc).toAlgHom =
      Localization.awayMapₐ (Algebra.ofId A B) xA := rfl

/-- The localization comparison preserves the original-algebra base map. -/
theorem adjoinMonomialLocalizationEquiv_algebraMap
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    adjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap A LA a) =
      algebraMap B LB (algebraMap A B a) :=
  ((adjoinMonomialLocalizationEquiv (R := R) S c hc).commutes a).trans
    (IsScalarTower.algebraMap_apply A B LB a)

/-- The same conductor monomial is inverted on both sides. -/
@[simp]
theorem adjoinMonomialLocalizationEquiv_invSelf
    [Algebra A B] [IsScalarTower A B P] :
    adjoinMonomialLocalizationEquiv (R := R) S c hc (IsLocalization.Away.invSelf xA) =
      IsLocalization.Away.invSelf xB := by
  apply (IsLocalization.Away.algebraMap_isUnit xB).mul_right_inj.mp
  calc
    algebraMap B LB xB *
        adjoinMonomialLocalizationEquiv (R := R) S c hc (IsLocalization.Away.invSelf xA) =
      adjoinMonomialLocalizationEquiv (R := R) S c hc
        (algebraMap A LA xA * IsLocalization.Away.invSelf xA) := by
          rw [map_mul, adjoinMonomialLocalizationEquiv_algebraMap]
    _ = 1 :=
      (congrArg (adjoinMonomialLocalizationEquiv (R := R) S c hc)
        (IsLocalization.Away.mul_invSelf xA)).trans
          (map_one (adjoinMonomialLocalizationEquiv (R := R) S c hc))
    _ = algebraMap B LB xB * IsLocalization.Away.invSelf xB :=
      (IsLocalization.Away.mul_invSelf xB).symm

/-- Scalar multiplication is for the given original-algebra actions. -/
theorem adjoinMonomialLocalizationEquiv_smul
    [Algebra A B] [IsScalarTower A B P] (a : A) (z : LA) :
    adjoinMonomialLocalizationEquiv (R := R) S c hc (a • z) =
      a • adjoinMonomialLocalizationEquiv (R := R) S c hc z :=
  map_smul (adjoinMonomialLocalizationEquiv (R := R) S c hc) a z

/-- Coefficients are unchanged by the localization comparison. -/
@[simp]
theorem adjoinMonomialLocalizationEquiv_coefficient
    [Algebra A B] [IsScalarTower A B P] (r : R) :
    adjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap R LA r) = algebraMap R LB r := by
  let := isScalarTower_adjoin_monomial_relative_root (R := R) S
  rw [IsScalarTower.algebraMap_apply R A LA,
    adjoinMonomialLocalizationEquiv_algebraMap,
    ← IsScalarTower.algebraMap_apply R A B, ← IsScalarTower.algebraMap_apply R B LB]

/-- The comparison respects the coefficient action as well as the A-action. -/
theorem adjoinMonomialLocalizationEquiv_coefficient_smul
    [Algebra A B] [IsScalarTower A B P] (r : R) (z : LA) :
    adjoinMonomialLocalizationEquiv (R := R) S c hc (r • z) =
      r • adjoinMonomialLocalizationEquiv (R := R) S c hc z := by
  calc
    _ = adjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap R LA r * z) :=
      congrArg (adjoinMonomialLocalizationEquiv (R := R) S c hc) (Algebra.smul_def r z)
    _ = adjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap R LA r) *
        adjoinMonomialLocalizationEquiv (R := R) S c hc z := map_mul _ _ _
    _ = algebraMap R LB r * adjoinMonomialLocalizationEquiv (R := R) S c hc z :=
      congrArg (fun t : LB => t * adjoinMonomialLocalizationEquiv (R := R) S c hc z)
        (adjoinMonomialLocalizationEquiv_coefficient (R := R) S c hc r)
    _ = _ := (Algebra.smul_def r _).symm

/-- The localization universal property uniquely specifies the forward map. -/
theorem adjoinMonomialLocalizationEquiv_unique
    [Algebra A B] [IsScalarTower A B P] (f : LA →ₐ[A] LB) :
    f = (adjoinMonomialLocalizationEquiv (R := R) S c hc).toAlgHom :=
  IsLocalization.algHom_ext (Submonoid.powers xA) (Subsingleton.elim _ _)

/-- A clearing witness gives an explicit inverse image, independently of the
choice of witness; no coefficient cancellation is used. -/
theorem adjoinMonomialLocalizationEquiv_symm_algebraMap
    [Algebra A B] [IsScalarTower A B P] (b : B) (a : A)
    (ha : algebraMap A B a = xB * b) :
    (adjoinMonomialLocalizationEquiv (R := R) S c hc).symm (algebraMap B LB b) =
      algebraMap A LA a * IsLocalization.Away.invSelf xA := by
  apply (adjoinMonomialLocalizationEquiv (R := R) S c hc).injective
  rw [AlgEquiv.apply_symm_apply, map_mul,
    adjoinMonomialLocalizationEquiv_algebraMap, adjoinMonomialLocalizationEquiv_invSelf,
    ha, map_mul, mul_right_comm, IsLocalization.Away.mul_invSelf, one_mul]

/-- Finite generation supplies a conductor and its canonical principal
localization comparison, without a finiteness hypothesis on the variables. -/
theorem exists_adjoinMonomialLocalizationEquiv
    [Algebra A B] [IsScalarTower A B P] (hS : S.FG) :
    ∃ c : S,
      (∀ n : σ →₀ ℕ,
        ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
        (c : σ →₀ ℕ) + n ∈ S) ∧
      Nonempty
        (Localization.Away (⟨monomial (c : σ →₀ ℕ) (1 : R),
            Algebra.subset_adjoin ⟨c, rfl⟩⟩ : A) ≃ₐ[A]
          Localization.Away (algebraMap A B
            (⟨monomial (c : σ →₀ ℕ) (1 : R), Algebra.subset_adjoin ⟨c, rfl⟩⟩ : A))) := by
  obtain ⟨c, hc, hconductor⟩ := S.exists_relative_root_conductor hS
  exact ⟨⟨c, hc⟩, hconductor, ⟨adjoinMonomialLocalizationEquiv (R := R) S ⟨c, hc⟩ hconductor⟩⟩

end Semiring

section Normalization

variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable (c : S)

local notation "xA" => (Subtype.mk (monomial (c : σ →₀ ℕ) (1 : R))
  (Algebra.subset_adjoin (Set.mem_range_self c)) : A)
local notation "xB" => algebraMap A B xA
local notation "LA" => Localization.Away xA
local notation "LB" => Localization.Away xB
local notation "D" => integralClosure A (FractionRing A)
local notation "xD" => algebraMap A D xA
local notation "LD" => Localization.Away xD

/-- Localizing the own-normalization comparison at the same image monomial
retains its original-algebra structure. This transport needs no conductor. -/
def integralClosureAdjoinMonomialAwayEquiv
    [Algebra A B] [IsScalarTower A B P] : LD ≃ₐ[A] LB := by
  let e : D ≃ₐ[A] B := integralClosureAdjoinMonomialEquiv (R := R) S
  have hx : e.toAlgHom xD = xB := e.commutes xA
  let : IsLocalization.Away (e.toAlgHom xD) LB := by
    rw [hx]
    infer_instance
  exact AlgEquiv.ofBijective (IsLocalization.Away.mapₐ (R := A) LD LB e.toAlgHom xD)
    ⟨IsLocalization.Away.mapₐ_injective_of_injective
        (R := A) («A» := D) («B» := B) (Aₚ := LD) (Bₚ := LB)
        (f := e.toAlgHom) xD e.injective,
      IsLocalization.Away.mapₐ_surjective_of_surjective
        (R := A) («A» := D) («B» := B) (Aₚ := LD) (Bₚ := LB)
        (f := e.toAlgHom) xD e.surjective⟩

/-- The localized normalization comparison extends the extracted comparison. -/
theorem integralClosureAdjoinMonomialAwayEquiv_algebraMap
    [Algebra A B] [IsScalarTower A B P] (d : D) :
    integralClosureAdjoinMonomialAwayEquiv (R := R) S c (algebraMap D LD d) =
      algebraMap B LB (integralClosureAdjoinMonomialEquiv (R := R) S d) := by
  let e : D ≃ₐ[A] B := integralClosureAdjoinMonomialEquiv (R := R) S
  have hx : e.toAlgHom.toRingHom xD = xB := e.commutes xA
  let : IsLocalization.Away (e.toAlgHom.toRingHom xD) LB := by
    rw [hx]
    infer_instance
  have hmap : Submonoid.powers xD ≤
      (Submonoid.powers (e.toAlgHom.toRingHom xD)).comap e.toAlgHom.toRingHom := by
    rintro z ⟨k, rfl⟩
    exact ⟨k, (map_pow e.toAlgHom.toRingHom xD k).symm⟩
  change IsLocalization.Away.map LD LB e.toAlgHom.toRingHom xD
      (algebraMap D LD d) = algebraMap B LB (e.toAlgHom.toRingHom d)
  exact IsLocalization.map_eq (M := Submonoid.powers xD) (S := LD)
    (T := Submonoid.powers (e.toAlgHom.toRingHom xD)) (Q := LB)
    (g := e.toAlgHom.toRingHom) (hy := hmap) (x := d)

/-- The image of the original conductor monomial is the element inverted by
the localized normalization comparison. -/
theorem integralClosureAdjoinMonomialAwayEquiv_invSelf
    [Algebra A B] [IsScalarTower A B P] :
    integralClosureAdjoinMonomialAwayEquiv (R := R) S c (IsLocalization.Away.invSelf xD) =
      IsLocalization.Away.invSelf xB := by
  apply (IsLocalization.Away.algebraMap_isUnit xB).mul_right_inj.mp
  have hx := integralClosureAdjoinMonomialEquiv_algebraMap (R := R) S xA
  calc
    algebraMap B LB xB *
        integralClosureAdjoinMonomialAwayEquiv (R := R) S c (IsLocalization.Away.invSelf xD) =
      integralClosureAdjoinMonomialAwayEquiv (R := R) S c (algebraMap D LD xD) *
        integralClosureAdjoinMonomialAwayEquiv (R := R) S c
          (IsLocalization.Away.invSelf xD) :=
      congrArg (fun t : LB => t * integralClosureAdjoinMonomialAwayEquiv (R := R) S c
        (IsLocalization.Away.invSelf xD))
        ((integralClosureAdjoinMonomialAwayEquiv_algebraMap (R := R) S c xD).trans
          (congrArg (algebraMap B LB) hx)).symm
    _ = integralClosureAdjoinMonomialAwayEquiv (R := R) S c
        (algebraMap D LD xD * IsLocalization.Away.invSelf xD) := (map_mul _ _ _).symm
    _ = 1 :=
      (congrArg (integralClosureAdjoinMonomialAwayEquiv (R := R) S c)
        (IsLocalization.Away.mul_invSelf xD)).trans
          (map_one (integralClosureAdjoinMonomialAwayEquiv (R := R) S c))
    _ = algebraMap B LB xB * IsLocalization.Away.invSelf xB :=
      (IsLocalization.Away.mul_invSelf xB).symm

/-- The localized normalization comparison preserves coefficients. -/
theorem integralClosureAdjoinMonomialAwayEquiv_coefficient
    [Algebra A B] [IsScalarTower A B P] (r : R) :
    integralClosureAdjoinMonomialAwayEquiv (R := R) S c (algebraMap R LD r) =
      algebraMap R LB r := by
  let := isScalarTower_adjoin_monomial_relative_root (R := R) S
  calc
    _ = integralClosureAdjoinMonomialAwayEquiv (R := R) S c
        (algebraMap D LD (algebraMap R D r)) :=
      congrArg (integralClosureAdjoinMonomialAwayEquiv (R := R) S c)
        (IsScalarTower.algebraMap_apply R D LD r)
    _ = algebraMap B LB (integralClosureAdjoinMonomialEquiv (R := R) S
        (algebraMap R D r)) :=
      integralClosureAdjoinMonomialAwayEquiv_algebraMap (R := R) S c (algebraMap R D r)
    _ = algebraMap B LB (integralClosureAdjoinMonomialEquiv (R := R) S
        (algebraMap A D (algebraMap R A r))) :=
      congrArg (fun d : D => algebraMap B LB (integralClosureAdjoinMonomialEquiv (R := R) S d))
        (IsScalarTower.algebraMap_apply R A D r)
    _ = algebraMap B LB (algebraMap A B (algebraMap R A r)) :=
      congrArg (algebraMap B LB)
        (integralClosureAdjoinMonomialEquiv_algebraMap (R := R) S (algebraMap R A r))
    _ = algebraMap B LB (algebraMap R B r) :=
      congrArg (algebraMap B LB) (IsScalarTower.algebraMap_apply R A B r).symm
    _ = _ := (IsScalarTower.algebraMap_apply R B LB r).symm

/-- The localized normalization comparison respects coefficient multiplication. -/
theorem integralClosureAdjoinMonomialAwayEquiv_coefficient_smul
    [Algebra A B] [IsScalarTower A B P] (r : R) (z : LD) :
    integralClosureAdjoinMonomialAwayEquiv (R := R) S c (r • z) =
      r • integralClosureAdjoinMonomialAwayEquiv (R := R) S c z := by
  calc
    _ = integralClosureAdjoinMonomialAwayEquiv (R := R) S c (algebraMap R LD r * z) :=
      congrArg (integralClosureAdjoinMonomialAwayEquiv (R := R) S c) (Algebra.smul_def r z)
    _ = integralClosureAdjoinMonomialAwayEquiv (R := R) S c (algebraMap R LD r) *
        integralClosureAdjoinMonomialAwayEquiv (R := R) S c z := map_mul _ _ _
    _ = algebraMap R LB r * integralClosureAdjoinMonomialAwayEquiv (R := R) S c z :=
      congrArg (fun t : LB => t * integralClosureAdjoinMonomialAwayEquiv (R := R) S c z)
        (integralClosureAdjoinMonomialAwayEquiv_coefficient (R := R) S c r)
    _ = _ := (Algebra.smul_def r _).symm

variable (hc : ∀ n : σ →₀ ℕ,
  ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
  (c : σ →₀ ℕ) + n ∈ S)

/-- Localizing the original monomial algebra at a conductor monomial identifies
it canonically with its own-fraction normalization localized at the same image. -/
def integralClosureAdjoinMonomialLocalizationEquiv
    [Algebra A B] [IsScalarTower A B P] : LA ≃ₐ[A] LD :=
  (adjoinMonomialLocalizationEquiv (R := R) S c hc).trans
    (integralClosureAdjoinMonomialAwayEquiv (R := R) S c).symm

/-- The comparison triangle commutes for every localized element. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_square
    [Algebra A B] [IsScalarTower A B P] (z : LA) :
    integralClosureAdjoinMonomialAwayEquiv (R := R) S c
      (integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc z) =
      adjoinMonomialLocalizationEquiv (R := R) S c hc z :=
  (integralClosureAdjoinMonomialAwayEquiv (R := R) S c).apply_symm_apply _

/-- The own-normalization localization map is the canonical localized A-map. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_toAlgHom
    [Algebra A B] [IsScalarTower A B P] :
    (integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc).toAlgHom =
      Localization.awayMapₐ (Algebra.ofId A D) xA :=
  IsLocalization.algHom_ext (Submonoid.powers xA) (Subsingleton.elim _ _)

/-- The comparison preserves the given original-algebra base map. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_algebraMap
    [Algebra A B] [IsScalarTower A B P] (a : A) :
    integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap A LA a) =
      algebraMap D LD (algebraMap A D a) :=
  ((integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc).commutes a).trans
    (IsScalarTower.algebraMap_apply A D LD a)

/-- The normalization-side inverse is of the same image of the conductor. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_invSelf
    [Algebra A B] [IsScalarTower A B P] :
    integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc
      (IsLocalization.Away.invSelf xA) = IsLocalization.Away.invSelf xD := by
  apply (integralClosureAdjoinMonomialAwayEquiv (R := R) S c).injective
  exact ((integralClosureAdjoinMonomialLocalizationEquiv_square (R := R) S c hc
      (IsLocalization.Away.invSelf xA)).trans
    (adjoinMonomialLocalizationEquiv_invSelf (R := R) S c hc)).trans
      (integralClosureAdjoinMonomialAwayEquiv_invSelf (R := R) S c).symm

/-- The original-to-normalization comparison preserves coefficients. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_coefficient
    [Algebra A B] [IsScalarTower A B P] (r : R) :
    integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc (algebraMap R LA r) =
      algebraMap R LD r := by
  calc
    _ = integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc
        (algebraMap A LA (algebraMap R A r)) :=
      congrArg (integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc)
        (IsScalarTower.algebraMap_apply R A LA r)
    _ = algebraMap D LD (algebraMap A D (algebraMap R A r)) :=
      integralClosureAdjoinMonomialLocalizationEquiv_algebraMap (R := R) S c hc
        (algebraMap R A r)
    _ = algebraMap D LD (algebraMap R D r) :=
      congrArg (algebraMap D LD) (IsScalarTower.algebraMap_apply R A D r).symm
    _ = _ := (IsScalarTower.algebraMap_apply R D LD r).symm

/-- Both coefficient and original-algebra actions are retained by the comparison. -/
theorem integralClosureAdjoinMonomialLocalizationEquiv_coefficient_smul
    [Algebra A B] [IsScalarTower A B P] (r : R) (z : LA) :
    integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc (r • z) =
      r • integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc z := by
  calc
    _ = integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc
        (algebraMap R LA r * z) :=
      congrArg (integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc)
        (Algebra.smul_def r z)
    _ = integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc
        (algebraMap R LA r) *
        integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc z := map_mul _ _ _
    _ = algebraMap R LD r *
        integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc z :=
      congrArg (fun t : LD => t *
        integralClosureAdjoinMonomialLocalizationEquiv (R := R) S c hc z)
        (integralClosureAdjoinMonomialLocalizationEquiv_coefficient (R := R) S c hc r)
    _ = _ := (Algebra.smul_def r _).symm

/-- Finite generation also supplies the canonical principal-localization
comparison with the original algebra's own-fraction normalization. -/
theorem exists_integralClosureAdjoinMonomialLocalizationEquiv
    [Algebra A B] [IsScalarTower A B P] (hS : S.FG) :
    ∃ c : S,
      (∀ n : σ →₀ ℕ,
        ((∃ b, b ∈ S ∧ b + n ∈ S) ∧ ∃ k : ℕ, 0 < k ∧ k • n ∈ S) →
        (c : σ →₀ ℕ) + n ∈ S) ∧
      Nonempty
        (Localization.Away (⟨monomial (c : σ →₀ ℕ) (1 : R),
            Algebra.subset_adjoin ⟨c, rfl⟩⟩ : A) ≃ₐ[A]
          Localization.Away (algebraMap A D
            (⟨monomial (c : σ →₀ ℕ) (1 : R), Algebra.subset_adjoin ⟨c, rfl⟩⟩ : A))) := by
  obtain ⟨c, hc, hconductor⟩ := S.exists_relative_root_conductor hS
  exact ⟨⟨c, hc⟩, hconductor,
    ⟨integralClosureAdjoinMonomialLocalizationEquiv (R := R) S ⟨c, hc⟩ hconductor⟩⟩

end Normalization

end MvPolynomial
