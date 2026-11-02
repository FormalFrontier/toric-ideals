/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.MonomialSubalgebra
public import ToricIdeals.Submonoid.FiniteCover
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite extensions of monomial subalgebras

For submonoids `S ≤ T` of a monoid, a finite left translate cover `T ⊆ S * E`
with `E ⊆ T` makes the `T`-monomial subalgebra a finite module over the
`S`-monomial subalgebra. Over a nontrivial coefficient semiring, the converse
holds. The module structure is induced by the inclusion of subalgebras.

The proof uses the span/support characterization of monomial subalgebras and
Mathlib's finite-generation API. In the converse, the finite set of remainders
is the union of the coefficient supports of finitely many module generators.
Neither commutativity nor cancellation of the exponent monoid is needed for
this finite-cover criterion.

For a cancellative commutative exponent monoid, module finiteness also implies
that either the coefficient semiring is subsingleton or one positive exponent
sends every element of `T` into `S`. The module structure in this implication is
the left action induced by inclusion of the coefficient-one monomial adjoins.

## References

* Mathlib's finite-generation API, by Johan Commelin.
* Mathlib's monoid-algebra module and support API, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison.
-/

@[expose] public section

namespace MonoidAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [Monoid M]

open scoped Pointwise

-- The ambient inclusion is linear over any contained subalgebra for the
-- inclusion-induced module structure.
private def inclusionLinearMap {A : Type*} [Semiring A] [Algebra R A]
    {S T : Subalgebra R A} (hST : S ≤ T) :
    let _ : Module S T := (Subalgebra.inclusion hST).toRingHom.toModule
    T →ₗ[S] A := by
  let : Module S T := (Subalgebra.inclusion hST).toRingHom.toModule
  exact
    { toFun := fun p => p.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem mem_span_single_iff_support_subset_mul
    (S : Submonoid M) (E : Set M) (p : R[M]) :
    p ∈ Submodule.span (monomialSubalgebra R S) ((fun m => single m (1 : R)) '' E) ↔
      (↑p.coeff.support : Set M) ⊆ (S : Set M) * E := by
  change p ∈ (Submodule.span (monomialSubalgebra R S)
    ((fun m => single m (1 : R)) '' E)).restrictScalars R ↔ _
  rw [span_single_restrictScalars_monomialSubalgebra]
  exact mem_supported

/-- A finite left translate cover of `T` by `S` makes the inclusion of their
monomial subalgebras module-finite. The coefficient semiring may be trivial. -/
theorem moduleFinite_monomialSubalgebra_of_subset_mul
    {S T : Submonoid M} (hST : S ≤ T) {E : Set M} (hE : E.Finite)
    (hET : E ⊆ (T : Set M)) (hcover : (T : Set M) ⊆ (S : Set M) * E) :
    @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) := by
  let : Module (monomialSubalgebra R S) (monomialSubalgebra R T) :=
    (Subalgebra.inclusion (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule
  let f : monomialSubalgebra R T →ₗ[monomialSubalgebra R S] R[M] :=
    inclusionLinearMap (monomialSubalgebra_mono (R := R) hST)
  have hmulT : (S : Set M) * E ⊆ (T : Set M) := by
    rintro _ ⟨s, hs, e, he, rfl⟩
    exact T.mul_mem (hST hs) (hET he)
  have hrange : f.range = Submodule.span (monomialSubalgebra R S)
      ((fun m => single m (1 : R)) '' E) := by
    ext p
    change (∃ q : monomialSubalgebra R T, f q = p) ↔ _
    rw [mem_span_single_iff_support_subset_mul]
    constructor
    · rintro ⟨q, rfl⟩
      exact ((mem_monomialSubalgebra_iff T q.val).mp q.property).trans hcover
    · intro hp
      exact ⟨⟨p, (mem_monomialSubalgebra_iff T p).mpr (hp.trans hmulT)⟩, rfl⟩
  apply Module.Finite.of_fg_top
  apply Submodule.fg_of_fg_map_injective f Subtype.val_injective
  rw [Submodule.map_top, hrange]
  exact Submodule.fg_span (hE.image _)

/-- Over a nontrivial coefficient semiring, module finiteness of the inclusion
of monomial subalgebras gives a finite left translate cover of the exponent
submonoid. The remainders belong to the target submonoid. -/
theorem exists_finite_cover_of_moduleFinite_monomialSubalgebra [Nontrivial R]
    {S T : Submonoid M} (hST : S ≤ T)
    (hfinite : @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule)) :
    ∃ E : Set M, E.Finite ∧ E ⊆ (T : Set M) ∧
      (T : Set M) ⊆ (S : Set M) * E := by
  classical
  let : Module (monomialSubalgebra R S) (monomialSubalgebra R T) :=
    (Subalgebra.inclusion (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule
  let : Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) := hfinite
  let f : monomialSubalgebra R T →ₗ[monomialSubalgebra R S] R[M] :=
    inclusionLinearMap (monomialSubalgebra_mono (R := R) hST)
  obtain ⟨G, hG, hspanG⟩ := Submodule.fg_def.mp (Submodule.fg_range f)
  let E : Set M := ⋃ p ∈ G, (↑p.coeff.support : Set M)
  have hE : E.Finite := hG.biUnion fun p _ => p.coeff.support.finite_toSet
  have hET : E ⊆ (T : Set M) := by
    intro m hm
    obtain ⟨p, hp, hm⟩ := Set.mem_iUnion₂.mp hm
    have hpRange : p ∈ f.range := hspanG ▸ Submodule.subset_span hp
    obtain ⟨q, rfl⟩ := hpRange
    exact (mem_monomialSubalgebra_iff T q.val).mp q.property hm
  refine ⟨E, hE, hET, ?_⟩
  have hspanle : Submodule.span (monomialSubalgebra R S) G ≤
      Submodule.span (monomialSubalgebra R S) ((fun m => single m (1 : R)) '' E) := by
    apply Submodule.span_le.mpr
    intro p hp
    apply (mem_span_single_iff_support_subset_mul S E p).mpr
    intro m hm
    have hmE : m ∈ E := Set.mem_iUnion₂.mpr ⟨p, hp, hm⟩
    exact ⟨1, S.one_mem, m, hmE, one_mul m⟩
  intro t ht
  have htA : single t (1 : R) ∈ monomialSubalgebra R T :=
    (single_mem_monomialSubalgebra_iff T t 1).mpr (Or.inl ht)
  have htRange : single t (1 : R) ∈ f.range := ⟨⟨single t 1, htA⟩, rfl⟩
  have htspan : single t (1 : R) ∈ Submodule.span (monomialSubalgebra R S)
      ((fun m => single m (1 : R)) '' E) := hspanle (hspanG.symm ▸ htRange)
  apply (single_mem_span_single (R := R) (m := t) (s := (S : Set M) * E)).mp
  rw [← supported_eq_span_single]
  exact mem_supported.mpr ((mem_span_single_iff_support_subset_mul S E _).mp htspan)

/-- Over a nontrivial coefficient semiring, an inclusion of monomial
subalgebras is module-finite exactly when the target exponent submonoid has a
finite left translate cover by the source submonoid. -/
theorem moduleFinite_monomialSubalgebra_iff [Nontrivial R]
    {S T : Submonoid M} (hST : S ≤ T) :
    @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) ↔
    ∃ E : Set M, E.Finite ∧ E ⊆ (T : Set M) ∧
      (T : Set M) ⊆ (S : Set M) * E := by
  constructor
  · exact exists_finite_cover_of_moduleFinite_monomialSubalgebra hST
  · rintro ⟨E, hE, hET, hcover⟩
    exact moduleFinite_monomialSubalgebra_of_subset_mul hST hE hET hcover

/-- Finiteness of the left inclusion module between coefficient-one monomial
adjoins implies that either the coefficient semiring is subsingleton or one
positive exponent sends every target exponent into the source submonoid. -/
theorem subsingleton_or_exists_forall_pow_mem_of_moduleFinite_monomialSubalgebra
    {R : Type u} {M : Type v} [CommSemiring R] [CancelCommMonoid M]
    {S T : Submonoid M} (hST : S ≤ T)
    (hfinite : @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : M) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : M) (1 : R))) _ _
      (Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) :
    Subsingleton R ∨ ∃ n : ℕ, 0 < n ∧ ∀ t ∈ T, t ^ n ∈ S := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Or.inl hR
  · let : Nontrivial R := hR
    obtain ⟨E, hE, hET, hcover⟩ :=
      exists_finite_cover_of_moduleFinite_monomialSubalgebra hST hfinite
    refine Or.inr ⟨E.ncard.factorial, Nat.factorial_pos _, ?_⟩
    intro t ht
    exact Submonoid.pow_factorial_mem_of_finite_cover hE hET hcover ht

end MonoidAlgebra
