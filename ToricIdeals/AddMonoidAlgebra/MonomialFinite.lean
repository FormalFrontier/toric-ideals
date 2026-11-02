/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.AddMonoidAlgebra.MonomialSubalgebra
public import ToricIdeals.MonoidAlgebra.MonomialFinite

/-!
# Finite extensions of additive monomial algebras

The additive monomial adjoins are transported along
`AddMonoidAlgebra.toMultiplicativeAlgEquiv`. Their canonical inclusion modules
are finite precisely when the larger exponent submonoid has a finite cover by
left translates of the smaller one. Only the converse requires nontrivial
coefficients. Neither the additive monoid nor its submonoids need be commutative,
cancellative, or finitely generated.

## References

* Mathlib's monoid-algebra equivalences and supported modules, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison.
* Mathlib's subalgebra and adjoining API, by Kenny Lau and Yury Kudryashov.
-/

@[expose] public section

open scoped Pointwise

namespace AddMonoidAlgebra

universe u v

variable {R : Type u} {N : Type v} [CommSemiring R] [AddMonoid N]

private theorem moduleFinite_inclusion_congr
    {A : Type*} [Semiring A] [Algebra R A]
    {U V U' V' : Subalgebra R A} (hUV : U ≤ V) (hU'V' : U' ≤ V')
    (hU : U = U') (hV : V = V') :
    @Module.Finite U V _ _ (Subalgebra.inclusion hUV).toRingHom.toModule ↔
      @Module.Finite U' V' _ _ (Subalgebra.inclusion hU'V').toRingHom.toModule := by
  cases hU
  cases hV
  rfl

private theorem moduleFinite_inclusion_map_iff
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) {U V : Subalgebra R A} (hUV : U ≤ V) :
    @Module.Finite U V _ _ (Subalgebra.inclusion hUV).toRingHom.toModule ↔
      @Module.Finite (U.map e.toAlgHom) (V.map e.toAlgHom) _ _
        (Subalgebra.inclusion (Subalgebra.map_mono hUV)).toRingHom.toModule := by
  let := (Subalgebra.inclusion hUV).toRingHom.toModule
  let := (Subalgebra.inclusion (Subalgebra.map_mono (f := e.toAlgHom) hUV)).toRingHom.toModule
  let eU := e.subalgebraMap U
  let eV := e.subalgebraMap V
  let : RingHomSurjective eU.toRingEquiv.toRingHom := ⟨eU.surjective⟩
  let f : V →ₛₗ[eU.toRingEquiv.toRingHom] V.map e.toAlgHom :=
    { toFun := eV
      map_add' := eV.map_add
      map_smul' := by
        intro u v
        apply Subtype.ext
        change e ((u : A) * (v : A)) = e (u : A) * e (v : A)
        exact e.map_mul _ _ }
  exact f.finite_iff_of_bijective eV.bijective

private theorem moduleFinite_adjoin_single_iff_multiplicative
    {S T : AddSubmonoid N} (hST : S ≤ T) :
    @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : N) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : N) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_single_mono (R := R) hST)).toRingHom.toModule ↔
    @Module.Finite (MonoidAlgebra.monomialSubalgebra R S.toSubmonoid)
      (MonoidAlgebra.monomialSubalgebra R T.toSubmonoid) _ _
      (Subalgebra.inclusion
        (MonoidAlgebra.monomialSubalgebra_mono (R := R)
          (show S.toSubmonoid ≤ T.toSubmonoid from hST))).toRingHom.toModule := by
  refine (moduleFinite_inclusion_map_iff (toMultiplicativeAlgEquiv R R N)
    (adjoin_single_mono (R := R) hST)).trans ?_
  exact moduleFinite_inclusion_congr
    (Subalgebra.map_mono (f := (toMultiplicativeAlgEquiv R R N).toAlgHom)
      (adjoin_single_mono (R := R) hST))
    (MonoidAlgebra.monomialSubalgebra_mono (R := R)
      (show S.toSubmonoid ≤ T.toSubmonoid from hST))
    (map_adjoin_single_eq_monomialSubalgebra (R := R) S)
    (map_adjoin_single_eq_monomialSubalgebra (R := R) T)

/-- A finite cover by left additive translates gives a finite canonical
inclusion module between the corresponding monomial adjoins. This direction
also holds for the zero coefficient semiring. -/
theorem moduleFinite_adjoin_single_of_subset_add {S T : AddSubmonoid N} (hST : S ≤ T)
    {E : Set N} (hE : E.Finite) (hET : E ⊆ (T : Set N))
    (hcover : (T : Set N) ⊆ (S : Set N) + E) :
    @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : N) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : N) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_single_mono (R := R) hST)).toRingHom.toModule := by
  apply (moduleFinite_adjoin_single_iff_multiplicative hST).mpr
  apply MonoidAlgebra.moduleFinite_monomialSubalgebra_of_subset_mul
    (show S.toSubmonoid ≤ T.toSubmonoid from hST)
    (hE.image Multiplicative.ofAdd)
  · rintro _ ⟨n, hn, rfl⟩
    exact hET hn
  · intro n hn
    obtain ⟨s, hs, t, ht, hst⟩ := hcover hn
    exact ⟨Multiplicative.ofAdd s, hs, Multiplicative.ofAdd t, ⟨t, ht, rfl⟩,
      congrArg Multiplicative.ofAdd hst⟩

/-- Over nontrivial coefficients, finiteness of the canonical inclusion module
forces a finite cover of exponents by left additive translates. -/
theorem exists_finite_cover_of_moduleFinite_adjoin_single [Nontrivial R]
    {S T : AddSubmonoid N} (hST : S ≤ T)
    (hfinite : @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : N) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : N) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_single_mono (R := R) hST)).toRingHom.toModule) :
    ∃ E : Set N, E.Finite ∧ E ⊆ (T : Set N) ∧ (T : Set N) ⊆ (S : Set N) + E := by
  obtain ⟨E, hE, hET, hcover⟩ :=
    MonoidAlgebra.exists_finite_cover_of_moduleFinite_monomialSubalgebra
      (show S.toSubmonoid ≤ T.toSubmonoid from hST)
      ((moduleFinite_adjoin_single_iff_multiplicative hST).mp hfinite)
  refine ⟨Multiplicative.toAdd '' E, hE.image _, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact hET hn
  · intro n hn
    obtain ⟨s, hs, t, ht, hst⟩ := hcover (show Multiplicative.ofAdd n ∈ T.toSubmonoid from hn)
    exact ⟨Multiplicative.toAdd s, hs, Multiplicative.toAdd t, ⟨t, ht, rfl⟩,
      congrArg Multiplicative.toAdd hst⟩

/-- The canonical extension of additive monomial adjoins is module-finite if
and only if the exponent submonoid admits a finite left translate cover. -/
theorem moduleFinite_adjoin_single_iff [Nontrivial R] {S T : AddSubmonoid N} (hST : S ≤ T) :
    @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : N) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : N) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_single_mono (R := R) hST)).toRingHom.toModule ↔
    ∃ E : Set N, E.Finite ∧ E ⊆ (T : Set N) ∧ (T : Set N) ⊆ (S : Set N) + E := by
  constructor
  · exact exists_finite_cover_of_moduleFinite_adjoin_single hST
  · rintro ⟨E, hE, hET, hcover⟩
    exact moduleFinite_adjoin_single_of_subset_add hST hE hET hcover

end AddMonoidAlgebra
