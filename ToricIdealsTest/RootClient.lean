/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals
import Mathlib.Data.ZMod.Basic

/-!
# Root-import clients

Stored private checks of the public monomial-map and rational-normal-curve APIs
through an ordinary import of `ToricIdeals`.
-/

open ToricIdeals.RationalNormalCurve

universe u v w

private theorem generic_fiber_normalization
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommMonoid M] [AddCommMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      AddMonoidAlgebra.single m r -
        AddMonoidAlgebra.single (normal (exponentMap m)) r ∈ I)
    {f : AddMonoidAlgebra R M}
    (hf : AddMonoidAlgebra.mapDomain exponentMap f = 0) : f ∈ I :=
  ToricIdeals.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero
    I exponentMap normal basis_sub_normal_mem hf

variable (k : Type u) [CommRing k]

private theorem degree_zero_strict [Nontrivial k] :
    hankelIdeal k 0 < RingHom.ker (rncMap k 0) :=
  hankelIdeal_zero_lt_ker k

private theorem degree_zero_subsingleton [Subsingleton k] :
    hankelIdeal k 0 = RingHom.ker (rncMap k 0) :=
  Subsingleton.elim _ _

private theorem degree_one_kernel :
    hankelIdeal k 1 = RingHom.ker (rncMap k 1) :=
  hankelIdeal_one_eq_ker k

private theorem degree_two_kernel :
    hankelIdeal k 2 = RingHom.ker (rncMap k 2) :=
  hankelIdeal_eq_ker k 2 (by decide)

private theorem exposed_coordinate (index : Fin 2) :
    coordinateExponent 1 index =
      Finsupp.single (0 : Fin 2) (1 - index.val) +
        Finsupp.single (1 : Fin 2) index.val :=
  rfl

private theorem exposed_monomial_map (n : ℕ) :
    rncMap k n = AddMonoidAlgebra.mapDomainRingHom k (rncExponent n) :=
  rfl

private theorem coefficient_embedding_injective (n : ℕ) :
    Function.Injective (fun r : k ↦ rncMap k n (MvPolynomial.C r)) := by
  intro r s h
  apply MvPolynomial.C_injective (Fin 2) k
  simpa only [rncMap_C] using h

private theorem quotient_range_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (quotientEquivRange k n hn) :=
  (quotientEquivRange k n hn).surjective

private theorem quotient_range_evaluation (n : ℕ) (hn : 1 ≤ n) :
    quotientEquivRange k n hn (1 : Source k n ⧸ hankelIdeal k n) = 1 :=
  map_one (quotientEquivRange k n hn)

private theorem degree_two_prime [IsDomain k] :
    (hankelIdeal k 2).IsPrime :=
  hankelIdeal_isPrime k 2 (by decide)

private theorem degree_two_domain [IsDomain k] :
    IsDomain (Source k 2 ⧸ hankelIdeal k 2) :=
  quotient_isDomain k 2 (by decide)

private theorem degree_two_spectrum [IsDomain k] :
    IrreducibleSpace (PrimeSpectrum (Source k 2 ⧸ hankelIdeal k 2)) :=
  spectrum_irreducible k 2 (by decide)

/-! Closed coefficient-change clients use the existing quotient map directly,
without introducing a coordinate-ring alias or a specialized public map. -/

private theorem residue_four_not_injective :
    ¬ Function.Injective (Int.castRingHom (ZMod 4)) := by
  intro hinj
  exact (by decide : (4 : ℤ) ≠ 0) (hinj (by decide))

private theorem coefficient_minor_mod_four :
    MvPolynomial.map (Int.castRingHom (ZMod 4))
        (hankelMinor ℤ 2 ⟨(0, 1), by decide⟩) =
      MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) -
        MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (1 : Fin 3) := by
  rw [map_hankelMinor]
  rfl

private theorem coefficient_quotient_mod_four_relation :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 2).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 2)
          (hankelMinor ℤ 2 ⟨(0, 1), by decide⟩)) = 0 := by
  rw [Ideal.quotientMap_mk, map_hankelMinor]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (minor_mem (ZMod 4) 2 ⟨(0, 1), by decide⟩)

private theorem coefficient_quotient_mod_four_constant :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 2).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 2) (MvPolynomial.C (4 : ℤ))) = 0 := by
  have hfour : (Int.castRingHom (ZMod 4)) (4 : ℤ) = 0 := by decide
  rw [Ideal.quotientMap_mk, MvPolynomial.map_C, hfour]
  simp

private theorem coefficient_ideal_mod_four_degree_zero :
    Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (hankelIdeal ℤ 0) = ⊥ := by
  rw [map_hankelIdeal, hankelIdeal_zero]

private theorem coefficient_quotient_mod_four_degree_zero_variable :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 0)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 0).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1))) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (MvPolynomial.X (0 : Fin 1)) := by
  simp

private theorem integer_degree_zero_kernel_boundary :
    hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) :=
  hankelIdeal_zero_lt_ker ℤ

private theorem integer_degree_zero_constants_distinct :
    rncMap ℤ 0 (MvPolynomial.C (4 : ℤ)) ≠
      rncMap ℤ 0 (MvPolynomial.C (0 : ℤ)) := by
  intro h
  exact (by decide : (4 : ℤ) ≠ 0) (coefficient_embedding_injective ℤ 0 h)

private theorem integer_degree_two_constant :
    rncMap ℤ 2 (MvPolynomial.C (-3 : ℤ)) = MvPolynomial.C (-3 : ℤ) :=
  rncMap_C ℤ 2 (-3)

private theorem product_degree_two_constant :
    rncMap (ℤ × ℤ) 2 (MvPolynomial.C ((1, 0) : ℤ × ℤ)) =
      MvPolynomial.C ((1, 0) : ℤ × ℤ) :=
  rncMap_C (ℤ × ℤ) 2 (1, 0)
