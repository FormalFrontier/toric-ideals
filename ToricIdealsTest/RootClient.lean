/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals

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
