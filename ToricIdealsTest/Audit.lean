/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ToricIdeals

/-!
# Audit examples

Named, stored clients of the toric-ideal boundary results and selected axiom prints.
-/

open ToricIdeals.RationalNormalCurve

universe w

variable (k : Type w) [CommRing k]

private theorem positive_kernel (n : ℕ) (hn : 1 ≤ n) :
    hankelIdeal k n = RingHom.ker (rncMap k n) :=
  hankelIdeal_eq_ker k n hn

private theorem one_kernel : hankelIdeal k 1 = RingHom.ker (rncMap k 1) :=
  hankelIdeal_one_eq_ker k

private theorem zero_strict [Nontrivial k] : hankelIdeal k 0 < RingHom.ker (rncMap k 0) :=
  hankelIdeal_zero_lt_ker k

private theorem zero_subsingleton [Subsingleton k] :
    hankelIdeal k 0 = RingHom.ker (rncMap k 0) :=
  Subsingleton.elim _ _

#print axioms ToricIdeals.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero
#print axioms ToricIdeals.RationalNormalCurve.hankelIdeal_zero_lt_ker
#print axioms ToricIdeals.RationalNormalCurve.hankelIdeal_one_eq_ker
#print axioms ToricIdeals.RationalNormalCurve.exists_normal
#print axioms ToricIdeals.RationalNormalCurve.rncExponent_injective_on_normal
#print axioms ToricIdeals.RationalNormalCurve.hankelIdeal_eq_ker
#print axioms ToricIdeals.RationalNormalCurve.quotientEquivRange
#print axioms ToricIdeals.RationalNormalCurve.hankelIdeal_isPrime
#print axioms ToricIdeals.RationalNormalCurve.quotient_isDomain
#print axioms ToricIdeals.RationalNormalCurve.spectrum_irreducible
