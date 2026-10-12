/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
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

/-- The criterion gives Artinian quotients over the zero coefficient ring. -/
private theorem zero_coefficients_quotient_artinian (n : ℕ) :
    IsArtinianRing (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
  (quotient_isArtinianRing_iff (ZMod 1) n).mpr inferInstance

/-- Finite nonreduced coefficients do not make a Hankel quotient Artinian. -/
private theorem mod_four_quotient_not_artinian (n : ℕ) :
    ¬ IsArtinianRing (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  intro hArt
  have hR := (quotient_isArtinianRing_iff (ZMod 4) n).mp hArt
  exact htwo (@Subsingleton.elim (ZMod 4) hR 2 0)

#print axioms ToricIdeals.RationalNormalCurve.quotient_isArtinianRing_iff
#print axioms zero_coefficients_quotient_artinian
#print axioms mod_four_quotient_not_artinian
