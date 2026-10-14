/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals
import ToricIdealsTest.Audit.PolynomialCoefficientFinitenessModels
import ToricIdealsTest.Audit.RationalNormalCurveAugmentationKernel
import ToricIdealsTest.Audit.RationalNormalCurveCoefficientFaithfullyFlatClients
import ToricIdealsTest.Audit.RationalNormalCurveCoefficientFaithfullyFlatModels
import ToricIdealsTest.Audit.RationalNormalCurveCoefficientFinitenessClient
import ToricIdealsTest.Audit.RationalNormalCurveCoefficientFinitenessModels
import ToricIdealsTest.Audit.RationalNormalCurveFlatnessClient
import ToricIdealsTest.Audit.RationalNormalCurveFlatnessModels
import ToricIdealsTest.Audit.RationalNormalCurveFreenessClient
import ToricIdealsTest.Audit.RationalNormalCurveFreenessModels
import ToricIdealsTest.Audit.RationalNormalCurveHomogeneousBasisClients
import ToricIdealsTest.Audit.RationalNormalCurveHomogeneousQuotientModels
import ToricIdealsTest.Audit.RationalNormalCurveSurjectivityClient
import ToricIdealsTest.Audit.RationalNormalCurveSurjectivityModels

/-!
# Audit examples

Named, stored clients of the toric-ideal boundary results.
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
