/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.Artinian

/-!
# Coefficient-ring degeneration in kernel and Artinian criteria

Zero coefficients give equality in the degree-zero kernel comparison and
Artinian full Hankel quotients in every degree. Finite nonzero coefficients,
as in `ZMod 4`, do not give Artinian quotients.
-/

open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.CoefficientBoundaryModels

universe w

variable (k : Type w) [CommRing k]

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

end ToricIdeals.RationalNormalCurve.CoefficientBoundaryModels
