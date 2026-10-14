/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals

/-!
# Clients of the rational-normal-curve flatness criterion

The forward and reverse directions of `rncMap_flat_iff` apply to the full
polynomial source and target through the parametrization. Zero coefficients
give flat ring maps in every degree. In contrast, the conic map over `ZMod 4`
is not flat, even though degree one is flat over this same ring with a
nonzero square-zero coefficient.

These examples use `RingHom.Flat` directly, so the source action is the one
induced by the ring homomorphism, not an evaluation action on coefficients.
-/

@[expose] public section

open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.FlatnessClient

noncomputable section

private theorem zero_coefficients_flat (n : ℕ) : (rncMap (ZMod 1) n).Flat :=
  (rncMap_flat_iff (ZMod 1) n).mpr (Or.inr inferInstance)

private theorem mod_four_flatness_boundary :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      (rncMap (ZMod 4) 1).Flat ∧ ¬ (rncMap (ZMod 4) 2).Flat := by
  refine ⟨by decide, by decide, (rncMap_flat_iff (ZMod 4) 1).mpr (Or.inl rfl), ?_⟩
  intro hflat
  rcases (rncMap_flat_iff (ZMod 4) 2).mp hflat with hdegree | hcoeff
  · exact (by decide : (2 : ℕ) ≠ 1) hdegree
  · exact (by decide : (2 : ZMod 4) ≠ 0) (@Subsingleton.elim _ hcoeff 2 0)

end

end ToricIdeals.RationalNormalCurve.FlatnessClient
