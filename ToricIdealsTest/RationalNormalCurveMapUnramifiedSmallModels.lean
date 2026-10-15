/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.ZMod.Basic
public import ToricIdeals.RationalNormalCurve.MapUnramified

/-!
# Small models for formal unramifiedness of the polynomial parametrization

Over `ℤ`, the degree-two parametrization is not formally unramified, whereas
the degree-one map is the identity and is formally unramified. The degree-zero
map is not formally unramified either: its source is the polynomial ring
`Source ℤ 0 = ℤ[X₀]` and its sole variable maps to `1` in the full bivariate
target. These are properties relative to the source polynomial ring through
`rncMap`, not relative to the coefficient ring.

The zero ring `ZMod 1` gives a formally unramified map in every degree.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

noncomputable section

/-- The quadratic parametrization over the integers is not formally unramified. -/
example : ¬ RingHom.FormallyUnramified (rncMap ℤ 2) := by
  intro h
  rcases (rncMap_formallyUnramified_iff ℤ 2).mp h with h | h
  · exact (by decide : (2 : ℕ) ≠ 1) h
  · exact not_subsingleton ℤ h

/-- The degree-one parametrization over the integers is formally unramified. -/
example : RingHom.FormallyUnramified (rncMap ℤ 1) := by
  exact (rncMap_formallyUnramified_iff ℤ 1).mpr (Or.inl rfl)

/-- The degree-zero parametrization over the integers is not formally unramified. -/
example : ¬ RingHom.FormallyUnramified (rncMap ℤ 0) := by
  intro h
  rcases (rncMap_formallyUnramified_iff ℤ 0).mp h with h | h
  · exact (by decide : (0 : ℕ) ≠ 1) h
  · exact not_subsingleton ℤ h

/-- Over the zero ring the parametrization is formally unramified in every degree. -/
example (n : ℕ) : RingHom.FormallyUnramified (rncMap (ZMod 1) n) := by
  exact (rncMap_formallyUnramified_iff (ZMod 1) n).mpr (Or.inr inferInstance)

end

end ToricIdeals.RationalNormalCurve
