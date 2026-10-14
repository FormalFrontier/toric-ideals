/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals

/-!
# Clients of raw rational-normal-curve surjectivity

The classifier supplies preimages for arbitrary bivariate polynomials over
`ZMod 1` in every degree. Its converse rules out full-target surjectivity in
degrees zero and two over the nonring coefficient semiring `ℕ`.

## References

* Formal Frontier Agents,
  `ToricIdeals.RationalNormalCurve.MapSurjectivity`, for the raw-map classifier.
* Mathlib contributors, `Mathlib.Data.ZMod.Basic`, for the zero coefficient ring.
-/

namespace ToricIdeals.RationalNormalCurve.SurjectivityClient

noncomputable section

/-- Every target polynomial has a source preimage over zero coefficients,
including degrees zero and two. -/
private theorem zero_coefficients_full_target_preimage (n : ℕ) (q : Target (ZMod 1)) :
    ∃ p : Source (ZMod 1) n, rncMap (ZMod 1) n p = q :=
  (rncMap_surjective_iff (ZMod 1) n).mpr (Or.inr inferInstance) q

/-- Neither the constant-image map nor the conic map reaches the full
bivariate target over the natural numbers. -/
private theorem nat_degree_zero_and_two_not_surjective :
    ¬ Function.Surjective (rncMap ℕ 0) ∧ ¬ Function.Surjective (rncMap ℕ 2) := by
  have hnot (n : ℕ) (hn : n ≠ 1) : ¬ Function.Surjective (rncMap ℕ n) := by
    intro hsurj
    rcases (rncMap_surjective_iff ℕ n).mp hsurj with hdegree | hR
    · exact hn hdegree
    · exact Nat.zero_ne_one (@Subsingleton.elim ℕ hR 0 1)
  exact ⟨hnot 0 (by decide), hnot 2 (by decide)⟩

end

end ToricIdeals.RationalNormalCurve.SurjectivityClient
