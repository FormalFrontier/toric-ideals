/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.FormallySmooth

/-!
# Small models for formal smoothness of Hankel quotients

The degree-one quotient over the integers and the degree-zero quotient over
any commutative ring are formally smooth for the canonical coefficient action.
The degree-zero quotient retains its polynomial variable. The degree-two
quotient over `ZMod 2` is not formally smooth, while over the zero coefficient
ring `ZMod 1` every degree is formally smooth.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u

/-- The degree-one Hankel quotient over the integers is formally smooth. -/
example : Algebra.FormallySmooth ℤ (Source ℤ 1 ⧸ hankelIdeal ℤ 1) := by
  exact (quotient_formallySmooth_iff ℤ 1).mpr (Or.inl le_rfl)

/-- The full degree-zero polynomial quotient is formally smooth over any coefficient ring. -/
example (R : Type u) [CommRing R] :
    Algebra.FormallySmooth R (Source R 0 ⧸ hankelIdeal R 0) := by
  exact (quotient_formallySmooth_iff R 0).mpr (Or.inl (Nat.zero_le 1))

/-- Characteristic two already detects the failure of formal smoothness in degree two. -/
example : ¬ Algebra.FormallySmooth (ZMod 2) (Source (ZMod 2) 2 ⧸ hankelIdeal (ZMod 2) 2) := by
  intro h
  rcases (quotient_formallySmooth_iff (ZMod 2) 2).mp h with hn | hR
  · exact (Nat.not_succ_le_self 1) hn
  · let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
    let : Subsingleton (ZMod 2) := hR
    exact zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

/-- Over the zero coefficient ring every Hankel quotient is formally smooth. -/
example (n : ℕ) :
    Algebra.FormallySmooth (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  exact (quotient_formallySmooth_iff (ZMod 1) n).mpr (Or.inr inferInstance)

end ToricIdeals.RationalNormalCurve
