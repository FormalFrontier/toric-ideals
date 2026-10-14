/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.CoefficientFiniteness

/-!
# Clients of the Hankel quotient coefficient-finiteness criterion

The criterion rules out finite generation over the integers even in degree
zero, where the full one-variable polynomial quotient remains. Its reverse
direction gives finite coefficient modules over the zero ring in every degree.
These clients use the public criterion, separately from the polynomial and
Hankel-quotient coefficient models.
-/

open ToricIdeals.RationalNormalCurve

/-- The degree-zero integer Hankel quotient is not a finite integer module. -/
private theorem integer_degree_zero_quotient_not_finite :
    ¬ Module.Finite ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) := by
  intro hQ
  have hR := (quotient_moduleFinite_iff ℤ 0).mp hQ
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (@Subsingleton.elim ℤ hR 1 0)

/-- Every Hankel quotient over the zero coefficient ring is a finite module. -/
private theorem zero_coefficients_quotient_finite (n : ℕ) :
    Module.Finite (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
  (quotient_moduleFinite_iff (ZMod 1) n).mpr inferInstance
