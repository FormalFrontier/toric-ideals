/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.CoefficientAlgebra

/-!
# Coefficient-module uses of Hankel quotients

Freeness makes doubling by an integer injective on the full Hankel quotient
in every degree. Flatness makes tensoring with the full Hankel quotient
preserve the inclusion of the submodule spanned by `2` in `ZMod 4`, a
nonreduced coefficient ring. Both use the canonical coefficient action and
include degree zero, with its full one-variable polynomial quotient.

The clients use Mathlib's torsion-free-module and tensor-injectivity APIs,
rather than constructing a basis or identifying the quotient with an image.
-/

open ToricIdeals.RationalNormalCurve

/-- Integer doubling can be cancelled in every Hankel quotient. -/
private theorem integer_coefficient_doubling_injective (n : ℕ) :
    Function.Injective (fun q : Source ℤ n ⧸ hankelIdeal ℤ n => (2 : ℤ) • q) := by
  let : Module.Free ℤ (Source ℤ n ⧸ hankelIdeal ℤ n) := quotient_free ℤ n
  exact smul_right_injective _ (by simp : (2 : ℤ) ≠ 0)

/-- Tensoring with the Hankel quotient over `ZMod 4` preserves the inclusion of `(2)`. -/
private theorem mod_four_tensor_ideal_inclusion_injective (n : ℕ) :
    Function.Injective
      ((Submodule.span (ZMod 4) ({2} : Set (ZMod 4))).subtype.lTensor
        (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)) := by
  let : Module.Flat (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) :=
    quotient_flat (ZMod 4) n
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
