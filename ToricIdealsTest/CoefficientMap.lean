/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.CoefficientMap

/-!
# Coefficient change on full Hankel quotients

Integer-to-rational coefficient change is injective on the quadratic Hankel
quotient; reduction modulo two is surjective. At degree zero the polynomial
variable still survives in the full quotient, whereas changing integer
coefficients to the zero ring is not injective.
-/

open ToricIdeals.RationalNormalCurve

private theorem intCast_rat_quotientMap_injective : Function.Injective
    (Ideal.quotientMap (hankelIdeal ℚ 2) (MvPolynomial.map (Int.castRingHom ℚ))
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal (Int.castRingHom ℚ) 2).le)) := by
  exact (coefficient_quotientMap_injective_iff ℤ ℚ (Int.castRingHom ℚ) 2).2
    Int.cast_injective

private theorem intCast_zmod_two_quotientMap_surjective : Function.Surjective
    (Ideal.quotientMap (hankelIdeal (ZMod 2) 2)
      (MvPolynomial.map (Int.castRingHom (ZMod 2)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (Int.castRingHom (ZMod 2)) 2).le)) := by
  exact (coefficient_quotientMap_surjective_iff ℤ (ZMod 2)
    (Int.castRingHom (ZMod 2)) 2).2 ZMod.intCast_surjective

private theorem hankel_zero_quotient_X_ne_zero : Ideal.Quotient.mk (hankelIdeal ℤ 0)
    (MvPolynomial.X (0 : Fin 1)) ≠ 0 := by
  intro h
  have hp : (MvPolynomial.X (0 : Fin 1) : Source ℤ 0) = 0 := by
    simpa only [hankelIdeal_zero, Submodule.mem_bot] using
      (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact MvPolynomial.X_ne_zero (0 : Fin 1) hp

private theorem intCast_zmod_one_quotientMap_not_injective : ¬ Function.Injective
    (Ideal.quotientMap (hankelIdeal (ZMod 1) 0)
      (MvPolynomial.map (Int.castRingHom (ZMod 1)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (Int.castRingHom (ZMod 1)) 0).le)) := by
  rw [coefficient_quotientMap_injective_iff]
  intro h
  have h01 : (0 : ℤ) = 1 := h (Subsingleton.elim _ _)
  exact zero_ne_one h01
