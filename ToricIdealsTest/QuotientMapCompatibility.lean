/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.RingTheory.RingHom.Flat
import ToricIdeals.RationalNormalCurve.QuotientMap

/-!
# Quotient-map compatibility checks

The canonical quotient map commutes with coefficients and agrees with
the raw ring lift. Over the integers in degree zero, it kills the
retained variable minus one but does not kill the coefficient two.
-/

open MvPolynomial
open ToricIdeals.RationalNormalCurve

universe u

-- Coefficient compatibility is intrinsic to the algebra homomorphism.
private theorem quotientMap_commutes (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    quotientMap R n (algebraMap R (Source R n ⧸ hankelIdeal R n) r) = C r :=
  (quotientMap R n).commutes r

-- The independently used ring lift and the new map are the same map.
private theorem quotientMap_toRingHom_eq_lift (R : Type u) [CommRing R] (n : ℕ) :
    (quotientMap R n).toRingHom =
      Ideal.Quotient.lift (hankelIdeal R n) (rncMap R n)
        (fun _ hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp)) :=
  quotientMap_toRingHom R n

-- Degree zero retains its variable, although its image is one.
private theorem quotientMap_zero_kernel_element : quotientMap ℤ 0
    (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X 0 - 1)) = 0 := by
  simp [quotientMap_mk, rncMap_X, coordinateExponent]

private theorem quotientMap_two_ne_zero : quotientMap ℤ 0
    (Ideal.Quotient.mk (hankelIdeal ℤ 0) (C 2)) ≠ 0 := by
  rw [quotientMap_C]
  intro h
  have hc := congrArg (fun p : Target ℤ => p.coeff (0 : Fin 2 →₀ ℕ)) h
  simp at hc
