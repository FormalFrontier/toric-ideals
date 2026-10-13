/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import ToricIdeals

/-!
# Jacobson consequences of the Hankel quotient criterion

Every quotient by the Hankel minors over `ℚ` is Jacobson, including degrees zero
and one. Conversely, if a Hankel quotient is Jacobson, its coefficient ring is
Jacobson, so the radical and Jacobson radical of every coefficient ideal agree.
The reverse example assumes only the quotient's Jacobson property, not a
Jacobson instance on the coefficient ring.

Both examples use the quotient ring itself, rather than the parametrization
image.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Jacobson`, for the
  quotient criterion.
* Mathlib contributors, `Mathlib.Algebra.Field.Rat`, for the rational field
  instance, and `Mathlib.RingTheory.Artinian.Module` and
  `Mathlib.RingTheory.Jacobson.Ring`, for Jacobson instances on fields and
  `Ideal.radical_eq_jacobson`.
-/

namespace ToricIdeals.RationalNormalCurve

universe u

/-- All rational-coefficient Hankel quotients are Jacobson. -/
private theorem rational_quotient_isJacobsonRing (n : ℕ) :
    IsJacobsonRing (Source ℚ n ⧸ hankelIdeal ℚ n) :=
  (quotient_isJacobsonRing_iff ℚ n).mpr inferInstance

/-- A Jacobson Hankel quotient makes radical and Jacobson radical agree for
all ideals of its coefficient ring. -/
private theorem radical_eq_jacobson_of_quotient_isJacobsonRing
    (R : Type u) [CommRing R] (n : ℕ)
    [IsJacobsonRing (Source R n ⧸ hankelIdeal R n)] (I : Ideal R) :
    I.radical = I.jacobson := by
  let : IsJacobsonRing R := (quotient_isJacobsonRing_iff R n).mp inferInstance
  exact Ideal.radical_eq_jacobson I

#print axioms rational_quotient_isJacobsonRing
#print axioms radical_eq_jacobson_of_quotient_isJacobsonRing

end ToricIdeals.RationalNormalCurve
