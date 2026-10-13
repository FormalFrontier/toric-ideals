/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.SplitQuadric.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Coefficients in the determinantal coordinate algebra

The coefficient homomorphism into the split quadric coordinate algebra is injective
for every commutative coefficient ring, including the zero ring. Evaluation at the
origin gives an elementary retraction of the coefficient homomorphism. Consequently,
a domain coordinate ring, or a prime relation ideal, forces the coefficient ring
to be a domain.

## Implementation notes

These are necessary directions only. The proofs use point evaluation through the
quotient universal morphism, not the parametrization's injectivity or any of the
global kernel, domain or primality theorems.

## References

* `ToricIdeals.SplitQuadric.Basic`: the formalization of the quotient universal morphism
  `SplitQuadric.lift`.
* Mathlib, `Algebra/Ring/Hom/InjSurj`: pullback of the domain property along an
  injective ring homomorphism.
* Mathlib, `RingTheory/Ideal/Quotient/Basic`: the domain instance for a quotient
  by a prime ideal.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*
  §4.4: the motivating determinant quadric.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

variable (A : Type u) [CommRing A]

namespace Examples

/-- Evaluation on the `w`-axis, defined directly by the quotient universal morphism. -/
def axisPoint (a : A) : CoordinateRing A →ₐ[A] A :=
  lift A (![a, 0, 0, 0] : Fin 4 → A) (by simp)

@[simp]
theorem axisPoint_w (a : A) : axisPoint A a (w A) = a := by
  simp [axisPoint, w]

@[simp]
theorem axisPoint_coefficient (a b : A) : axisPoint A a (coefficientMap A b) = b :=
  (axisPoint A a).commutes b

end Examples

open Examples in
/-- The coefficient homomorphism into the determinantal coordinate algebra is injective. -/
theorem coefficientMap_injective : Function.Injective (coefficientMap A) := by
  intro a b h
  have h' := congrArg (axisPoint A 0) h
  simpa using h'

/-- If the determinantal coordinate algebra is a domain, its coefficient ring is a domain. -/
theorem isDomain_of_coordinateRing [IsDomain (CoordinateRing A)] : IsDomain A :=
  (coefficientMap_injective A).isDomain (coefficientMap A)

/-- A prime determinantal relation ideal forces the coefficient ring to be a domain. -/
theorem isDomain_of_relationIdeal_isPrime (h : (relationIdeal A).IsPrime) : IsDomain A := by
  let : (relationIdeal A).IsPrime := h
  exact isDomain_of_coordinateRing A

end SplitQuadric
