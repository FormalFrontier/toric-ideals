/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.SplitQuadric.Kernel
public import ToricIdeals.SplitQuadric.CoefficientRetraction
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Range, domain and primality criteria for the split quadric

The first isomorphism theorem identifies the coordinate algebra with the
range of its parametrization, not the entire parameter algebra. The
coordinate algebra of `wz - xy = 0` is a domain exactly when its
commutative coefficient ring is a domain. The necessary direction uses the
coefficient retraction, independent of the kernel proof; the sufficient
direction uses the injective parametrization into the polynomial algebra.
Primality of the relation ideal follows from Mathlib's quotient-domain
criterion. Nontriviality and properness are included in these statements.

## References

* Formal Frontier Agents: the determinant model and coefficient retraction.
* Mathlib, `Algebra/Ring/Hom/InjSurj` and `RingTheory/Ideal/Quotient/Basic`:
  domain transport and the quotient-domain criterion for prime ideals.
* Mathlib, `RingTheory/Ideal/Quotient/Operations`: the first isomorphism
  theorem for algebras and its computation on quotient classes.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025),
  §4.4: motivation for the determinant model.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

variable (A : Type u) [CommRing A]

/-- The first-isomorphism equivalence with the range of the parametrization.
Its codomain is the range subalgebra, not the whole parameter algebra. -/
noncomputable def rangeEquiv : CoordinateRing A ≃ₐ[A] (theta A).range :=
  (Ideal.quotientEquivAlgOfEq A (kernel_theta A).symm).trans
    (Ideal.quotientKerEquivRange (theta A))

/-- The range equivalence computes substitution on a polynomial representative. -/
theorem rangeEquiv_quotientMap (p : Polynomial A) :
    (rangeEquiv A (quotientMap A p) : ParameterPolynomial A) = theta A p := by
  -- Both quotient transports keep the representative, and the final quotient lift
  -- evaluates it with the range-restricted homomorphism.
  rfl

/-- Including the range equivalence in the parameter algebra gives `phi`. -/
@[simp]
theorem rangeEquiv_coe_apply (q : CoordinateRing A) :
    (rangeEquiv A q : ParameterPolynomial A) = phi A q := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective A (relationIdeal A) q
  have hp' : quotientMap A p = q := hp
  rw [← hp', rangeEquiv_quotientMap, phi_quotientMap]

/-- The coordinate algebra is a domain exactly when its coefficient ring is.
Necessity uses the coefficient retraction; sufficiency uses the injective parametrization
into the polynomial algebra over a domain. Nontriviality is included in `IsDomain`. -/
theorem coordinateRing_isDomain_iff : IsDomain (CoordinateRing A) ↔ IsDomain A := by
  constructor
  · intro h
    let : IsDomain (CoordinateRing A) := h
    exact isDomain_of_coordinateRing A
  · intro h
    let : IsDomain A := h
    let : IsDomain (ParameterPolynomial A) := inferInstance
    exact (phi_injective A).isDomain (phi A)

/-- The relation ideal is prime exactly when the coefficient ring is a domain.
Mathlib's quotient-domain criterion includes properness of the ideal, so the zero
coefficient ring is excluded without adding a hypothesis. -/
theorem relationIdeal_isPrime_iff : (relationIdeal A).IsPrime ↔ IsDomain A :=
  (Ideal.Quotient.isDomain_iff_prime (relationIdeal A)).symm.trans
    (coordinateRing_isDomain_iff A)

end SplitQuadric
