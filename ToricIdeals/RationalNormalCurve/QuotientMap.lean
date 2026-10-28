/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve

/-!
# The Hankel quotient parametrization

The rational-normal-curve parametrization descends to an `R`-algebra map
from the full Hankel quotient to the full bivariate polynomial ring in
every degree. At degree zero the quotient retains its source variable;
this map is not the quotient-to-range equivalence.

## References

* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  for algebra-homomorphism descent to ideal quotients.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The parametrization from the full Hankel quotient to the full target
polynomial ring, with its coefficient algebra structure. -/
noncomputable def quotientMap : (Source R n ⧸ hankelIdeal R n) →ₐ[R] Target R :=
  Ideal.Quotient.liftₐ (hankelIdeal R n)
    (AddMonoidAlgebra.mapDomainAlgHom R R (rncExponent n))
    (fun _ hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp))

/-- On representatives the quotient parametrization is the original map. -/
@[simp] theorem quotientMap_mk (p : Source R n) :
    quotientMap R n (Ideal.Quotient.mk (hankelIdeal R n) p) = rncMap R n p := rfl

/-- The quotient parametrization fixes coefficients. -/
theorem quotientMap_C (r : R) :
    quotientMap R n (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)) =
      MvPolynomial.C r := by
  rw [quotientMap_mk, rncMap_C]

/-- A quotient coordinate has its designated monomial image. -/
theorem quotientMap_X (i : Fin (n + 1)) :
    quotientMap R n (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) =
      MvPolynomial.monomial (coordinateExponent n i) 1 := by
  rw [quotientMap_mk, rncMap_X]

/-- The underlying ring map is the canonical quotient lift. -/
theorem quotientMap_toRingHom :
    (quotientMap R n).toRingHom =
      Ideal.Quotient.lift (hankelIdeal R n) (rncMap R n)
        (fun _ hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp)) := rfl

/-- Composing with the quotient projection recovers the parametrization. -/
theorem quotientMap_comp_mk :
    (quotientMap R n).toRingHom.comp (Ideal.Quotient.mk (hankelIdeal R n)) =
      rncMap R n := rfl

end ToricIdeals.RationalNormalCurve
