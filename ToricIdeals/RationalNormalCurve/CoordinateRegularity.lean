/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Regular.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve

/-!
# Regular coordinate classes in rational-normal-curve rings

Each coordinate class in the quotient of `Source R n` by `hankelIdeal R n`
is regular over an arbitrary commutative coefficient ring. Regularity here
means injectivity of multiplication on both sides, expressed by Mathlib's
root `IsRegular`, rather than a regular-sequence condition.

The statement concerns every `i : Fin (n + 1)`. The first and last
coordinates are obtained by taking `i = 0` and `i = Fin.last n`.
There is no domain, reducedness, Noetherianity, nontriviality or
positive-degree hypothesis. At degree zero the Hankel ideal is bottom and
the quotient is the full one-variable polynomial ring, not the image of
the monomial parametrization. At degree one it is the full two-variable
polynomial ring.

For positive degree, the kernel calculation gives an injective quotient
lift of the monomial parametrization. Each coordinate maps to a monomial
with coefficient one, which is regular without restrictions on zero
divisors in the coefficient ring. Injectivity reflects cancellation back
to the quotient. At degree zero the quotient by the bottom ideal instead
identifies with the polynomial ring, where a variable is regular.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
  3.6.F, motivates the Hankel presentation of the rational normal curve.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies that
  presentation, its kernel calculation and its small-degree boundary API.
* Mathlib contributors, `Mathlib.Algebra.Regular.Defs` and
  `Mathlib.Algebra.MvPolynomial.Basic`, supply the element-regularity
  predicate and regularity of coefficient-one monomials and variables.
* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  supply injectivity of quotient lifts and the bottom-quotient equivalence.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- Every coordinate class in the Hankel quotient is regular, over any
commutative coefficient ring and in every degree. This is the coordinate
cancellation property for the rational-normal-curve presentation motivated
by Vakil's Exercise 3.6.F. At degree zero it concerns the quotient by the
bottom ideal, not the parametrization kernel or image. -/
theorem isRegular_quotient_X (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    _root_.IsRegular
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n)) := by
  cases n with
  | zero =>
      rw [hankelIdeal_zero]
      apply isLeftRegular_iff_isRegular.mp
      intro a b hab
      apply (RingEquiv.quotientBot (Source R 0)).injective
      apply (MvPolynomial.isRegular_X (R := R) (n := i)).left
      simpa only [map_mul, RingEquiv.quotientBot_mk] using
        congrArg (RingEquiv.quotientBot (Source R 0)) hab
  | succ n =>
      let H : ∀ p : Source R (n + 1), p ∈ hankelIdeal R (n + 1) →
          rncMap R (n + 1) p = 0 :=
        fun p hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R (n + 1) hp)
      let f := Ideal.Quotient.lift (hankelIdeal R (n + 1)) (rncMap R (n + 1)) H
      have hf : Function.Injective f :=
        RingHom.lift_injective_of_ker_le_ideal (hankelIdeal R (n + 1)) H
          (le_of_eq (hankelIdeal_eq_ker R (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))).symm)
      have hX : _root_.IsRegular
          (f (Ideal.Quotient.mk (hankelIdeal R (n + 1))
            (MvPolynomial.X i : Source R (n + 1)))) := by
        simpa only [f, Ideal.Quotient.lift_mk, rncMap_X] using
          (isRegular_one (R := R)).monomial (m := coordinateExponent (n + 1) i)
      apply isLeftRegular_iff_isRegular.mp
      intro a b hab
      apply hf
      apply hX.left
      simpa only [map_mul] using congrArg f hab

end ToricIdeals.RationalNormalCurve
