/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Defs
public import ToricIdeals.RationalNormalCurve

/-!
# Artinian rational-normal-curve coordinate rings

The quotient of `Source R n` by `hankelIdeal R n` is Artinian exactly when
its commutative coefficient ring `R` is a zero ring, expressed by
`Subsingleton R`. Artinianity is taken over the quotient ring itself, not
as a module over the coefficient ring. The criterion concerns every degree
and includes zero coefficient rings, rings with nilpotent elements and
product rings.

At degree zero the Hankel ideal is `⊥`, so the quotient is the full
one-variable polynomial ring, not the parametrization kernel quotient or
image. At degree one the ideal is again `⊥`, giving the full two-variable
polynomial ring.

Sending `x₀` to `Polynomial.X` and every other variable to zero gives a
surjection from the quotient onto `Polynomial R`. Over a nonzero coefficient
ring, Artinianity would make the regular element `X` a unit, contradicting
its noninvertibility.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the Hankel
  presentation and its small-degree boundary results.
* Mathlib contributors, `Mathlib.RingTheory.Artinian.Defs` and
  `Mathlib.RingTheory.Artinian.Module`, for Artinianity over the ring itself,
  its descent along surjective ring homomorphisms and the regular-unit criterion.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Eval`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`, `Mathlib.Algebra.Polynomial.Monomial`
  and `Mathlib.RingTheory.Ideal.Quotient.Defs`, for polynomial evaluation,
  homomorphism extensionality and quotient lifts.
* Mathlib contributors, `Mathlib.Algebra.Polynomial.Coeff` and
  `Mathlib.Algebra.Polynomial.Degree.Operations`, for regularity and
  noninvertibility of the polynomial variable.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- In every degree, the quotient by the Hankel minors is Artinian as a module
over itself exactly when its commutative coefficient ring is a zero ring.
This includes degree zero and needs no nontriviality, domain or
positive-degree assumption. The proof uses Mathlib's surjective descent of
Artinianity and its criterion that regular elements of an Artinian ring are units. -/
theorem quotient_isArtinianRing_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsArtinianRing (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R := by
  classical
  constructor
  · intro hArt
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact hR
    · let : Nontrivial R := hR
      -- Retain the first variable; every term of a minor has a successor variable.
      let e : Source R n →+* Polynomial R :=
        MvPolynomial.eval₂Hom Polynomial.C
          (fun i => if i = 0 then Polynomial.X else 0)
      have he : hankelIdeal R n ≤ RingHom.ker e := by
        apply Ideal.span_le.2
        rintro _ ⟨p, rfl⟩
        apply RingHom.mem_ker.mpr
        simp only [hankelMinor, map_sub, map_mul, e, MvPolynomial.eval₂Hom_X',
          Fin.succ_ne_zero, ↓reduceIte, mul_zero, zero_mul, sub_self]
      -- The one-variable polynomial ring supplies a section of the evaluation.
      let s : Polynomial R →+* Source R n :=
        Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin (n + 1)))
      have hes : e.comp s = RingHom.id (Polynomial R) := by
        apply Polynomial.ringHom_ext
        · intro r
          simp [e, s]
        · simp [e, s]
      have heSurj : Function.Surjective e := by
        intro f
        exact ⟨s f, RingHom.congr_fun hes f⟩
      have hkill : ∀ f : Source R n, f ∈ hankelIdeal R n → e f = 0 :=
        fun _ hf => he hf
      let q : Source R n ⧸ hankelIdeal R n →+* Polynomial R :=
        Ideal.Quotient.lift (hankelIdeal R n) e hkill
      have hqSurj : Function.Surjective q :=
        Ideal.Quotient.lift_surjective_of_surjective (hankelIdeal R n) hkill heSurj
      let : IsArtinianRing (Source R n ⧸ hankelIdeal R n) := hArt
      have : IsArtinianRing (Polynomial R) := hqSurj.isArtinianRing
      exact (Polynomial.not_isUnit_X (R := R)
        (IsArtinianRing.isUnit_iff_isRegular.mpr Polynomial.isRegular_X)).elim
  · intro hR
    let : Subsingleton R := hR
    have h01 : (0 : Source R n) = 1 := Subsingleton.elim _ _
    apply Ring.isArtinian_of_zero_eq_one
    simpa only [map_zero, map_one] using
      congrArg (Ideal.Quotient.mk (hankelIdeal R n)) h01

end ToricIdeals.RationalNormalCurve
