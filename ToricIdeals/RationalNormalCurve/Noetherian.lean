/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
import MultivariatePolynomials.Noetherian
public import ToricIdeals.RationalNormalCurve
public import ToricIdeals.RationalNormalCurve.AxisProjection

/-!
# Noetherian rational-normal-curve coordinate rings

The quotient of `Source R n` by `hankelIdeal R n` is Noetherian exactly when
its commutative coefficient ring `R` is Noetherian. The criterion concerns
every degree, including zero, and includes zero coefficient rings.

For the canonical coefficient `R`-module action, the quotient is Noetherian
exactly when `R` is a zero ring, expressed by `Subsingleton R`. This differs
from Noetherianity over the quotient ring itself.

At degree zero the source has one variable and the Hankel ideal is `⊥`;
at degree one the source has two variables and the Hankel ideal is again `⊥`.
The degree-zero quotient is not replaced by the parametrization kernel
quotient or image.

## References

* Mathlib contributors, `Mathlib.RingTheory.Noetherian.Basic`, for
  coefficient-module descent along surjective linear maps and
  trivial-coefficient Noetherianity.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft, Exercise 3.6.F, motivates the Hankel presentation used here.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  polynomial presentation, Hankel ideal and small-degree boundary results.
* Mathlib contributors, `Mathlib.RingTheory.Polynomial.Basic` and
  `Mathlib.RingTheory.Ideal.Quotient.Noetherian`, supply the finite-variable
  Hilbert basis theorem and Noetherian quotient-ring theory.
* Formal Frontier Agents, `MultivariatePolynomials.Noetherian`, for the
  coefficient-module criterion for univariate polynomials.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- The quotient by the Hankel minors is Noetherian exactly when its coefficient
ring is Noetherian, in every degree, including zero. This uses the polynomial
presentation from `ToricIdeals.RationalNormalCurve` and Mathlib's
`IsNoetherianRing`; it needs no nontriviality, domain or positive-degree assumption. -/
theorem quotient_isNoetherianRing_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsNoetherianRing (Source R n ⧸ hankelIdeal R n) ↔ IsNoetherianRing R := by
  constructor
  · intro hQ
    let : IsNoetherianRing (Source R n ⧸ hankelIdeal R n) := hQ
    let e : Source R n →+* R := MvPolynomial.constantCoeff
    have hI : hankelIdeal R n ≤ RingHom.ker e := by
      apply Ideal.span_le.mpr
      rintro _ ⟨p, rfl⟩
      apply RingHom.mem_ker.mpr
      simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
        mul_zero, sub_self]
    let g : (Source R n ⧸ hankelIdeal R n) →+* R :=
      Ideal.Quotient.lift (hankelIdeal R n) e
        (fun _ hf => RingHom.mem_ker.mp (hI hf))
    have hg : Function.Surjective g := by
      intro r
      refine ⟨Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r), ?_⟩
      simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
    exact isNoetherianRing_of_surjective (Source R n ⧸ hankelIdeal R n) R g hg
  · intro hR
    let : IsNoetherianRing R := hR
    let : IsNoetherianRing (Source R n) := MvPolynomial.isNoetherianRing_fin
    exact Ideal.Quotient.isNoetherianRing (hankelIdeal R n)

/-- In every degree, the full Hankel quotient is Noetherian as a module over
its coefficient ring `R` exactly when `R` is a zero ring. The scalar action is
the canonical coefficient action, not multiplication as a quotient self-module;
no nontriviality or positive-degree assumption is needed. -/
theorem quotient_isNoetherian_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsNoetherian R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R := by
  constructor
  · intro hQ
    let : IsNoetherian R (Source R n ⧸ hankelIdeal R n) := hQ
    have hP : IsNoetherian R (Polynomial R) :=
      isNoetherian_of_surjective (axisProjection R n).toLinearMap
        (LinearMap.range_eq_top.mpr (axisProjection_surjective R n))
    exact (Polynomial.isNoetherian_iff R).mp hP
  · intro hR
    let : Subsingleton R := hR
    exact isNoetherian_of_subsingleton R (Source R n ⧸ hankelIdeal R n)

end ToricIdeals.RationalNormalCurve
