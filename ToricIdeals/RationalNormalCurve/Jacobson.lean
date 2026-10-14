/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import ToricIdeals.RationalNormalCurve.Augmentation

/-!
# Jacobson rational-normal-curve coordinate rings

The quotient of `Source R n` by `hankelIdeal R n` is Jacobson exactly when
its commutative coefficient ring `R` is Jacobson. The criterion uses the
quotient ring itself and concerns every degree, including zero. It includes
zero coefficient rings and requires no Noetherian, domain, field or
reducedness assumption.

At degree zero the source has one variable and the Hankel ideal is `⊥`;
at degree one the source has two variables and the Hankel ideal is again `⊥`.
The degree-zero quotient is not replaced by the parametrization kernel
quotient or image.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the Hankel
  presentation and its small-degree boundary results.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Augmentation`,
  supplies the reusable surjective coefficient augmentation of the quotient.
* Mathlib contributors, `Mathlib.RingTheory.Jacobson.Ring`, for
  `IsJacobsonRing`, finite-variable polynomial closure, quotient-ring closure
  and descent along surjective ring homomorphisms.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- In every degree, including zero, the quotient by the Hankel minors is
Jacobson exactly when its commutative coefficient ring is Jacobson.
This uses Mathlib's `IsJacobsonRing` and the quotient ring itself; it needs
no nontriviality, Noetherian, domain, field, reducedness or positive-degree assumption. -/
theorem quotient_isJacobsonRing_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsJacobsonRing (Source R n ⧸ hankelIdeal R n) ↔ IsJacobsonRing R := by
  constructor
  · intro hQ
    let : IsJacobsonRing (Source R n ⧸ hankelIdeal R n) := hQ
    let g : (Source R n ⧸ hankelIdeal R n) →+* R :=
      (quotientAugmentation R n).toRingHom
    have hg : Function.Surjective g := quotientAugmentation_surjective R n
    exact isJacobsonRing_of_surjective ⟨g, hg⟩
  · intro hR
    let : IsJacobsonRing R := hR
    let : IsJacobsonRing (Source R n) :=
      MvPolynomial.isJacobsonRing_MvPolynomial_fin (n + 1)
    infer_instance

end ToricIdeals.RationalNormalCurve
