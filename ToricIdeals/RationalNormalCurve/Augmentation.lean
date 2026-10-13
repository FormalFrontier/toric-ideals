/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve

/-!
# Coefficient augmentation of rational-normal-curve coordinate rings

Zero-variable evaluation descends to an `R`-algebra homomorphism from the full
quotient of `Source R n` by `hankelIdeal R n` to its coefficient ring. Every
Hankel minor is a difference of products of variables, so this evaluation kills
the generating span. The construction applies to every commutative coefficient
ring and every degree, including zero and one. In those degrees the quotient
remains the full polynomial ring; it is not replaced by the parametrization image.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Noetherian` and
  `ToricIdeals.RationalNormalCurve.Jacobson`, for the constant-coefficient
  augmentation argument followed here.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Eval` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, for polynomial algebra evaluation
  and algebra-homomorphism descent to ideal quotients.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- The coefficient augmentation of the full Hankel quotient, induced by
sending every variable to zero and fixing the coefficient ring. -/
noncomputable def quotientAugmentation (R : Type u) [CommRing R] (n : ℕ) :
    (Source R n ⧸ hankelIdeal R n) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (hankelIdeal R n)
    (MvPolynomial.aeval (0 : Fin (n + 1) → R))
    (by
      intro f hf
      have hI : hankelIdeal R n ≤
          RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → R)).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨p, rfl⟩
        apply RingHom.mem_ker.mpr
        change MvPolynomial.aeval (0 : Fin (n + 1) → R) (hankelMinor R n p) = 0
        simp only [hankelMinor, map_sub, map_mul, MvPolynomial.aeval_X, Pi.zero_apply,
          mul_zero, sub_self]
      exact RingHom.mem_ker.mp (hI hf))

/-- The augmentation of a quotient representative is its constant coefficient. -/
@[simp] theorem quotientAugmentation_mk (R : Type u) [CommRing R] (n : ℕ)
    (f : Source R n) :
    quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) f) =
      MvPolynomial.constantCoeff f := by
  change MvPolynomial.aeval (0 : Fin (n + 1) → R) f = MvPolynomial.constantCoeff f
  simpa only [Algebra.algebraMap_self_apply] using (MvPolynomial.aeval_zero (S₁ := R) f)

/-- The coefficient augmentation is surjective in every degree. -/
theorem quotientAugmentation_surjective (R : Type u) [CommRing R] (n : ℕ) :
    Function.Surjective (quotientAugmentation R n) := by
  intro r
  refine ⟨Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r), ?_⟩
  rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_C]

end ToricIdeals.RationalNormalCurve
