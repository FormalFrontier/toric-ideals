/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import ToricIdeals.RationalNormalCurve
public import ToricIdeals.RationalNormalCurve.QuotientMap
import MultivariatePolynomials.EvaluationIdeal

/-!
# Coefficient augmentation of rational-normal-curve coordinate rings

Zero-variable evaluation descends to an `R`-algebra homomorphism from the full
quotient of `Source R n` by `hankelIdeal R n` to its coefficient ring. Every
Hankel minor is a difference of products of variables, so this evaluation kills
the generating span. The construction applies to every commutative coefficient
ring and every degree, including zero and one. In those degrees the quotient
remains the full polynomial ring; it is not replaced by the parametrization image.

The kernel of this augmentation is the ideal spanned by all quotient classes of
variables. This includes the class of `X₀` in degree zero. Membership in this
span is equivalent to vanishing under the augmentation. Consequently, Mathlib's
first isomorphism theorem identifies the quotient by this span with `R`.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Noetherian` and
  `ToricIdeals.RationalNormalCurve.Jacobson`, for the constant-coefficient
  augmentation argument followed here.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Eval` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, for polynomial algebra evaluation
  and algebra-homomorphism descent to ideal quotients.
* Formal Frontier Agents, `MultivariatePolynomials.EvaluationIdeal`, for the
  coordinate-difference description of evaluation kernels, specialized here to
  the zero point and transported to the Hankel quotient using Mathlib's ideal
  map and comap APIs.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- Every Hankel relation belongs to the square of the polynomial augmentation
ideal, over every commutative coefficient ring and in every degree. -/
theorem hankelIdeal_le_idealOfVars_sq (R : Type u) [CommRing R] (n : ℕ) :
    hankelIdeal R n ≤ (MvPolynomial.idealOfVars (Fin (n + 1)) R) ^ 2 := by
  rw [hankelIdeal, pow_two]
  apply Ideal.span_le.mpr
  rintro _ ⟨p, rfl⟩
  apply Ideal.sub_mem
  · exact Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_range_self p.1.1.castSucc))
      (Ideal.subset_span (Set.mem_range_self p.1.2.succ))
  · exact Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_range_self p.1.1.succ))
      (Ideal.subset_span (Set.mem_range_self p.1.2.castSucc))

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

/-- In positive degree, taking the constant coefficient after the quotient
parametrization agrees with the coefficient augmentation. In degree zero the
source variable remains in the full quotient and is sent to `1` by the
parametrization, whereas its augmentation is `0`. -/
theorem constantCoeff_comp_quotientMap (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) :
    (MvPolynomial.constantCoeff : Target R →+* R).comp (quotientMap R n).toRingHom =
      (quotientAugmentation R n).toRingHom := by
  have hcomp : MvPolynomial.constantCoeff.comp (rncMap R n) =
      (MvPolynomial.constantCoeff : Source R n →+* R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, rncMap_C, MvPolynomial.constantCoeff_C]
    · intro i
      have he : coordinateExponent n i ≠ 0 := by
        intro h
        have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
        have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
        simp only [coordinateExponent, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
          Finsupp.zero_apply, add_zero, zero_add] at h0 h1
        omega
      simp only [RingHom.comp_apply, rncMap_X, MvPolynomial.constantCoeff_monomial,
        ite_eq_right he, MvPolynomial.constantCoeff_X]
  apply RingHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro f
  change MvPolynomial.constantCoeff (rncMap R n f) =
    quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) f)
  exact (RingHom.congr_fun hcomp f).trans (quotientAugmentation_mk R n f).symm

/-- The coefficient augmentation is surjective in every degree. -/
theorem quotientAugmentation_surjective (R : Type u) [CommRing R] (n : ℕ) :
    Function.Surjective (quotientAugmentation R n) := by
  intro r
  refine ⟨Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r), ?_⟩
  rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_C]

/-- The augmentation kernel is the ideal spanned by all variable classes in
the full Hankel quotient, over every commutative coefficient ring and in every degree. -/
theorem ker_quotientAugmentation (R : Type u) [CommRing R] (n : ℕ) :
    RingHom.ker (quotientAugmentation R n).toRingHom =
      Ideal.span (Set.range (fun i : Fin (n + 1) =>
        Ideal.Quotient.mkₐ R (hankelIdeal R n) (MvPolynomial.X i))) := by
  have hcomp : (quotientAugmentation R n).toRingHom.comp
      (Ideal.Quotient.mk (hankelIdeal R n)) =
        (MvPolynomial.constantCoeff : Source R n →+* R) := by
    apply RingHom.ext
    intro f
    exact quotientAugmentation_mk R n f
  have hker : RingHom.ker (MvPolynomial.constantCoeff : Source R n →+* R) =
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Source R n)) := by
    simpa only [Pi.zero_apply, map_zero, sub_zero, MvPolynomial.eval_zero] using
      (MvPolynomial.ideal_span_X_sub_C_eq_ker_eval (R := R)
        (0 : Fin (n + 1) → R)).symm
  calc
    RingHom.ker (quotientAugmentation R n).toRingHom =
        ((RingHom.ker (quotientAugmentation R n).toRingHom).comap
          (Ideal.Quotient.mk (hankelIdeal R n))).map
            (Ideal.Quotient.mk (hankelIdeal R n)) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    _ = (RingHom.ker (MvPolynomial.constantCoeff : Source R n →+* R)).map
        (Ideal.Quotient.mk (hankelIdeal R n)) := by
      rw [RingHom.comap_ker, hcomp]
    _ = (Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Source R n))).map
        (Ideal.Quotient.mk (hankelIdeal R n)) := by rw [hker]
    _ = _ := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl

/-- A class belongs to the span of all variable classes exactly when its
augmentation vanishes. -/
theorem mem_span_quotient_X_iff (R : Type u) [CommRing R] (n : ℕ)
    (q : Source R n ⧸ hankelIdeal R n) :
    q ∈ Ideal.span (Set.range (fun i : Fin (n + 1) =>
      Ideal.Quotient.mkₐ R (hankelIdeal R n) (MvPolynomial.X i))) ↔
        quotientAugmentation R n q = 0 := by
  rw [← ker_quotientAugmentation, RingHom.mem_ker]
  rfl

end ToricIdeals.RationalNormalCurve
