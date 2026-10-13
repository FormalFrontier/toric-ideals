/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ToricIdeals.RationalNormalCurve

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Endpoint coordinates in a rational-normal-curve quotient

The endpoint map evaluates the two variables of `MvPolynomial (Fin 2) R`
at the classes of `X₀` and `Xₙ` in the quotient by the Hankel minors.
Coefficients are mapped by the quotient homomorphism. Its characteristic
lemmas and uniqueness property let users work without unfolding the map.

At degree zero the Hankel ideal is bottom and the quotient is the full
one-variable polynomial ring: both endpoint variables map to its single
variable class. At degree one the Hankel ideal is also bottom. The positive
degree hypothesis in the injectivity statement excludes the coincidence
of the two endpoints at degree zero over nontrivial coefficient rings.

## References

The Hankel quotient and its monomial parametrization are those of
`ToricIdeals.RationalNormalCurve`, formalized by Formal Frontier Agents.
The construction and uniqueness argument reuse Mathlib's multivariate
polynomial evaluation API by Johannes Hölzl, Johan Commelin and Mario Carneiro,
and its ideal-quotient API by the Mathlib contributors. The integral and
finite-module predicates are Mathlib's, developed by Kenny Lau and
Johan Commelin, respectively.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

/-- Evaluation at the first and last variable classes in the Hankel quotient. -/
def endpointMap (n : ℕ) :
    MvPolynomial (Fin 2) R →+* (Source R n ⧸ hankelIdeal R n) :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk (hankelIdeal R n)).comp MvPolynomial.C)
    ![Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))),
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))]

/-- The endpoint map preserves the quotient image of each coefficient. -/
@[simp] theorem endpointMap_C (n : ℕ) (r : R) :
    endpointMap (R := R) n (C r) =
      Ideal.Quotient.mk (hankelIdeal R n) (C r) := by
  simp [endpointMap]

/-- A variable is evaluated at the corresponding endpoint class. -/
theorem endpointMap_X (n : ℕ) (i : Fin 2) :
    endpointMap (R := R) n (X i) =
      ![Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))),
        Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))] i := by
  simp [endpointMap]

/-- The first endpoint variable maps to the class of `X₀`. -/
@[simp] theorem endpointMap_X_zero (n : ℕ) :
    endpointMap (R := R) n (X (0 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))) := by
  simp [endpointMap_X]

/-- The second endpoint variable maps to the class of `Xₙ`. -/
@[simp] theorem endpointMap_X_one (n : ℕ) :
    endpointMap (R := R) n (X (1 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n)) := by
  simp [endpointMap_X]

/-- Coefficients and the two endpoint images determine the endpoint map. -/
theorem endpointMap_unique (n : ℕ)
    (f : MvPolynomial (Fin 2) R →+* (Source R n ⧸ hankelIdeal R n))
    (hC : ∀ r, f (C r) = Ideal.Quotient.mk (hankelIdeal R n) (C r))
    (hzero : f (X (0 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))))
    (hone : f (X (1 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))) :
    f = endpointMap (R := R) n := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [endpointMap_C] using hC r
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [endpointMap_X_zero] using hzero
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using hone

private theorem endpointMap_zero_surjective :
    Function.Surjective (endpointMap (R := R) 0) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨C r, endpointMap_C 0 r⟩
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by simp only [map_add, hp', hq']⟩
  | mul_X p i hp =>
      obtain ⟨p', hp'⟩ := hp
      have hi : i = (0 : Fin (0 + 1)) := Fin.eq_zero i
      subst i
      exact ⟨p' * X (0 : Fin 2), by
        simp only [map_mul, endpointMap_X_zero, hp']⟩

-- The kernel equality is the existing coefficientwise Hankel-normalization
-- theorem. In particular this relation uses neither cancellation nor a domain.
private theorem quotient_coordinate_pow (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (n + 1)) :
    Ideal.Quotient.mk (hankelIdeal R n) (X i) ^ n =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))) ^ (n - i.val) *
        Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n)) ^ i.val := by
  have hexponent : n • coordinateExponent n i =
      (n - i.val) • coordinateExponent n (0 : Fin (n + 1)) +
        i.val • coordinateExponent n (Fin.last n) := by
    ext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [coordinateExponent, Finsupp.coe_smul, smul_eq_mul,
        Nat.mul_comm]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [coordinateExponent, Finsupp.coe_smul, smul_eq_mul,
        Nat.mul_comm]
  have hmem : (X i : Source R n) ^ n -
      X (0 : Fin (n + 1)) ^ (n - i.val) * X (Fin.last n) ^ i.val ∈
        hankelIdeal R n := by
    rw [hankelIdeal_eq_ker R n hn]
    change rncMap R n ((X i) ^ n -
      X (0 : Fin (n + 1)) ^ (n - i.val) * X (Fin.last n) ^ i.val) = 0
    simp only [map_sub, map_mul, map_pow, rncMap_X, monomial_pow, one_pow,
      monomial_mul_monomial, one_mul]
    rw [hexponent, sub_self]
  simpa only [map_pow, map_mul] using
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hmem

/-- For every commutative coefficient ring and degree, the Hankel quotient is
integral over the two-variable polynomial ring through the endpoint map. -/
theorem endpointMap_isIntegral (n : ℕ) :
    (endpointMap (R := R) n).IsIntegral := by
  by_cases hn : n = 0
  · subst n
    exact (endpointMap (R := R) 0).isIntegral_of_surjective endpointMap_zero_surjective
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hX (i : Fin (n + 1)) :
      (endpointMap (R := R) n).IsIntegralElem
        (Ideal.Quotient.mk (hankelIdeal R n) (X i)) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C
      (X (0 : Fin 2) ^ (n - i.val) * X (1 : Fin 2) ^ i.val),
      Polynomial.monic_X_pow_sub_C _ hn, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    simp only [map_mul, map_pow, endpointMap_X_zero, endpointMap_X_one,
      quotient_coordinate_pow n hn' i, sub_self]
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa only [endpointMap_C] using
        (endpointMap (R := R) n).isIntegralElem_map (x := C r)
  | add p q hp hq =>
      simpa only [map_add] using hp.add (endpointMap (R := R) n) hq
  | mul_X p i hp =>
      simpa only [map_mul] using hp.mul (endpointMap (R := R) n) (hX i)

/-- The Hankel quotient is a finite module over the two-variable polynomial
ring through the endpoint map, for every degree. -/
theorem endpointMap_finite (n : ℕ) :
    (endpointMap (R := R) n).Finite := by
  by_cases hn : n = 0
  · subst n
    exact RingHom.Finite.of_surjective _ endpointMap_zero_surjective
  apply (endpointMap_isIntegral (R := R) n).to_finite
  have hC : (MvPolynomial.C : R →+* Source R n).FiniteType := by
    change (algebraMap R (Source R n)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hcomp : (endpointMap (R := R) n).comp MvPolynomial.C =
      (Ideal.Quotient.mk (hankelIdeal R n)).comp MvPolynomial.C := by
    ext r
    exact endpointMap_C n r
  apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
  rw [hcomp]
  exact (RingHom.FiniteType.of_surjective
    (Ideal.Quotient.mk (hankelIdeal R n)) Ideal.Quotient.mk_surjective).comp hC

/-- In positive degree the endpoint map is injective, without any domain or
nontriviality assumption on the coefficient ring. -/
theorem endpointMap_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (endpointMap (R := R) n) := by
  let f : (Source R n ⧸ hankelIdeal R n) →+* Target R :=
    Ideal.Quotient.lift (hankelIdeal R n) (rncMap R n)
      (fun p hp ↦ hankelIdeal_le_ker R n hp)
  have hmk (p : Source R n) :
      f (Ideal.Quotient.mk (hankelIdeal R n) p) = rncMap R n p := by
    exact Ideal.Quotient.lift_mk (hankelIdeal R n) (rncMap R n)
      (fun p hp ↦ hankelIdeal_le_ker R n hp) (a := p)
  have hcomp :
      f.comp (endpointMap (R := R) n) =
        (MvPolynomial.expand n (R := R) (σ := Fin 2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (endpointMap (R := R) n (C r)) = MvPolynomial.expand n (C r)
      rw [endpointMap_C, hmk, rncMap_C, MvPolynomial.expand_C]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change f (endpointMap (R := R) n (X (0 : Fin 2))) =
          MvPolynomial.expand n (X (0 : Fin 2))
        rw [endpointMap_X_zero, hmk, rncMap_X, MvPolynomial.expand_X]
        simp [coordinateExponent, X_pow_eq_monomial]
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change f (endpointMap (R := R) n (X (1 : Fin 2))) =
          MvPolynomial.expand n (X (1 : Fin 2))
        rw [endpointMap_X_one, hmk, rncMap_X, MvPolynomial.expand_X]
        simp [coordinateExponent, X_pow_eq_monomial]
  have hinj : Function.Injective (f.comp (endpointMap (R := R) n)) := by
    rw [hcomp]
    exact MvPolynomial.expand_injective (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact Function.Injective.of_comp (f := f) (g := endpointMap (R := R) n) hinj

end

end

end ToricIdeals.RationalNormalCurve
