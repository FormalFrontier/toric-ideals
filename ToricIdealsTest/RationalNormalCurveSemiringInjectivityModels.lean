/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve

/-!
# Semiring and universe boundaries for the rational-normal-curve map

These examples use the full polynomial source with natural-number coefficients.
At degree zero, the sole variable and the constant one are distinct but both
map to one. At degree one, the parametrization is injective and the two source
variables are distinct. For conics and cubics, `X₀ X₂` and `X₁²` are distinct
coefficient-one monomials with common target exponents `(2, 2)` and `(4, 2)`.
The first pair of columns gives the same collision in every degree `n ≥ 2`,
with target exponent `(2*n-2, 2)`.

These collisions use additive exponent maps and natural-number energy, without
subtracting source polynomials. The coefficient one is nonzero in `ℕ`; the
natural two in `X₁²` is an exponent, not a coefficient. The coefficient and
variable laws are also exercised on the degree-two polynomial `C 3 * X₁`.

The degree-one examples with coefficients in `ULift.{u} ℕ` and
`ULift.{u} (ZMod 4)` use the canonical polynomial source and stock coefficient
instances in arbitrary universes. The latter source contains the nonzero
square-zero constant `C (ULift.up 2)` despite injectivity of the map.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`: the polynomial
  parametrization, its coefficient and variable laws, degree-one injectivity,
  and the equal-exponent and decreasing-energy arguments for a pair of columns.
* Mathlib contributors: the multivariate-polynomial monomial and coefficient
  APIs, additive monoid-algebra map-domain API, and canonical natural-number,
  modular, and universe-lifted coefficient instances.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdealsTest.RationalNormalCurveSemiringInjectivityModels

noncomputable section

universe u

private theorem natural_coefficient_and_variable_images :
    (1 : ℕ) ≠ 0 ∧
      rncMap ℕ 2 (C 3) = (C 3 : Target ℕ) ∧
      rncMap ℕ 2 (X (1 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 :
          Target ℕ) ∧
      rncMap ℕ 2 (C 3 * X (1 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 3 :
          Target ℕ) := by
  have hX : rncMap ℕ 2 (X (1 : Fin 3)) =
      (monomial
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 :
        Target ℕ) := by
    simp [coordinateExponent]
  refine ⟨by decide, rncMap_C ℕ 2 3, hX, ?_⟩
  rw [map_mul, rncMap_C, hX, MvPolynomial.C_mul_monomial, mul_one]

private theorem natural_degree_zero_polynomials_collide :
    (X (0 : Fin 1) : Source ℕ 0) ≠ C 1 ∧
      rncMap ℕ 0 (X (0 : Fin 1)) = rncMap ℕ 0 (C 1) ∧
      rncMap ℕ 0 (X (0 : Fin 1)) = 1 ∧
      rncMap ℕ 0 (C 1) = 1 ∧
      ¬ Function.Injective (rncMap ℕ 0) := by
  have hone : (1 : ℕ) ≠ 0 := by decide
  have hne : (X (0 : Fin 1) : Source ℕ 0) ≠ C 1 := by
    intro h
    have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
    have hcoeff := congrArg
      (fun f : Source ℕ 0 => f.coeff (Finsupp.single (0 : Fin 1) 1)) h
    rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
    exact hone hcoeff
  have hX : rncMap ℕ 0 (X (0 : Fin 1)) = 1 := by
    simp [rncMap_X, coordinateExponent]
  have hC : rncMap ℕ 0 (C 1) = 1 := by simp
  refine ⟨hne, hX.trans hC.symm, hX, hC, ?_⟩
  intro hinj
  exact hne (hinj (hX.trans hC.symm))

private theorem natural_degree_one_injective :
    Function.Injective (rncMap ℕ 1) ∧
      (X (0 : Fin 2) : Source ℕ 1) ≠ X (1 : Fin 2) := by
  refine ⟨rncMap_one_injective ℕ, ?_⟩
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective h)

private theorem conic_exponents_collide :
    (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) ≠
        Finsupp.single (1 : Fin 3) 2 ∧
      rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) =
        rncExponent 2 (Finsupp.single (1 : Fin 3) 2) ∧
      rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) =
        Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2 := by
  let p : MinorIndex 2 := ⟨(0, 1), by decide⟩
  have houter : outerExponent 2 p =
      Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1 := rfl
  have hinner : innerExponent 2 p = Finsupp.single (1 : Fin 3) 2 := by
    change Finsupp.single (1 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 1 = _
    rw [← Finsupp.single_add]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have henergy := inner_energy_lt_outer_energy 2 p
    rw [houter, hinner, h] at henergy
    exact (Nat.lt_irrefl _) henergy
  · simpa only [houter, hinner] using rncExponent_outer_eq_inner 2 p
  · rw [map_add, rncExponent_single, rncExponent_single]
    ext q
    fin_cases q <;> simp [coordinateExponent]

private theorem cubic_exponents_collide :
    (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) ≠
        Finsupp.single (1 : Fin 4) 2 ∧
      rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) =
        rncExponent 3 (Finsupp.single (1 : Fin 4) 2) ∧
      rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) =
        Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2 := by
  let p : MinorIndex 3 := ⟨(0, 1), by decide⟩
  have houter : outerExponent 3 p =
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1 := rfl
  have hinner : innerExponent 3 p = Finsupp.single (1 : Fin 4) 2 := by
    change Finsupp.single (1 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 = _
    rw [← Finsupp.single_add]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have henergy := inner_energy_lt_outer_energy 3 p
    rw [houter, hinner, h] at henergy
    exact (Nat.lt_irrefl _) henergy
  · simpa only [houter, hinner] using rncExponent_outer_eq_inner 3 p
  · rw [map_add, rncExponent_single, rncExponent_single]
    ext q
    fin_cases q <;> simp [coordinateExponent]

private theorem natural_conic_polynomials_collide :
    (X (0 : Fin 3) * X (2 : Fin 3) : Source ℕ 2) ≠ X (1 : Fin 3) ^ 2 ∧
      rncMap ℕ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        rncMap ℕ 2 (X (1 : Fin 3) ^ 2) ∧
      rncMap ℕ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      rncMap ℕ 2 (X (1 : Fin 3) ^ 2) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      ¬ Function.Injective (rncMap ℕ 2) := by
  have hone : (1 : ℕ) ≠ 0 := by decide
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source ℕ 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source ℕ 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne : (X (0 : Fin 3) * X (2 : Fin 3) : Source ℕ 2) ≠ X (1 : Fin 3) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact conic_exponents_collide.1 (MvPolynomial.monomial_left_injective hone h)
  have hmapP : rncMap ℕ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) 1 :
        Target ℕ) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap ℕ 2 (X (1 : Fin 3) ^ 2) =
      (monomial (rncExponent 2 (Finsupp.single (1 : Fin 3) 2)) 1 : Target ℕ) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap ℕ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      rncMap ℕ 2 (X (1 : Fin 3) ^ 2) := by
    rw [hmapP, hmapQ, conic_exponents_collide.2.1]
  have hcommon : rncMap ℕ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
        Target ℕ) := by
    rw [hmapP, conic_exponents_collide.2.2]
  refine ⟨hne, heq, hcommon, heq.symm.trans hcommon, ?_⟩
  intro hinj
  exact hne (hinj heq)

private theorem natural_cubic_polynomials_collide :
    (X (0 : Fin 4) * X (2 : Fin 4) : Source ℕ 3) ≠ X (1 : Fin 4) ^ 2 ∧
      rncMap ℕ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        rncMap ℕ 3 (X (1 : Fin 4) ^ 2) ∧
      rncMap ℕ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      rncMap ℕ 3 (X (1 : Fin 4) ^ 2) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      ¬ Function.Injective (rncMap ℕ 3) := by
  have hone : (1 : ℕ) ≠ 0 := by decide
  have hP : (X (0 : Fin 4) * X (2 : Fin 4) : Source ℕ 3) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 4) ^ 2 : Source ℕ 3) =
      monomial (Finsupp.single (1 : Fin 4) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne : (X (0 : Fin 4) * X (2 : Fin 4) : Source ℕ 3) ≠ X (1 : Fin 4) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact cubic_exponents_collide.1 (MvPolynomial.monomial_left_injective hone h)
  have hmapP : rncMap ℕ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1)) 1 :
        Target ℕ) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap ℕ 3 (X (1 : Fin 4) ^ 2) =
      (monomial (rncExponent 3 (Finsupp.single (1 : Fin 4) 2)) 1 : Target ℕ) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap ℕ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      rncMap ℕ 3 (X (1 : Fin 4) ^ 2) := by
    rw [hmapP, hmapQ, cubic_exponents_collide.2.1]
  have hcommon : rncMap ℕ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
        Target ℕ) := by
    rw [hmapP, cubic_exponents_collide.2.2]
  refine ⟨hne, heq, hcommon, heq.symm.trans hcommon, ?_⟩
  intro hinj
  exact hne (hinj heq)

private theorem natural_higher_degree_polynomials_collide (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : MinorIndex n, p.1.1.val = 0 ∧ p.1.2.val = 1 ∧
      outerExponent n p ≠ innerExponent n p ∧
      (monomial (outerExponent n p) (1 : ℕ) : Source ℕ n) ≠
        monomial (innerExponent n p) 1 ∧
      rncMap ℕ n (monomial (outerExponent n p) 1) =
        rncMap ℕ n (monomial (innerExponent n p) 1) ∧
      rncMap ℕ n (monomial (outerExponent n p) 1) =
        (monomial
          (Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      rncMap ℕ n (monomial (innerExponent n p) 1) =
        (monomial
          (Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℕ) ∧
      ¬ Function.Injective (rncMap ℕ n) := by
  have hone : (1 : ℕ) ≠ 0 := by decide
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let p : MinorIndex n := ⟨(a, b), by
    change 0 < 1
    decide⟩
  have hexponent : outerExponent n p ≠ innerExponent n p := by
    intro h
    have henergy := inner_energy_lt_outer_energy n p
    rw [h] at henergy
    exact (Nat.lt_irrefl _) henergy
  have hne : (monomial (outerExponent n p) (1 : ℕ) : Source ℕ n) ≠
      monomial (innerExponent n p) 1 := by
    intro h
    exact hexponent (MvPolynomial.monomial_left_injective hone h)
  have htarget : rncExponent n (outerExponent n p) =
      Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2 := by
    simp only [outerExponent, map_add, rncExponent_single]
    ext q
    fin_cases q <;> simp [coordinateExponent, p, a, b]
    omega
  have heq : rncMap ℕ n (monomial (outerExponent n p) 1) =
      rncMap ℕ n (monomial (innerExponent n p) 1) := by
    rw [rncMap_monomial, rncMap_monomial, rncExponent_outer_eq_inner]
  have hcommon : rncMap ℕ n (monomial (outerExponent n p) 1) =
      (monomial
        (Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2) 1 :
        Target ℕ) := by
    rw [rncMap_monomial, htarget]
  refine ⟨p, rfl, rfl, hexponent, hne, heq, hcommon, heq.symm.trans hcommon, ?_⟩
  intro hinj
  exact hne (hinj heq)

private theorem lifted_natural_degree_one_injective :
    Function.Injective (rncMap (ULift.{u} ℕ) 1) ∧
      (X (0 : Fin 2) : Source (ULift.{u} ℕ) 1) ≠ X (1 : Fin 2) := by
  refine ⟨rncMap_one_injective (ULift.{u} ℕ), ?_⟩
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective h)

private theorem lifted_mod_four_degree_one_injective_with_nilpotents :
    Function.Injective (rncMap (ULift.{u} (ZMod 4)) 1) ∧
      (X (0 : Fin 2) : Source (ULift.{u} (ZMod 4)) 1) ≠ X (1 : Fin 2) ∧
      (C (ULift.up (2 : ZMod 4)) : Source (ULift.{u} (ZMod 4)) 1) ≠ 0 ∧
      (C (ULift.up (2 : ZMod 4)) : Source (ULift.{u} (ZMod 4)) 1) ^ 2 = 0 := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have htwo : (ULift.up (2 : ZMod 4) : ULift.{u} (ZMod 4)) ≠ 0 := by
    intro h
    have hdown := congrArg ULift.down h
    change (2 : ZMod 4) = 0 at hdown
    exact (by decide : (2 : ZMod 4) ≠ 0) hdown
  have hsq : (ULift.up (2 : ZMod 4) : ULift.{u} (ZMod 4)) ^ 2 = 0 := by
    apply ULift.ext
    change (2 : ZMod 4) ^ 2 = 0
    decide
  refine ⟨rncMap_one_injective (ULift.{u} (ZMod 4)), ?_, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective h)
  · exact fun h => htwo (MvPolynomial.C_eq_zero.mp h)
  · rw [← MvPolynomial.C_pow, hsq, MvPolynomial.C_0]

end

end ToricIdealsTest.RationalNormalCurveSemiringInjectivityModels
