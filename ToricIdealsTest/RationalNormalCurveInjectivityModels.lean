/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve

/-!
# Injectivity boundaries for the rational-normal-curve parametrization

These examples concern the map on the full polynomial source, rather than
its restriction to terminal exponents or its descent to a Hankel quotient.
At degree zero, the sole variable and the constant one are distinct over
both the integers and `ZMod 4`, but have the same image. At degree one,
coefficients with nilpotents (`ZMod 4`) or zero divisors (`ℤ × ℤ`) still give
an injective map with two distinct source variables.

For conics and cubics, the distinct polynomials `X₀ X₂` and `X₁²` have the
same coefficient-one target monomial over `ℤ`, `ZMod 2`, `ZMod 4` and
`ℤ × ℤ`. The corresponding source exponents remain distinct independently
of the coefficients. A further family over `ZMod 4` exhibits the first
Hankel collision in every degree at least two, with target exponent
`(2*n-2, 2)`. In characteristic two the conic relation is nonzero: its
outer coefficient is one, even though subtraction equals addition. The
two in the inner source exponent is a natural exponent, not a coefficient.

With coefficients in `ZMod 1`, the source and target are subsingleton in
every degree, so the polynomial map is injective. The degree-zero and conic
examples retain noninjective exponent maps while their polynomials collapse.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`: the
  parametrization, degree-one injectivity, degree-zero strict kernel
  inclusion, and the Hankel exponent collision and energy argument.
* Mathlib contributors: multivariate-polynomial monomial and coefficient
  APIs, additive monoid-algebra map-domain APIs, and the canonical modular
  and product coefficient-ring instances.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdealsTest.RationalNormalCurveInjectivityModels

noncomputable section

private theorem degree_zero_exponents_collide :
    (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 ∧
      rncExponent 0 (Finsupp.single (0 : Fin 1) 1) = rncExponent 0 0 ∧
      rncExponent 0 (Finsupp.single (0 : Fin 1) 1) = 0 := by
  refine ⟨by simp, ?_, ?_⟩ <;>
    simp [rncExponent_single, coordinateExponent]

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

private theorem integer_degree_zero_polynomials_collide :
    (X (0 : Fin 1) : Source ℤ 0) ≠ C 1 ∧
      rncMap ℤ 0 (X (0 : Fin 1)) = rncMap ℤ 0 (C 1) ∧
      rncMap ℤ 0 (X (0 : Fin 1)) = 1 ∧
      rncMap ℤ 0 (C 1) = 1 ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) ∧
      ¬ Function.Injective (rncMap ℤ 0) := by
  have hne : (X (0 : Fin 1) : Source ℤ 0) ≠ C 1 := by
    intro h
    have hs := degree_zero_exponents_collide.1
    have hcoeff := congrArg
      (fun f : Source ℤ 0 => f.coeff (Finsupp.single (0 : Fin 1) 1)) h
    rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
    exact one_ne_zero hcoeff
  have hX : rncMap ℤ 0 (X (0 : Fin 1)) = 1 := by
    simp [rncMap_X, coordinateExponent]
  have hC : rncMap ℤ 0 (C 1) = 1 := by simp
  refine ⟨hne, hX.trans hC.symm, hX, hC, hankelIdeal_zero_lt_ker ℤ, ?_⟩
  intro hinj
  exact hne (hinj (hX.trans hC.symm))

private theorem mod_four_degree_zero_polynomials_collide :
    (X (0 : Fin 1) : Source (ZMod 4) 0) ≠ C 1 ∧
      rncMap (ZMod 4) 0 (X (0 : Fin 1)) = rncMap (ZMod 4) 0 (C 1) ∧
      rncMap (ZMod 4) 0 (X (0 : Fin 1)) = 1 ∧
      rncMap (ZMod 4) 0 (C 1) = 1 ∧
      hankelIdeal (ZMod 4) 0 < RingHom.ker (rncMap (ZMod 4) 0) ∧
      ¬ Function.Injective (rncMap (ZMod 4) 0) := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have hne : (X (0 : Fin 1) : Source (ZMod 4) 0) ≠ C 1 := by
    intro h
    have hs := degree_zero_exponents_collide.1
    have hcoeff := congrArg
      (fun f : Source (ZMod 4) 0 => f.coeff (Finsupp.single (0 : Fin 1) 1)) h
    rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
    exact one_ne_zero hcoeff
  have hX : rncMap (ZMod 4) 0 (X (0 : Fin 1)) = 1 := by
    simp [rncMap_X, coordinateExponent]
  have hC : rncMap (ZMod 4) 0 (C 1) = 1 := by simp
  refine ⟨hne, hX.trans hC.symm, hX, hC, hankelIdeal_zero_lt_ker (ZMod 4), ?_⟩
  intro hinj
  exact hne (hinj (hX.trans hC.symm))

private theorem mod_four_degree_one_injective_with_nilpotents :
    Function.Injective (rncMap (ZMod 4) 1) ∧
      (X (0 : Fin 2) : Source (ZMod 4) 1) ≠ X (1 : Fin 2) ∧
      (C (2 : ZMod 4) : Source (ZMod 4) 1) ≠ 0 ∧
      (C (2 : ZMod 4) : Source (ZMod 4) 1) ^ 2 = 0 := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨rncMap_one_injective (ZMod 4), ?_, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective h)
  · exact fun h => htwo (MvPolynomial.C_eq_zero.mp h)
  · rw [← MvPolynomial.C_pow, hsq, MvPolynomial.C_0]

private theorem integer_product_degree_one_injective_with_zero_divisors :
    Function.Injective (rncMap (ℤ × ℤ) 1) ∧
      (X (0 : Fin 2) : Source (ℤ × ℤ) 1) ≠ X (1 : Fin 2) ∧
      (C ((1, 0) : ℤ × ℤ) : Source (ℤ × ℤ) 1) ≠ 0 ∧
      (C ((0, 1) : ℤ × ℤ) : Source (ℤ × ℤ) 1) ≠ 0 ∧
      (C ((1, 0) : ℤ × ℤ) : Source (ℤ × ℤ) 1) * C ((0, 1) : ℤ × ℤ) = 0 := by
  have hleft : ((1, 0) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.fst h)
  have hright : ((0, 1) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have hprod : ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by ext <;> simp
  refine ⟨rncMap_one_injective (ℤ × ℤ), ?_, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective h)
  · exact fun h => hleft (MvPolynomial.C_eq_zero.mp h)
  · exact fun h => hright (MvPolynomial.C_eq_zero.mp h)
  · rw [← MvPolynomial.C_mul, hprod, MvPolynomial.C_0]

private theorem integer_conic_polynomials_collide :
    (X (0 : Fin 3) * X (2 : Fin 3) : Source ℤ 2) ≠ X (1 : Fin 3) ^ 2 ∧
      rncMap ℤ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        rncMap ℤ 2 (X (1 : Fin 3) ^ 2) ∧
      rncMap ℤ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℤ) ∧
      ¬ Function.Injective (rncMap ℤ 2) := by
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source ℤ 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source ℤ 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 3) * X (2 : Fin 3) : Source ℤ 2) ≠ X (1 : Fin 3) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact conic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap ℤ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) 1 :
        Target ℤ) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap ℤ 2 (X (1 : Fin 3) ^ 2) =
      (monomial (rncExponent 2 (Finsupp.single (1 : Fin 3) 2)) 1 : Target ℤ) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap ℤ 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      rncMap ℤ 2 (X (1 : Fin 3) ^ 2) := by
    rw [hmapP, hmapQ, conic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, conic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem mod_two_conic_polynomials_collide :
    (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 2) 2) ≠ X (1 : Fin 3) ^ 2 ∧
      rncMap (ZMod 2) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        rncMap (ZMod 2) 2 (X (1 : Fin 3) ^ 2) ∧
      rncMap (ZMod 2) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ZMod 2)) ∧
      ¬ Function.Injective (rncMap (ZMod 2) 2) := by
  let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 2) 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source (ZMod 2) 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 2) 2) ≠ X (1 : Fin 3) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact conic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ZMod 2) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) 1 :
        Target (ZMod 2)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ZMod 2) 2 (X (1 : Fin 3) ^ 2) =
      (monomial (rncExponent 2 (Finsupp.single (1 : Fin 3) 2)) 1 : Target (ZMod 2)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ZMod 2) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      rncMap (ZMod 2) 2 (X (1 : Fin 3) ^ 2) := by
    rw [hmapP, hmapQ, conic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, conic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem mod_four_conic_polynomials_collide :
    (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 4) 2) ≠ X (1 : Fin 3) ^ 2 ∧
      rncMap (ZMod 4) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        rncMap (ZMod 4) 2 (X (1 : Fin 3) ^ 2) ∧
      rncMap (ZMod 4) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ZMod 4)) ∧
      ¬ Function.Injective (rncMap (ZMod 4) 2) := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 4) 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source (ZMod 4) 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 4) 2) ≠ X (1 : Fin 3) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact conic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ZMod 4) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) 1 :
        Target (ZMod 4)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ZMod 4) 2 (X (1 : Fin 3) ^ 2) =
      (monomial (rncExponent 2 (Finsupp.single (1 : Fin 3) 2)) 1 : Target (ZMod 4)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ZMod 4) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      rncMap (ZMod 4) 2 (X (1 : Fin 3) ^ 2) := by
    rw [hmapP, hmapQ, conic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, conic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem integer_product_conic_polynomials_collide :
    (X (0 : Fin 3) * X (2 : Fin 3) : Source (ℤ × ℤ) 2) ≠ X (1 : Fin 3) ^ 2 ∧
      rncMap (ℤ × ℤ) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        rncMap (ℤ × ℤ) 2 (X (1 : Fin 3) ^ 2) ∧
      rncMap (ℤ × ℤ) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 2 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ℤ × ℤ)) ∧
      ¬ Function.Injective (rncMap (ℤ × ℤ) 2) := by
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source (ℤ × ℤ) 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source (ℤ × ℤ) 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 3) * X (2 : Fin 3) : Source (ℤ × ℤ) 2) ≠ X (1 : Fin 3) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact conic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ℤ × ℤ) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      (monomial
        (rncExponent 2
          (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) 1 :
        Target (ℤ × ℤ)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ℤ × ℤ) 2 (X (1 : Fin 3) ^ 2) =
      (monomial (rncExponent 2 (Finsupp.single (1 : Fin 3) 2)) 1 : Target (ℤ × ℤ)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ℤ × ℤ) 2 (X (0 : Fin 3) * X (2 : Fin 3)) =
      rncMap (ℤ × ℤ) 2 (X (1 : Fin 3) ^ 2) := by
    rw [hmapP, hmapQ, conic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, conic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem integer_cubic_polynomials_collide :
    (X (0 : Fin 4) * X (2 : Fin 4) : Source ℤ 3) ≠ X (1 : Fin 4) ^ 2 ∧
      rncMap ℤ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        rncMap ℤ 3 (X (1 : Fin 4) ^ 2) ∧
      rncMap ℤ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target ℤ) ∧
      ¬ Function.Injective (rncMap ℤ 3) := by
  have hP : (X (0 : Fin 4) * X (2 : Fin 4) : Source ℤ 3) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 4) ^ 2 : Source ℤ 3) =
      monomial (Finsupp.single (1 : Fin 4) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 4) * X (2 : Fin 4) : Source ℤ 3) ≠ X (1 : Fin 4) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact cubic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap ℤ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1)) 1 :
        Target ℤ) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap ℤ 3 (X (1 : Fin 4) ^ 2) =
      (monomial (rncExponent 3 (Finsupp.single (1 : Fin 4) 2)) 1 : Target ℤ) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap ℤ 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      rncMap ℤ 3 (X (1 : Fin 4) ^ 2) := by
    rw [hmapP, hmapQ, cubic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, cubic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem mod_two_cubic_polynomials_collide :
    (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 2) 3) ≠ X (1 : Fin 4) ^ 2 ∧
      rncMap (ZMod 2) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        rncMap (ZMod 2) 3 (X (1 : Fin 4) ^ 2) ∧
      rncMap (ZMod 2) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ZMod 2)) ∧
      ¬ Function.Injective (rncMap (ZMod 2) 3) := by
  let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  have hP : (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 2) 3) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 4) ^ 2 : Source (ZMod 2) 3) =
      monomial (Finsupp.single (1 : Fin 4) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 2) 3) ≠ X (1 : Fin 4) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact cubic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ZMod 2) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1)) 1 :
        Target (ZMod 2)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ZMod 2) 3 (X (1 : Fin 4) ^ 2) =
      (monomial (rncExponent 3 (Finsupp.single (1 : Fin 4) 2)) 1 : Target (ZMod 2)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ZMod 2) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      rncMap (ZMod 2) 3 (X (1 : Fin 4) ^ 2) := by
    rw [hmapP, hmapQ, cubic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, cubic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem mod_four_cubic_polynomials_collide :
    (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 4) 3) ≠ X (1 : Fin 4) ^ 2 ∧
      rncMap (ZMod 4) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        rncMap (ZMod 4) 3 (X (1 : Fin 4) ^ 2) ∧
      rncMap (ZMod 4) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ZMod 4)) ∧
      ¬ Function.Injective (rncMap (ZMod 4) 3) := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have hP : (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 4) 3) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 4) ^ 2 : Source (ZMod 4) 3) =
      monomial (Finsupp.single (1 : Fin 4) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 4) * X (2 : Fin 4) : Source (ZMod 4) 3) ≠ X (1 : Fin 4) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact cubic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ZMod 4) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1)) 1 :
        Target (ZMod 4)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ZMod 4) 3 (X (1 : Fin 4) ^ 2) =
      (monomial (rncExponent 3 (Finsupp.single (1 : Fin 4) 2)) 1 : Target (ZMod 4)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ZMod 4) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      rncMap (ZMod 4) 3 (X (1 : Fin 4) ^ 2) := by
    rw [hmapP, hmapQ, cubic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, cubic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem integer_product_cubic_polynomials_collide :
    (X (0 : Fin 4) * X (2 : Fin 4) : Source (ℤ × ℤ) 3) ≠ X (1 : Fin 4) ^ 2 ∧
      rncMap (ℤ × ℤ) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        rncMap (ℤ × ℤ) 3 (X (1 : Fin 4) ^ 2) ∧
      rncMap (ℤ × ℤ) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
        (monomial
          (Finsupp.single (0 : Fin 2) 4 + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ℤ × ℤ)) ∧
      ¬ Function.Injective (rncMap (ℤ × ℤ) 3) := by
  have hP : (X (0 : Fin 4) * X (2 : Fin 4) : Source (ℤ × ℤ) 3) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 4) ^ 2 : Source (ℤ × ℤ) 3) =
      monomial (Finsupp.single (1 : Fin 4) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hne :
      (X (0 : Fin 4) * X (2 : Fin 4) : Source (ℤ × ℤ) 3) ≠ X (1 : Fin 4) ^ 2 := by
    rw [hP, hQ]
    intro h
    exact cubic_exponents_collide.1
      (MvPolynomial.monomial_left_injective one_ne_zero h)
  have hmapP : rncMap (ℤ × ℤ) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      (monomial
        (rncExponent 3
          (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1)) 1 :
        Target (ℤ × ℤ)) := by
    rw [hP, rncMap_monomial]
  have hmapQ : rncMap (ℤ × ℤ) 3 (X (1 : Fin 4) ^ 2) =
      (monomial (rncExponent 3 (Finsupp.single (1 : Fin 4) 2)) 1 : Target (ℤ × ℤ)) := by
    rw [hQ, rncMap_monomial]
  have heq : rncMap (ℤ × ℤ) 3 (X (0 : Fin 4) * X (2 : Fin 4)) =
      rncMap (ℤ × ℤ) 3 (X (1 : Fin 4) ^ 2) := by
    rw [hmapP, hmapQ, cubic_exponents_collide.2.1]
  refine ⟨hne, heq, ?_, ?_⟩
  · rw [hmapP, cubic_exponents_collide.2.2]
  · intro hinj
    exact hne (hinj heq)

private theorem mod_four_higher_degree_polynomials_collide (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : MinorIndex n, p.1.1.val = 0 ∧ p.1.2.val = 1 ∧
      (monomial (outerExponent n p) (1 : ZMod 4) : Source (ZMod 4) n) ≠
        monomial (innerExponent n p) 1 ∧
      rncMap (ZMod 4) n (monomial (outerExponent n p) 1) =
        rncMap (ZMod 4) n (monomial (innerExponent n p) 1) ∧
      rncMap (ZMod 4) n (monomial (outerExponent n p) 1) =
        (monomial
          (Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2) 1 :
          Target (ZMod 4)) := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let p : MinorIndex n := ⟨(a, b), by change 0 < 1; decide⟩
  have htarget : rncExponent n (outerExponent n p) =
      Finsupp.single (0 : Fin 2) (2 * n - 2) + Finsupp.single (1 : Fin 2) 2 := by
    simp only [outerExponent, map_add, rncExponent_single]
    ext q
    fin_cases q <;> simp [coordinateExponent, p, a, b]
    omega
  refine ⟨p, rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    have hexponent := MvPolynomial.monomial_left_injective one_ne_zero h
    have henergy := inner_energy_lt_outer_energy n p
    rw [hexponent] at henergy
    exact (Nat.lt_irrefl _) henergy
  · rw [rncMap_monomial, rncMap_monomial, rncExponent_outer_eq_inner]
  · rw [rncMap_monomial, htarget]

private theorem mod_two_conic_relation_nonzero :
    let f : Source (ZMod 2) 2 := X (0 : Fin 3) * X (2 : Fin 3) - X (1 : Fin 3) ^ 2
    f ≠ 0 ∧
      f.coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) = 1 ∧
      (1 : ZMod 2) ≠ 0 ∧
      rncMap (ZMod 2) 2 f = 0 ∧
      f = X (0 : Fin 3) * X (2 : Fin 3) + X (1 : Fin 3) ^ 2 := by
  let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  let f : Source (ZMod 2) 2 := X (0 : Fin 3) * X (2 : Fin 3) - X (1 : Fin 3) ^ 2
  change f ≠ 0 ∧
    f.coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) = 1 ∧
    (1 : ZMod 2) ≠ 0 ∧ rncMap (ZMod 2) 2 f = 0 ∧
    f = X (0 : Fin 3) * X (2 : Fin 3) + X (1 : Fin 3) ^ 2
  have hP : (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 2) 2) =
      monomial (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hQ : (X (1 : Fin 3) ^ 2 : Source (ZMod 2) 2) =
      monomial (Finsupp.single (1 : Fin 3) 2) 1 := MvPolynomial.X_pow_eq_monomial
  have hcoeff :
      f.coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) = 1 := by
    dsimp only [f]
    rw [hP, hQ, MvPolynomial.coeff_sub]
    simp [MvPolynomial.coeff_monomial, Ne.symm conic_exponents_collide.1]
  have hone : -(1 : ZMod 2) = 1 := by decide
  have hneg : -(X (1 : Fin 3) ^ 2 : Source (ZMod 2) 2) = X (1 : Fin 3) ^ 2 := by
    calc
      -(X (1 : Fin 3) ^ 2 : Source (ZMod 2) 2) =
          -monomial (Finsupp.single (1 : Fin 3) 2) (1 : ZMod 2) := by rw [hQ]
      _ = monomial (Finsupp.single (1 : Fin 3) 2) (-(1 : ZMod 2)) :=
        (map_neg (monomial (Finsupp.single (1 : Fin 3) 2)) (1 : ZMod 2)).symm
      _ = X (1 : Fin 3) ^ 2 := by rw [hone, ← hQ]
  refine ⟨?_, hcoeff, one_ne_zero, ?_, ?_⟩
  · intro hzero
    have h := congrArg
      (fun g : Source (ZMod 2) 2 =>
        g.coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) hzero
    rw [hcoeff, AddMonoidAlgebra.coeff_zero] at h
    exact one_ne_zero h
  · dsimp only [f]
    rw [map_sub, mod_two_conic_polynomials_collide.2.1, sub_self]
  · dsimp only [f]
    rw [sub_eq_add_neg, hneg]

private theorem zero_coefficients_polynomials_subsingleton (n : ℕ) :
    Subsingleton (Source (ZMod 1) n) ∧ Subsingleton (Target (ZMod 1)) := by
  exact ⟨inferInstance, inferInstance⟩

private theorem zero_coefficients_all_degrees_injective (n : ℕ) :
    Function.Injective (rncMap (ZMod 1) n) := by
  intro f g _
  exact Subsingleton.elim f g

private theorem zero_coefficients_degree_zero_injective_with_colliding_exponents :
    Function.Injective (rncMap (ZMod 1) 0) ∧
      ¬ Function.Injective (rncExponent 0) ∧
      (X (0 : Fin 1) : Source (ZMod 1) 0) = C 1 ∧
      (X (0 : Fin 1) : Source (ZMod 1) 0) = 0 ∧
      (C 1 : Source (ZMod 1) 0) = 0 := by
  refine ⟨zero_coefficients_all_degrees_injective 0, ?_,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  intro hinj
  exact degree_zero_exponents_collide.1 (hinj degree_zero_exponents_collide.2.1)

private theorem zero_coefficients_conic_injective_with_colliding_exponents :
    Function.Injective (rncMap (ZMod 1) 2) ∧
      ¬ Function.Injective (rncExponent 2) ∧
      (X (0 : Fin 3) * X (2 : Fin 3) : Source (ZMod 1) 2) = X (1 : Fin 3) ^ 2 ∧
      (X (0 : Fin 3) : Source (ZMod 1) 2) = X (1 : Fin 3) ∧
      (X (0 : Fin 3) : Source (ZMod 1) 2) = 0 := by
  refine ⟨zero_coefficients_all_degrees_injective 2, ?_,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  intro hinj
  exact conic_exponents_collide.1 (hinj conic_exponents_collide.2.1)

end

end ToricIdealsTest.RationalNormalCurveInjectivityModels
