/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ToricIdeals.RationalNormalCurve

/-!
# Coordinate cancellation and boundary models for Hankel quotients

These models use the Hankel presentation and generic polynomial and quotient
APIs, independently of the quotient coordinate-regularity theorem.

Over `ZMod 1`, every degree gives a subsingleton quotient, so multiplication
on either side is injective. Over the integers at degree zero, the quotient
map from the full one-variable polynomial ring is injective: the variable
and `X₀ - 1` remain nonzero, although the parametrization kills `X₀ - 1`.
Over `ZMod 4` at degree one, the full two-variable polynomial quotient
retains two distinct nonzero endpoint classes. Generic polynomial-variable
cancellation applies even over these nonreduced coefficients.

In degree two, the constant class `2` over `ZMod 4` is nonzero with square
zero. The constant classes `(1, 0)` and `(0, 1)` over `ℤ × ℤ` are nonzero
with product zero. Over the integers, zero and one are distinct quotient
classes and all three coordinates, including the interior coordinate, are
nonzero. These checks do not infer coordinate cancellation from a domain
or reducedness assumption.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  Hankel ideal, the parametrized coordinate images and the ideal-kernel
  inclusion. The constant computations use the same generic monoid-algebra
  APIs as the rational-normal-curve domain and reducedness models.
* Mathlib contributors, multivariate-polynomial coefficients and variable
  cancellation, monoid-algebra exponent maps, and quotients by bottom ideals.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.CoordinateRegularityModels

noncomputable section

private theorem zero_coefficients_all_degrees_subsingleton (n : ℕ) :
    Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) := by
  have hone : (1 : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) n))
        (Subsingleton.elim (1 : Source (ZMod 1) n) 0)
  exact subsingleton_of_zero_eq_one hone.symm

private theorem zero_coefficients_all_degrees_multiplication_injective
    (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective
        (fun q : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n =>
          Ideal.Quotient.mk (hankelIdeal (ZMod 1) n) (X i) * q) ∧
      Function.Injective
        (fun q : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n =>
          q * Ideal.Quotient.mk (hankelIdeal (ZMod 1) n) (X i)) := by
  let : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
    zero_coefficients_all_degrees_subsingleton n
  constructor <;> intro a b _ <;> exact Subsingleton.elim a b

private theorem integer_degree_zero_full_polynomial :
    hankelIdeal ℤ 0 = ⊥ ∧
      Function.Injective (Ideal.Quotient.mk (hankelIdeal ℤ 0)) := by
  refine ⟨hankelIdeal_zero ℤ, ?_⟩
  rw [hankelIdeal_zero]
  intro p q hpq
  have h := congrArg (RingEquiv.quotientBot (Source ℤ 0)) hpq
  simpa only [RingEquiv.quotientBot_mk] using h

/-- At degree zero, the variable and `X₀ - 1` are nonzero in the Hankel quotient,
although the monomial parametrization sends `X₀ - 1` to zero. -/
public theorem integer_degree_zero_nonzero_variable_and_kernel_element :
    Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1) - C 1) ≠ 0 ∧
      rncMap ℤ 0 (X (0 : Fin 1) - C 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hpoly : (X (0 : Fin 1) : Source ℤ 0) = 0 :=
      integer_degree_zero_full_polynomial.2 (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (0 : Fin 1) hpoly
  · intro hzero
    have hpoly : (X (0 : Fin 1) - C 1 : Source ℤ 0) = 0 :=
      integer_degree_zero_full_polynomial.2 (by simpa only [map_zero] using hzero)
    have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
    have hcoeff := congrArg
      (fun p : Source ℤ 0 => p.coeff (Finsupp.single 0 1)) hpoly
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_same,
      MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
    simp at hcoeff
  · simp [rncMap_X, coordinateExponent]

private theorem integer_degree_zero_variable_cancellation (p q : Source ℤ 0) :
    (X (0 : Fin 1) * p = X (0 : Fin 1) * q ↔ p = q) ∧
      (p * X (0 : Fin 1) = q * X (0 : Fin 1) ↔ p = q) := by
  exact ⟨MvPolynomial.X_mul_cancel_left_iff, MvPolynomial.X_mul_cancel_right_iff⟩

private theorem mod_four_degree_one_full_polynomial :
    hankelIdeal (ZMod 4) 1 = ⊥ ∧
      Function.Injective (Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1)) := by
  refine ⟨hankelIdeal_one (ZMod 4), ?_⟩
  rw [hankelIdeal_one]
  intro p q hpq
  have h := congrArg (RingEquiv.quotientBot (Source (ZMod 4) 1)) hpq
  simpa only [RingEquiv.quotientBot_mk] using h

private theorem mod_four_degree_one_endpoints_distinct :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1) (X (0 : Fin 2)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1) (X (Fin.last 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1) (X (0 : Fin 2)) ≠
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1) (X (Fin.last 1)) := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hpoly : (X (0 : Fin 2) : Source (ZMod 4) 1) = 0 :=
      mod_four_degree_one_full_polynomial.2 (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (0 : Fin 2) hpoly
  · intro hzero
    have hpoly : (X (Fin.last 1) : Source (ZMod 4) 1) = 0 :=
      mod_four_degree_one_full_polynomial.2 (by simpa only [map_zero] using hzero)
    exact MvPolynomial.X_ne_zero (Fin.last 1) hpoly
  · intro heq
    have hpoly := mod_four_degree_one_full_polynomial.2 heq
    have hindex := MvPolynomial.X_injective hpoly
    exact (by decide : (0 : Fin 2) ≠ Fin.last 1) hindex

private theorem mod_four_degree_one_variable_cancellation (i : Fin 2)
    (p q : Source (ZMod 4) 1) :
    (X i * p = X i * q ↔ p = q) ∧ (p * X i = q * X i ↔ p = q) := by
  exact ⟨MvPolynomial.X_mul_cancel_left_iff, MvPolynomial.X_mul_cancel_right_iff⟩

private theorem mod_four_degree_two_nonzero_square_zero :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0 := by
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨?_, ?_⟩
  · intro hzero
    have hker := hankelIdeal_le_ker (ZMod 4) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change rncMap (ZMod 4) 2 (C (2 : ZMod 4)) = 0 at hker
    rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply] at hker
    change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 (2 : ZMod 4)) = 0 at hker
    rw [AddMonoidAlgebra.mapDomain_single, map_zero] at hker
    change (C (2 : ZMod 4) : Target (ZMod 4)) = 0 at hker
    exact hne (MvPolynomial.C_eq_zero.mp hker)
  · simpa only [map_pow, map_zero] using
      congrArg (fun c : ZMod 4 => Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C c)) hsq

private theorem integer_product_degree_two_orthogonal_constants :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  have hleft : ((1, 0) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.fst h)
  have hright : ((0, 1) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have hprod : ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by ext <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change rncMap (ℤ × ℤ) 2 (C ((1, 0) : ℤ × ℤ)) = 0 at hker
    rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply] at hker
    change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 ((1, 0) : ℤ × ℤ)) = 0 at hker
    rw [AddMonoidAlgebra.mapDomain_single, map_zero] at hker
    change (C ((1, 0) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 at hker
    exact hleft (MvPolynomial.C_eq_zero.mp hker)
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change rncMap (ℤ × ℤ) 2 (C ((0, 1) : ℤ × ℤ)) = 0 at hker
    rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply] at hker
    change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 ((0, 1) : ℤ × ℤ)) = 0 at hker
    rw [AddMonoidAlgebra.mapDomain_single, map_zero] at hker
    change (C ((0, 1) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 at hker
    exact hright (MvPolynomial.C_eq_zero.mp hker)
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ => Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c)) hprod

private theorem integer_degree_two_zero_ne_one :
    (0 : Source ℤ 2 ⧸ hankelIdeal ℤ 2) ≠ 1 := by
  intro hzero
  have hone : Ideal.Quotient.mk (hankelIdeal ℤ 2) (1 : Source ℤ 2) = 0 := by
    simpa only [map_one] using hzero.symm
  have hker := hankelIdeal_le_ker ℤ 2 (Ideal.Quotient.eq_zero_iff_mem.mp hone)
  change rncMap ℤ 2 1 = 0 at hker
  exact one_ne_zero (by simpa only [map_one] using hker)

private theorem integer_degree_two_coordinate_class_nonzero (i : Fin 3) :
    Ideal.Quotient.mk (hankelIdeal ℤ 2) (X i) ≠ 0 := by
  intro hzero
  have hker := hankelIdeal_le_ker ℤ 2 (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  change rncMap ℤ 2 (X i) = 0 at hker
  rw [rncMap_X] at hker
  have hcoeff := congrArg
    (fun p : Target ℤ => p.coeff (coordinateExponent 2 i)) hker
  simp at hcoeff


end

end ToricIdeals.RationalNormalCurve.CoordinateRegularityModels
