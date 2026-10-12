/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
public import ToricIdeals.RationalNormalCurve

/-!
# Reduced and nonreduced rational-normal-curve coordinate rings

The integer-product coefficient ring is reduced but not a domain. Its two
orthogonal nonzero idempotents survive as constant classes in the degree-zero
and degree-two Hankel quotients. Both quotients are reduced but not domains.
Degree zero uses the quotient by the bottom ideal; degree two uses the
quotient-to-range equivalence and reducedness of multivariate polynomial rings.

Over `ZMod 4`, the nonzero coefficient `2` has square zero. Its constant class
remains nonzero, with square zero, in the degree-zero and degree-two quotients.
Thus both quotients are nonreduced. Over the zero coefficient ring `ZMod 1`,
both quotients are reduced, but their units are zero and they are not domains.

The degree-zero integer quotient is reduced and retains nonzero classes of
`X₀` and `X₀ - 1`. Its Hankel ideal is strictly smaller than the parametrization
kernel, so degree-zero reducedness concerns the polynomial quotient, not the
parametrization range.

These are concrete models using the existing Hankel ideal and parametrization;
no equivalence between quotient reducedness and coefficient reducedness is
assumed. Constant-class arguments follow the rational-normal-curve domain
models by Formal Frontier Agents.
-/

open MvPolynomial
open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve

noncomputable section

/-- At degree zero, the integer coefficient ring and its Hankel quotient are reduced.
The classes of the sole variable `X₀` and of `X₀ - 1` are nonzero, and the Hankel
ideal is strictly smaller than the parametrization kernel. Thus reducedness here
concerns the polynomial quotient, not an identification with the parametrization range. -/
public theorem integer_degree_zero_reduced_with_strict_kernel :
    IsReduced ℤ ∧
      IsReduced (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1) - C 1) ≠ 0 ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) := by
  have hred : IsReduced (Source ℤ 0 ⧸ hankelIdeal ℤ 0) := by
    rw [hankelIdeal_zero]
    exact isReduced_of_injective (RingEquiv.quotientBot (Source ℤ 0))
      (RingEquiv.quotientBot (Source ℤ 0)).injective
  refine ⟨inferInstance, hred, ?_, ?_, hankelIdeal_zero_lt_ker ℤ⟩
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact MvPolynomial.X_ne_zero (0 : Fin 1) hmem
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
    have hcoeff := congrArg
      (fun f : Source ℤ 0 ↦ f.coeff (Finsupp.single 0 1)) hmem
    change (X (0 : Fin 1) - C 1 : Source ℤ 0).coeff
      (Finsupp.single 0 1) = 0 at hcoeff
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_same,
      MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
    simp at hcoeff

private theorem integer_product_orthogonal_idempotents :
    ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (1, 0) = (1, 0) ∧
      ((0, 1) : ℤ × ℤ) * (0, 1) = (0, 1) ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro hzero
    exact one_ne_zero (congrArg Prod.snd hzero)
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp

private theorem integer_product_reduced_not_domain :
    IsReduced (ℤ × ℤ) ∧ ¬ IsDomain (ℤ × ℤ) := by
  refine ⟨inferInstance, ?_⟩
  intro hdomain
  let : IsDomain (ℤ × ℤ) := hdomain
  exact (mul_eq_zero.mp integer_product_orthogonal_idempotents.2.2.2.2).elim
    integer_product_orthogonal_idempotents.1
    integer_product_orthogonal_idempotents.2.1

private theorem integer_product_degree_zero_idempotents :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) =
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) =
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact integer_product_orthogonal_idempotents.1 (MvPolynomial.C_eq_zero.mp hmem)
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact integer_product_orthogonal_idempotents.2.1 (MvPolynomial.C_eq_zero.mp hmem)
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C c))
        integer_product_orthogonal_idempotents.2.2.1
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C c))
        integer_product_orthogonal_idempotents.2.2.2.1
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C c))
        integer_product_orthogonal_idempotents.2.2.2.2

private theorem integer_product_degree_zero_reduced_not_domain :
    IsReduced (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) ∧
      ¬ IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) := by
  constructor
  · rw [hankelIdeal_zero]
    exact isReduced_of_injective (RingEquiv.quotientBot (Source (ℤ × ℤ) 0))
      (RingEquiv.quotientBot (Source (ℤ × ℤ) 0)).injective
  · intro hdomain
    let : IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) := hdomain
    exact (mul_eq_zero.mp integer_product_degree_zero_idempotents.2.2.2.2).elim
      integer_product_degree_zero_idempotents.1
      integer_product_degree_zero_idempotents.2.1

private theorem rncMap_integer_product_degree_two_constant (c : ℤ × ℤ) :
    rncMap (ℤ × ℤ) 2 (C c) = C c := by
  rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
  change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 c) = AddMonoidAlgebra.single 0 c
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

private theorem integer_product_degree_two_idempotents :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) =
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) =
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C ((1, 0) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 := by
      simpa only [RingHom.mem_ker, rncMap_integer_product_degree_two_constant] using hker
    exact integer_product_orthogonal_idempotents.1 (MvPolynomial.C_eq_zero.mp htarget)
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C ((0, 1) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 := by
      simpa only [RingHom.mem_ker, rncMap_integer_product_degree_two_constant] using hker
    exact integer_product_orthogonal_idempotents.2.1 (MvPolynomial.C_eq_zero.mp htarget)
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        integer_product_orthogonal_idempotents.2.2.1
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        integer_product_orthogonal_idempotents.2.2.2.1
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        integer_product_orthogonal_idempotents.2.2.2.2

private theorem integer_product_degree_two_reduced_not_domain :
    IsReduced (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) ∧
      ¬ IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) := by
  constructor
  · let e := quotientEquivRange (ℤ × ℤ) 2 (by decide)
    exact isReduced_of_injective ((rncMap (ℤ × ℤ) 2).range.subtype.comp e.toRingHom)
      ((rncMap (ℤ × ℤ) 2).range.subtype_injective.comp e.injective)
  · intro hdomain
    let : IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) := hdomain
    exact (mul_eq_zero.mp integer_product_degree_two_idempotents.2.2.2.2).elim
      integer_product_degree_two_idempotents.1
      integer_product_degree_two_idempotents.2.1

private theorem two_mod_four_nonzero_square_zero :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧ ¬ IsReduced (ZMod 4) := by
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨hne, hsq, ?_⟩
  intro hred
  let : IsReduced (ZMod 4) := hred
  exact hne (eq_zero_of_pow_eq_zero hsq)

private theorem two_mod_four_degree_zero_nonzero_square_zero :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ^ 2 = 0 ∧
      ¬ IsReduced (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) := by
  have hne : Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ≠ 0 := by
    intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact two_mod_four_nonzero_square_zero.1 (MvPolynomial.C_eq_zero.mp hmem)
  have hsq : Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ^ 2 = 0 := by
    simpa only [map_pow, map_zero] using
      congrArg (fun c : ZMod 4 ↦ Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C c))
        two_mod_four_nonzero_square_zero.2.1
  refine ⟨hne, hsq, ?_⟩
  intro hred
  let : IsReduced (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) := hred
  exact hne (eq_zero_of_pow_eq_zero hsq)

private theorem rncMap_two_mod_four_degree_two_constant :
    rncMap (ZMod 4) 2 (C (2 : ZMod 4)) = C (2 : ZMod 4) := by
  rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
  change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 (2 : ZMod 4)) = AddMonoidAlgebra.single 0 (2 : ZMod 4)
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

private theorem two_mod_four_degree_two_nonzero_square_zero :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0 ∧
      ¬ IsReduced (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) := by
  have hne : Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 := by
    intro hzero
    have hker := hankelIdeal_le_ker (ZMod 4) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C (2 : ZMod 4) : Target (ZMod 4)) = 0 := by
      simpa only [RingHom.mem_ker, rncMap_two_mod_four_degree_two_constant] using hker
    exact two_mod_four_nonzero_square_zero.1 (MvPolynomial.C_eq_zero.mp htarget)
  have hsq : Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0 := by
    simpa only [map_pow, map_zero] using
      congrArg (fun c : ZMod 4 ↦ Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C c))
        two_mod_four_nonzero_square_zero.2.1
  refine ⟨hne, hsq, ?_⟩
  intro hred
  let : IsReduced (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) := hred
  exact hne (eq_zero_of_pow_eq_zero hsq)

private theorem zero_coefficients_reduced_not_domain :
    IsReduced (ZMod 1) ∧ ¬ IsDomain (ZMod 1) := by
  refine ⟨inferInstance, ?_⟩
  intro hdomain
  let : IsDomain (ZMod 1) := hdomain
  exact one_ne_zero (Subsingleton.elim (1 : ZMod 1) 0)

private theorem zero_coefficients_degree_zero_reduced_not_domain :
    IsReduced (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) ∧
      ¬ IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) ∧
      (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0 := by
  have hunit : (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) 0))
        (Subsingleton.elim (1 : Source (ZMod 1) 0) 0)
  refine ⟨inferInstance, ?_, hunit⟩
  intro hdomain
  let : IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) := hdomain
  exact one_ne_zero hunit

private theorem zero_coefficients_degree_two_reduced_not_domain :
    IsReduced (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) ∧
      ¬ IsDomain (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) ∧
      (1 : Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) = 0 := by
  have hunit : (1 : Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 1) 2))
        (Subsingleton.elim (1 : Source (ZMod 1) 2) 0)
  refine ⟨inferInstance, ?_, hunit⟩
  intro hdomain
  let : IsDomain (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) := hdomain
  exact one_ne_zero hunit

private theorem integer_degree_zero_reduced_radical_with_strict_kernel :
    IsReduced (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      (hankelIdeal ℤ 0).IsRadical ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1) - C 1) ≠ 0 ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) := by
  have hcoeff : IsReduced ℤ := integer_degree_zero_reduced_with_strict_kernel.1
  exact ⟨(quotient_isReduced_iff ℤ 0).mpr hcoeff,
    (hankelIdeal_isRadical_iff ℤ 0).mpr hcoeff,
    integer_degree_zero_reduced_with_strict_kernel.2.2⟩

private theorem integer_product_reduced_radical_orthogonal_classes :
    ¬ IsDomain (ℤ × ℤ) ∧
      (IsReduced (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) ∧
        (hankelIdeal (ℤ × ℤ) 0).IsRadical ∧
        ¬ IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) *
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) = 0) ∧
      (IsReduced (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) ∧
        (hankelIdeal (ℤ × ℤ) 2).IsRadical ∧
        ¬ IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
          Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) = 0) := by
  have hcoeff : IsReduced (ℤ × ℤ) := integer_product_reduced_not_domain.1
  refine ⟨integer_product_reduced_not_domain.2, ?_, ?_⟩
  · exact ⟨(quotient_isReduced_iff (ℤ × ℤ) 0).mpr hcoeff,
      (hankelIdeal_isRadical_iff (ℤ × ℤ) 0).mpr hcoeff,
      integer_product_degree_zero_reduced_not_domain.2,
      integer_product_degree_zero_idempotents.1,
      integer_product_degree_zero_idempotents.2.1,
      integer_product_degree_zero_idempotents.2.2.2.2⟩
  · exact ⟨(quotient_isReduced_iff (ℤ × ℤ) 2).mpr hcoeff,
      (hankelIdeal_isRadical_iff (ℤ × ℤ) 2).mpr hcoeff,
      integer_product_degree_two_reduced_not_domain.2,
      integer_product_degree_two_idempotents.1,
      integer_product_degree_two_idempotents.2.1,
      integer_product_degree_two_idempotents.2.2.2.2⟩

private theorem two_mod_four_nonreduced_nonradical_square_zero :
    ¬ IsReduced (ZMod 4) ∧
      (¬ IsReduced (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) ∧
        ¬ (hankelIdeal (ZMod 4) 0).IsRadical ∧
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (C (2 : ZMod 4)) ^ 2 = 0) ∧
      (¬ IsReduced (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) ∧
        ¬ (hankelIdeal (ZMod 4) 2).IsRadical ∧
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0) := by
  have hcoeff : ¬ IsReduced (ZMod 4) := two_mod_four_nonzero_square_zero.2.2
  refine ⟨hcoeff, ?_, ?_⟩
  · exact ⟨fun hred ↦ hcoeff ((quotient_isReduced_iff (ZMod 4) 0).mp hred),
      fun hrad ↦ hcoeff ((hankelIdeal_isRadical_iff (ZMod 4) 0).mp hrad),
      two_mod_four_degree_zero_nonzero_square_zero.1,
      two_mod_four_degree_zero_nonzero_square_zero.2.1⟩
  · exact ⟨fun hred ↦ hcoeff ((quotient_isReduced_iff (ZMod 4) 2).mp hred),
      fun hrad ↦ hcoeff ((hankelIdeal_isRadical_iff (ZMod 4) 2).mp hrad),
      two_mod_four_degree_two_nonzero_square_zero.1,
      two_mod_four_degree_two_nonzero_square_zero.2.1⟩

private theorem zero_coefficients_reduced_radical_unit_zero :
    ¬ IsDomain (ZMod 1) ∧
      (IsReduced (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) ∧
        (hankelIdeal (ZMod 1) 0).IsRadical ∧
        ¬ IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) ∧
        (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0) ∧
      (IsReduced (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) ∧
        (hankelIdeal (ZMod 1) 2).IsRadical ∧
        ¬ IsDomain (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) ∧
        (1 : Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) = 0) := by
  have hcoeff : IsReduced (ZMod 1) := zero_coefficients_reduced_not_domain.1
  refine ⟨zero_coefficients_reduced_not_domain.2, ?_, ?_⟩
  · exact ⟨(quotient_isReduced_iff (ZMod 1) 0).mpr hcoeff,
      (hankelIdeal_isRadical_iff (ZMod 1) 0).mpr hcoeff,
      zero_coefficients_degree_zero_reduced_not_domain.2⟩
  · exact ⟨(quotient_isReduced_iff (ZMod 1) 2).mpr hcoeff,
      (hankelIdeal_isRadical_iff (ZMod 1) 2).mpr hcoeff,
      zero_coefficients_degree_two_reduced_not_domain.2⟩

end

end ToricIdeals.RationalNormalCurve
