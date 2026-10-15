/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.ZMod.Basic
public import ToricIdeals.RationalNormalCurve
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import ToricIdeals.RationalNormalCurve.IntegralClosure

/-!
# Coefficient-ring models for rational-normal-curve quotients

Integer coefficients give prime Hankel ideals and domain quotients in degrees
zero, one and two. Each quotient has a specified nonzero variable class. In
degree zero there are no minors: the quotient retains a nonzero class of
`X₀ - 1`, although the parametrization sends `X₀` to `1`. In degree two the
Hankel relation `X₀ X₂ - X₁²` vanishes in the quotient.

The zero coefficient ring `ZMod 1` gives the top ideal and a quotient with
`1 = 0`, in degrees zero and two. Neither the coefficient ring nor either
quotient is a domain, and neither ideal is prime.

The nonzero zero-divisors `(1, 0)` and `(0, 1)` of `ℤ × ℤ` remain nonzero as
constant classes in the degree-zero and degree-two quotients. Their product is
zero, so these quotients are nontrivial but not domains, and their proper
Hankel ideals are not prime. Degree zero uses the empty set of minors; degree
two uses the containment of the Hankel ideal in the parametrization kernel to
check that the displayed constants survive.
-/

open MvPolynomial
open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.DomainModels

@[expose] public noncomputable section

/-- Over the integers, degree zero has a prime Hankel ideal and a domain
quotient. The classes of `X₀` and `X₀ - 1` are nonzero, even though the
parametrization sends `X₀` to `1`. -/
theorem integer_degree_zero :
    IsDomain ℤ ∧
      (hankelIdeal ℤ 0).IsPrime ∧
      IsDomain (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1) - C 1) ≠ 0 ∧
      rncMap ℤ 0 (X (0 : Fin 1)) = 1 := by
  have hprime : (hankelIdeal ℤ 0).IsPrime := by
    rw [hankelIdeal_zero]
    exact Ideal.isPrime_bot
  have hdomain : IsDomain (Source ℤ 0 ⧸ hankelIdeal ℤ 0) :=
    (Ideal.Quotient.isDomain_iff_prime (hankelIdeal ℤ 0)).mpr hprime
  refine ⟨inferInstance, hprime, hdomain, ?_, ?_, ?_⟩
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
  · simp [rncMap_X, coordinateExponent]

/-- The degree-one integer quotient is a domain with a nonzero variable
class, and its Hankel ideal is prime. -/
theorem integer_degree_one :
    IsDomain ℤ ∧
      (hankelIdeal ℤ 1).IsPrime ∧
      IsDomain (Source ℤ 1 ⧸ hankelIdeal ℤ 1) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠ 0 := by
  refine ⟨inferInstance, hankelIdeal_isPrime ℤ 1 (by decide),
    quotient_isDomain ℤ 1 (by decide), ?_⟩
  intro hzero
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hankelIdeal_one, Submodule.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero (0 : Fin 2) hmem

/-- The degree-two integer quotient is a domain with a nonzero variable
class, its Hankel ideal is prime, and its quadratic Hankel relation is zero
in the quotient. -/
theorem integer_degree_two :
    IsDomain ℤ ∧
      (hankelIdeal ℤ 2).IsPrime ∧
      IsDomain (Source ℤ 2 ⧸ hankelIdeal ℤ 2) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 2) (X (0 : Fin 3)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 2)
        (X (0 : Fin 3) * X 2 - X 1 ^ 2) = 0 := by
  refine ⟨inferInstance, hankelIdeal_isPrime ℤ 2 (by decide),
    quotient_isDomain ℤ 2 (by decide), ?_, ?_⟩
  · intro hzero
    have hker := hankelIdeal_le_ker ℤ 2 (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : monomial (coordinateExponent 2 (0 : Fin 3)) (1 : ℤ) = 0 := by
      simpa only [RingHom.mem_ker, rncMap_X] using hker
    exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp htarget)
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [hankelMinor, pow_two] using
      minor_mem ℤ 2 (⟨(0, 1), by decide⟩ : MinorIndex 2)

private theorem zmod_one_not_domain : ¬ IsDomain (ZMod 1) := by
  intro hdomain
  let : IsDomain (ZMod 1) := hdomain
  exact one_ne_zero (Subsingleton.elim (1 : ZMod 1) 0)

/-- Zero coefficients in degree zero give a nonprime top ideal and a
nondomain quotient whose unit is zero. -/
theorem zero_coefficients_degree_zero :
    ¬ IsDomain (ZMod 1) ∧
      hankelIdeal (ZMod 1) 0 = ⊤ ∧
      ¬ (hankelIdeal (ZMod 1) 0).IsPrime ∧
      ¬ IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) ∧
      (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0 := by
  have htop : hankelIdeal (ZMod 1) 0 = ⊤ := by
    rw [hankelIdeal_zero]
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Subsingleton.elim (1 : Source (ZMod 1) 0) 0]
    exact (⊥ : Ideal (Source (ZMod 1) 0)).zero_mem
  have hunit : (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0 := by
    have hmem : (1 : Source (ZMod 1) 0) ∈ hankelIdeal (ZMod 1) 0 := by
      rw [htop]
      exact Submodule.mem_top
    simpa only [map_one] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  refine ⟨zmod_one_not_domain, htop, ?_, ?_, hunit⟩
  · intro hprime
    exact hprime.ne_top htop
  · intro hdomain
    let : IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) := hdomain
    exact one_ne_zero hunit

/-- Zero coefficients in degree two give a nonprime top ideal and a
nondomain quotient whose unit is zero. -/
theorem zero_coefficients_degree_two :
    ¬ IsDomain (ZMod 1) ∧
      hankelIdeal (ZMod 1) 2 = ⊤ ∧
      ¬ (hankelIdeal (ZMod 1) 2).IsPrime ∧
      ¬ IsDomain (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) ∧
      (1 : Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) = 0 := by
  have htop : hankelIdeal (ZMod 1) 2 = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Subsingleton.elim (1 : Source (ZMod 1) 2) 0]
    exact (hankelIdeal (ZMod 1) 2).zero_mem
  have hunit : (1 : Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) = 0 := by
    have hmem : (1 : Source (ZMod 1) 2) ∈ hankelIdeal (ZMod 1) 2 := by
      rw [htop]
      exact Submodule.mem_top
    simpa only [map_one] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  refine ⟨zmod_one_not_domain, htop, ?_, ?_, hunit⟩
  · intro hprime
    exact hprime.ne_top htop
  · intro hdomain
    let : IsDomain (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2) := hdomain
    exact one_ne_zero hunit

private theorem product_idempotents :
    ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro hzero
    exact one_ne_zero (congrArg Prod.snd hzero)
  · ext <;> simp

/-- The product of two integer rings is not a domain: its two complementary
idempotents are nonzero and have zero product. -/
theorem product_coefficients :
    ¬ IsDomain (ℤ × ℤ) ∧
      ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by
  refine ⟨?_, product_idempotents⟩
  intro hdomain
  let : IsDomain (ℤ × ℤ) := hdomain
  exact (mul_eq_zero.mp product_idempotents.2.2).elim
    product_idempotents.1 product_idempotents.2.1

private theorem product_degree_zero_classes :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact product_idempotents.1 (MvPolynomial.C_eq_zero.mp hmem)
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero, Submodule.mem_bot] at hmem
    exact product_idempotents.2.1 (MvPolynomial.C_eq_zero.mp hmem)
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C c))
        product_idempotents.2.2

/-- In degree zero over `ℤ × ℤ`, the Hankel ideal is proper but not prime.
The constant classes of `(1, 0)` and `(0, 1)` are nonzero zero-divisors, so
the quotient is not a domain. -/
theorem product_degree_zero :
    ¬ IsDomain (ℤ × ℤ) ∧
      hankelIdeal (ℤ × ℤ) 0 ≠ ⊤ ∧
      ¬ (hankelIdeal (ℤ × ℤ) 0).IsPrime ∧
      ¬ IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 0) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  have hproper : hankelIdeal (ℤ × ℤ) 0 ≠ ⊤ := by
    intro htop
    apply product_degree_zero_classes.1
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [htop]
    exact Submodule.mem_top
  have hnotDomain : ¬ IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) := by
    intro hdomain
    let : IsDomain (Source (ℤ × ℤ) 0 ⧸ hankelIdeal (ℤ × ℤ) 0) := hdomain
    exact (mul_eq_zero.mp product_degree_zero_classes.2.2).elim
      product_degree_zero_classes.1 product_degree_zero_classes.2.1
  refine ⟨product_coefficients.1, hproper, ?_, hnotDomain, product_degree_zero_classes⟩
  intro hprime
  exact hnotDomain
    ((Ideal.Quotient.isDomain_iff_prime (hankelIdeal (ℤ × ℤ) 0)).mpr hprime)

private theorem product_degree_two_map_constant (c : ℤ × ℤ) :
    rncMap (ℤ × ℤ) 2 (C c) = C c := by
  rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
  change AddMonoidAlgebra.mapDomain (rncExponent 2)
      (AddMonoidAlgebra.single 0 c) = AddMonoidAlgebra.single 0 c
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

private theorem product_degree_two_classes :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C ((1, 0) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 := by
      simpa only [RingHom.mem_ker, product_degree_two_map_constant] using hker
    exact product_idempotents.1 (MvPolynomial.C_eq_zero.mp htarget)
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C ((0, 1) : ℤ × ℤ) : Target (ℤ × ℤ)) = 0 := by
      simpa only [RingHom.mem_ker, product_degree_two_map_constant] using hker
    exact product_idempotents.2.1 (MvPolynomial.C_eq_zero.mp htarget)
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        product_idempotents.2.2

/-- In degree two over `ℤ × ℤ`, the Hankel ideal is proper but not prime.
The constant classes of `(1, 0)` and `(0, 1)` survive the Hankel relations
and have zero product, so the quotient is not a domain. -/
theorem product_degree_two :
    ¬ IsDomain (ℤ × ℤ) ∧
      hankelIdeal (ℤ × ℤ) 2 ≠ ⊤ ∧
      ¬ (hankelIdeal (ℤ × ℤ) 2).IsPrime ∧
      ¬ IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C ((0, 1) : ℤ × ℤ)) = 0 := by
  have hproper : hankelIdeal (ℤ × ℤ) 2 ≠ ⊤ := by
    intro htop
    apply product_degree_two_classes.1
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [htop]
    exact Submodule.mem_top
  have hnotDomain : ¬ IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) := by
    intro hdomain
    let : IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) := hdomain
    exact (mul_eq_zero.mp product_degree_two_classes.2.2).elim
      product_degree_two_classes.1 product_degree_two_classes.2.1
  refine ⟨product_coefficients.1, hproper, ?_, hnotDomain, product_degree_two_classes⟩
  intro hprime
  exact hnotDomain
    ((Ideal.Quotient.isDomain_iff_prime (hankelIdeal (ℤ × ℤ) 2)).mpr hprime)

end

end ToricIdeals.RationalNormalCurve.DomainModels

namespace ToricIdeals.RationalNormalCurve.DomainModels

/-- The degree-zero integer quotient is a domain with a nonzero variable
class, although the parametrization kernel strictly contains its prime
Hankel ideal. -/
private theorem integer_degree_zero_prime_domain_strict_kernel :
    (hankelIdeal ℤ 0).IsPrime ∧
      IsDomain (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) := by
  exact ⟨(hankelIdeal_isPrime_iff ℤ 0).mpr inferInstance,
    (quotient_isDomain_iff ℤ 0).mpr inferInstance,
    integer_degree_zero.2.2.2.1, hankelIdeal_zero_lt_ker ℤ⟩

/-- The complementary integer-product idempotents witness that a proper
Hankel ideal in degree two need not be prime, and its quotient need not be
a domain. -/
private theorem product_degree_two_proper_with_coefficient_zero_divisors :
    hankelIdeal (ℤ × ℤ) 2 ≠ ⊤ ∧
      ¬ (hankelIdeal (ℤ × ℤ) 2).IsPrime ∧
      ¬ IsDomain (Source (ℤ × ℤ) 2 ⧸ hankelIdeal (ℤ × ℤ) 2) ∧
      ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by
  refine ⟨product_degree_two.2.1, ?_, ?_, product_coefficients.2⟩
  · intro hprime
    exact product_coefficients.1
      ((hankelIdeal_isPrime_iff (ℤ × ℤ) 2).mp hprime)
  · intro hdomain
    exact product_coefficients.1
      ((quotient_isDomain_iff (ℤ × ℤ) 2).mp hdomain)

/-- In degree zero over the zero coefficient ring, the quotient unit is
zero and both primality and the domain property fail. -/
private theorem zero_coefficients_degree_zero_unit_not_prime_not_domain :
    (1 : Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) = 0 ∧
      ¬ (hankelIdeal (ZMod 1) 0).IsPrime ∧
      ¬ IsDomain (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0) := by
  refine ⟨zero_coefficients_degree_zero.2.2.2.2, ?_, ?_⟩
  · intro hprime
    exact zmod_one_not_domain
      ((hankelIdeal_isPrime_iff (ZMod 1) 0).mp hprime)
  · intro hdomain
    exact zmod_one_not_domain
      ((quotient_isDomain_iff (ZMod 1) 0).mp hdomain)

-- The degree-two Hankel quotient over the integers is integrally closed.
example : IsIntegrallyClosed (Source ℤ 2 ⧸ hankelIdeal ℤ 2) :=
  (quotient_isIntegrallyClosed_iff ℤ 2).2 inferInstance

-- The full degree-zero quotient is integrally closed over an integrally closed
-- coefficient domain; its polynomial variable is retained.
example (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed (Source R 0 ⧸ hankelIdeal R 0) :=
  (quotient_isIntegrallyClosed_iff R 0).2 inferInstance

end ToricIdeals.RationalNormalCurve.DomainModels
