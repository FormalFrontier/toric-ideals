/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Coefficient modules and small-degree quotient models

These standalone examples describe polynomial coefficient modules and Hankel
quotients over commutative rings. The degree-zero parametrization and the full
Hankel quotient have different behavior: the parametrization sends the sole
variable to `1`, whereas the quotient is a polynomial ring in that variable.

The examples include the zero ring, the integers, `ZMod 4`, and `ℤ × ℤ`.
They exhibit small-degree freeness and flatness, surviving variables and
coefficients, nilpotents, zero divisors, and coefficient change from `ℤ` to
`ZMod 4` without an injectivity or flatness hypothesis.
-/

open ToricIdeals.RationalNormalCurve

universe u v w

variable (k : Type u) [CommRing k]

open scoped TensorProduct

private instance : Fact (1 < (4 : ℕ)) := ⟨by decide⟩

/-!
## Polynomial coefficient modules and small-degree quotients

The monoid index and coefficient ring occupy independent universes. Mathlib's
`AddMonoidAlgebra.basis` supplies polynomial freeness without a domain, field,
nontriviality, or finiteness assumption; freeness also gives flatness.

The Hankel ideal is zero in degrees zero and one. The corresponding quotient
algebras are `Polynomial k` and `MvPolynomial (Fin 2) k`, respectively. At
degree zero the raw parametrization sends `X₀` to `1`, but the full quotient
retains a polynomial variable, distinct from `1` when `k` is nontrivial.
-/

private theorem monoid_coefficient_free
    (R : Type u) [CommRing R] (M : Type v) [AddCommMonoid M] :
    Module.Free R (AddMonoidAlgebra R M) :=
  Module.Free.of_basis (AddMonoidAlgebra.basis M R)

private theorem polynomial_coefficient_free (σ : Type v) :
    Module.Free k (MvPolynomial σ k) :=
  Module.Free.of_basis (AddMonoidAlgebra.basis (σ →₀ ℕ) k)

private theorem polynomial_coefficient_flat (σ : Type v) :
    Module.Flat k (MvPolynomial σ k) := by
  let := polynomial_coefficient_free k σ
  exact Module.Flat.of_free

private theorem monomial_basis_coefficient (σ : Type v) (d : σ →₀ ℕ) :
    AddMonoidAlgebra.basis (σ →₀ ℕ) k d = MvPolynomial.monomial d 1 :=
  rfl

private theorem coefficient_quotient_mk (n : ℕ) (r : k) :
    Ideal.Quotient.mkₐ k (hankelIdeal k n) (MvPolynomial.C r) =
      algebraMap k (Source k n ⧸ hankelIdeal k n) r :=
  rfl

private theorem algebra_parametrization_coefficient (n : ℕ) (r : k) :
    AddMonoidAlgebra.mapDomainAlgHom k k (rncExponent n) (MvPolynomial.C r) =
      MvPolynomial.C r :=
  rncMap_C k n r

private noncomputable def degree_zero_polynomial :
    (Source k 0 ⧸ hankelIdeal k 0) ≃ₐ[k] Polynomial k :=
  ((Ideal.quotientEquivAlgOfEq k (hankelIdeal_zero k)).trans
    (AlgEquiv.quotientBot k (Source k 0))).trans
      (MvPolynomial.uniqueAlgEquiv k (Fin 1))

private theorem degree_zero_polynomial_variable :
    degree_zero_polynomial k
      (Ideal.Quotient.mk (hankelIdeal k 0) (MvPolynomial.X (0 : Fin 1))) =
        Polynomial.X := by
  simp [degree_zero_polynomial, MvPolynomial.uniqueAlgEquiv_apply]

private theorem degree_zero_variable_ne_one [Nontrivial k] :
    Ideal.Quotient.mk (hankelIdeal k 0) (MvPolynomial.X (0 : Fin 1)) ≠ 1 := by
  intro h
  have hX := congrArg (degree_zero_polynomial k) h
  rw [degree_zero_polynomial_variable, map_one] at hX
  exact Polynomial.X_ne_C (1 : k) (by simpa using hX)

private theorem degree_zero_raw_variable :
    rncMap k 0 (MvPolynomial.X (0 : Fin 1)) = 1 := by
  simp [rncMap_X, coordinateExponent, MvPolynomial.monomial_zero']

private theorem degree_zero_free :
    Module.Free k (Source k 0 ⧸ hankelIdeal k 0) :=
  Module.Free.of_equiv (degree_zero_polynomial k).symm.toLinearEquiv

private theorem degree_zero_flat :
    Module.Flat k (Source k 0 ⧸ hankelIdeal k 0) := by
  let := degree_zero_free k
  exact Module.Flat.of_free

private noncomputable def degree_one_polynomial :
    (Source k 1 ⧸ hankelIdeal k 1) ≃ₐ[k] MvPolynomial (Fin 2) k :=
  (Ideal.quotientEquivAlgOfEq k (hankelIdeal_one k)).trans
    (AlgEquiv.quotientBot k (Source k 1))

private theorem degree_one_polynomial_mk (f : Source k 1) :
    degree_one_polynomial k (Ideal.Quotient.mk (hankelIdeal k 1) f) = f := by
  simp [degree_one_polynomial]

private theorem degree_one_two_variables :
    degree_one_polynomial k
        (Ideal.Quotient.mk (hankelIdeal k 1) (MvPolynomial.X (0 : Fin 2))) =
          MvPolynomial.X (0 : Fin 2) ∧
      degree_one_polynomial k
        (Ideal.Quotient.mk (hankelIdeal k 1) (MvPolynomial.X (1 : Fin 2))) =
          MvPolynomial.X (1 : Fin 2) :=
  ⟨degree_one_polynomial_mk k _, degree_one_polynomial_mk k _⟩

private theorem degree_one_free :
    Module.Free k (Source k 1 ⧸ hankelIdeal k 1) :=
  Module.Free.of_basis ((AddMonoidAlgebra.basis (Fin 2 →₀ ℕ) k).map
    (degree_one_polynomial k).symm.toLinearEquiv)

private theorem degree_one_flat :
    Module.Flat k (Source k 1 ⧸ hankelIdeal k 1) := by
  let := degree_one_free k
  exact Module.Flat.of_free

/-!
## Zero-ring, integer, nilpotent, and product examples

The small-degree free and flat module examples follow from the preceding
polynomial descriptions. Over the zero ring the quotient is free and flat in
every degree. Over `ℤ` and `ZMod 4`, the degree-zero variable is distinct from
`1`; over `ℤ × ℤ`, the two degree-one variables are distinct.

The coefficient map into each Hankel quotient is injective. Thus the conic
quotient over `ZMod 4` contains a nonzero coefficient `2` whose square is zero,
alongside the relation `X₀ * X₂ = X₁ ^ 2`. The cubic quotient over `ℤ × ℤ`
contains nonzero coefficients `(1, 0)` and `(0, 1)` with zero product, alongside
`X₀ * X₃ = X₁ * X₂`. These illustrate nilpotents and zero divisors without
imposing domain or reducedness assumptions on the coefficient ring.
-/

private theorem zero_ring_free (n : ℕ) :
    Module.Free (PUnit.{1})
      (Source (PUnit.{1}) n ⧸ hankelIdeal (PUnit.{1}) n) :=
  Module.Free.of_subsingleton _ _

private theorem zero_ring_flat (n : ℕ) :
    Module.Flat (PUnit.{1})
      (Source (PUnit.{1}) n ⧸ hankelIdeal (PUnit.{1}) n) := by
  let := zero_ring_free n
  exact Module.Flat.of_free

private theorem integer_one_variable_free :
    Module.Free ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) :=
  degree_zero_free ℤ

private theorem integer_one_variable_survives :
    Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1)) ≠ 1 :=
  degree_zero_variable_ne_one ℤ

private theorem mod_four_one_variable_flat :
    Module.Flat (ZMod 4) (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) :=
  degree_zero_flat (ZMod 4)

private theorem mod_four_one_variable_survives :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (MvPolynomial.X (0 : Fin 1)) ≠ 1 :=
  degree_zero_variable_ne_one (ZMod 4)

private theorem product_two_variables_distinct :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 1) (MvPolynomial.X (0 : Fin 2)) ≠
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 1) (MvPolynomial.X (1 : Fin 2)) := by
  intro h
  have hX := congrArg (degree_one_polynomial (ℤ × ℤ)) h
  rw [degree_one_polynomial_mk, degree_one_polynomial_mk] at hX
  exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_injective hX)

private theorem product_two_variable_free :
    Module.Free (ℤ × ℤ) (Source (ℤ × ℤ) 1 ⧸ hankelIdeal (ℤ × ℤ) 1) :=
  degree_one_free (ℤ × ℤ)

private theorem mod_four_two_variable_flat :
    Module.Flat (ZMod 4) (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) :=
  degree_one_flat (ZMod 4)

private theorem coefficient_quotient_injective (n : ℕ) :
    Function.Injective (algebraMap k (Source k n ⧸ hankelIdeal k n)) := by
  intro a b hab
  apply MvPolynomial.C_injective (Fin 2) k
  have hmem : (MvPolynomial.C a - MvPolynomial.C b : Source k n) ∈
      hankelIdeal k n := Ideal.Quotient.eq.mp hab
  have hzero := hankelIdeal_le_ker k n hmem
  change rncMap k n (MvPolynomial.C a - MvPolynomial.C b) = 0 at hzero
  simpa only [map_sub, rncMap_C, sub_eq_zero] using hzero

private theorem mod_four_nilpotent_conic_coefficient :
    algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2 ≠ 0 ∧
      (algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2) ^ 2 = 0 := by
  constructor
  · intro h
    exact (by decide : (2 : ZMod 4) ≠ 0)
      (coefficient_quotient_injective (ZMod 4) 2 (h.trans (map_zero _).symm))
  · rw [← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero]

private theorem mod_four_conic_relation :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2)
      (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) -
        MvPolynomial.X (1 : Fin 3) ^ 2 : Source (ZMod 4) 2) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa [hankelMinor, pow_two] using
    minor_mem (ZMod 4) 2 ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩

private theorem product_cubic_relation :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 3)
      (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (3 : Fin 4) -
        MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (2 : Fin 4) :
          Source (ℤ × ℤ) 3) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa [hankelMinor] using
    minor_mem (ℤ × ℤ) 3 ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩

private theorem product_cubic_zero_divisors :
    algebraMap (ℤ × ℤ) (Source (ℤ × ℤ) 3 ⧸ hankelIdeal (ℤ × ℤ) 3) (1, 0) ≠ 0 ∧
      algebraMap (ℤ × ℤ) (Source (ℤ × ℤ) 3 ⧸ hankelIdeal (ℤ × ℤ) 3) (0, 1) ≠ 0 ∧
      algebraMap (ℤ × ℤ) (Source (ℤ × ℤ) 3 ⧸ hankelIdeal (ℤ × ℤ) 3) (1, 0) *
        algebraMap (ℤ × ℤ) (Source (ℤ × ℤ) 3 ⧸ hankelIdeal (ℤ × ℤ) 3) (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (by decide : ((1, 0) : ℤ × ℤ) ≠ 0)
      (coefficient_quotient_injective (ℤ × ℤ) 3 (h.trans (map_zero _).symm))
  · intro h
    exact (by decide : ((0, 1) : ℤ × ℤ) ≠ 0)
      (coefficient_quotient_injective (ℤ × ℤ) 3 (h.trans (map_zero _).symm))
  · rw [← map_mul, show ((1, 0) : ℤ × ℤ) * (0, 1) = 0 by decide, map_zero]

/-!
## Noninjective, nonflat coefficient change and tensor quotients

The coefficient map `ℤ → ZMod 4` kills `4` and is therefore not injective.
Also, `ZMod 4` is not flat over `ℤ`: multiplication by `4` is injective on
`ℤ` but is the zero map on the nonzero module `ZMod 4`.

Nevertheless, coefficient change carries the conic Hankel ideal over `ℤ` to
the conic Hankel ideal over `ZMod 4`. Mathlib's
`MvPolynomial.algebraTensorAlgEquiv` carries the tensor of a conic minor to
its coefficient image. Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv`
identifies the tensor of the quotient with the quotient of the tensor product
by the extended ideal; the final example describes the image of a variable
class under this equivalence.
-/

private theorem mod_four_not_flat_over_integer : ¬ Module.Flat ℤ (ZMod 4) := by
  intro hflat
  let : Module.Flat ℤ (ZMod 4) := hflat
  have hregular : IsSMulRegular ℤ (4 : ℤ) :=
    (IsRegular.of_ne_zero (by decide : (4 : ℤ) ≠ 0)).left.isSMulRegular
  have h := IsSMulRegular.of_flat (R := ℤ) (S := ZMod 4) hregular
  have hfour : algebraMap ℤ (ZMod 4) (4 : ℤ) = 0 := by decide
  have hzero : IsSMulRegular (ZMod 4) (0 : ZMod 4) := by
    simpa only [hfour] using h
  exact (IsSMulRegular.not_zero (M := ZMod 4)) hzero

private theorem integer_mod_four_conic_ideal :
    Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod 4))) (hankelIdeal ℤ 2) =
      hankelIdeal (ZMod 4) 2 :=
  map_hankelIdeal (Int.castRingHom (ZMod 4)) 2

private theorem integer_mod_four_polynomial_tensor :
    MvPolynomial.algebraTensorAlgEquiv ℤ (ZMod 4)
      ((1 : ZMod 4) ⊗ₜ[ℤ] (hankelMinor ℤ 2 ⟨(0, 1), by decide⟩)) =
        hankelMinor (ZMod 4) 2 ⟨(0, 1), by decide⟩ := by
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  exact map_hankelMinor (Int.castRingHom (ZMod 4)) 2 _

private theorem integer_mod_four_tensor_quotient_variable :
    Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ)
      (ZMod 4) (Source ℤ 2) (ZMod 4) (hankelIdeal ℤ 2)
      ((1 : ZMod 4) ⊗ₜ[ℤ]
        (Ideal.Quotient.mk (hankelIdeal ℤ 2) (MvPolynomial.X (1 : Fin 3)))) =
      Ideal.Quotient.mk
        ((hankelIdeal ℤ 2).map
          (Algebra.TensorProduct.includeRight (A := ZMod 4) (R := ℤ)))
        ((1 : ZMod 4) ⊗ₜ[ℤ] (MvPolynomial.X (1 : Fin 3) : Source ℤ 2)) :=
  Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul (R := ℤ)
    (ZMod 4) (Source ℤ 2) (ZMod 4) (hankelIdeal ℤ 2) 1 _
