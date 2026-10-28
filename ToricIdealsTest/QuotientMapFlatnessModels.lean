/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RingHom.Flat
import ToricIdeals.RationalNormalCurve.EndpointMap

/-!
# Fixed Hankel quotient flatness controls

These controls use an independent canonical quotient lift. They do not
import the quotient-map definition, its proposed flatness statement, or
any flatness classifier for the raw parametrization.
-/

open MvPolynomial TensorProduct
open ToricIdeals.RationalNormalCurve

noncomputable section

private def rawQuotientMap (R : Type*) [CommRing R] (n : ℕ) :
    (Source R n ⧸ hankelIdeal R n) →+* Target R :=
  Ideal.Quotient.lift (hankelIdeal R n) (rncMap R n)
    (fun _ hp => RingHom.mem_ker.mp (hankelIdeal_le_ker R n hp))

private theorem rawQuotientMap_mk (R : Type*) [CommRing R] (n : ℕ) (p : Source R n) :
    rawQuotientMap R n (Ideal.Quotient.mk (hankelIdeal R n) p) = rncMap R n p := rfl

private theorem integer_one_identity : rncMap ℤ 1 = RingHom.id (Target ℤ) := by
  have he : rncExponent 1 = AddMonoidHom.id (Fin 2 →₀ ℕ) := by
    apply AddMonoidHom.ext
    intro d
    exact rncExponent_one d
  rw [rncMap, he, AddMonoidAlgebra.mapDomainRingHom_id]

private theorem integer_one_bijective : Function.Bijective (rawQuotientMap ℤ 1) := by
  have hmk (p : Source ℤ 1) :
      rawQuotientMap ℤ 1 (Ideal.Quotient.mk (hankelIdeal ℤ 1) p) = p := by
    simp only [rawQuotientMap_mk, integer_one_identity, RingHom.id_apply]
  constructor
  · intro x y h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hpq : p = q := by simpa only [hmk] using h
    exact congrArg (Ideal.Quotient.mk (hankelIdeal ℤ 1)) hpq
  · intro p
    exact ⟨Ideal.Quotient.mk (hankelIdeal ℤ 1) p, hmk p⟩

private def integerOneEquiv :
    (Source ℤ 1 ⧸ hankelIdeal ℤ 1) ≃+* Target ℤ :=
  RingEquiv.ofBijective (rawQuotientMap ℤ 1) integer_one_bijective

private theorem integer_one_hankel_eq_bot : hankelIdeal ℤ 1 = ⊥ := hankelIdeal_one ℤ

private theorem integer_one_flat : @Module.Flat (Source ℤ 1 ⧸ hankelIdeal ℤ 1) (Target ℤ) _ _
    (@Algebra.toModule _ _ _ _ (rawQuotientMap ℤ 1).toAlgebra) := by
  change (rawQuotientMap ℤ 1).Flat
  exact RingHom.Flat.of_bijective integerOneEquiv.bijective

private abbrev IntegerZeroQuotient := Source ℤ 0 ⧸ hankelIdeal ℤ 0

private def retainedVariable : IntegerZeroQuotient :=
  Ideal.Quotient.mk (hankelIdeal ℤ 0) (X 0 - 1)

private theorem retainedVariable_ne_zero : retainedVariable ≠ 0 := by
  intro h
  have hp : (X (0 : Fin 1) - 1 : Source ℤ 0) ∈ hankelIdeal ℤ 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  simp only [hankelIdeal_zero, Ideal.mem_bot] at hp
  have hc := congrArg
    (fun p : Source ℤ 0 => MvPolynomial.constantCoeff p) hp
  simp at hc

private theorem retainedVariable_image : rawQuotientMap ℤ 0 retainedVariable = 0 := by
  simp [retainedVariable, rawQuotientMap_mk, rncMap_X, coordinateExponent]

private theorem integer_zero_not_flat : ¬ @Module.Flat IntegerZeroQuotient (Target ℤ) _ _
    (@Algebra.toModule _ _ _ _ (rawQuotientMap ℤ 0).toAlgebra) := by
  intro h
  let : Algebra IntegerZeroQuotient (Target ℤ) := (rawQuotientMap ℤ 0).toAlgebra
  let : Module.Flat IntegerZeroQuotient (Target ℤ) := h
  let : (hankelIdeal ℤ 0).IsPrime := by
    rw [hankelIdeal_zero]
    infer_instance
  have hreg : IsSMulRegular IntegerZeroQuotient retainedVariable := by
    intro x y hxy
    exact mul_left_cancel₀ retainedVariable_ne_zero hxy
  have ht : IsSMulRegular (Target ℤ)
      (algebraMap IntegerZeroQuotient (Target ℤ) retainedVariable) := hreg.of_flat
  have hz : algebraMap IntegerZeroQuotient (Target ℤ) retainedVariable = 0 :=
    retainedVariable_image
  rw [hz] at ht
  exact (one_ne_zero : (1 : Target ℤ) ≠ 0) (ht (by simp))

namespace DegreeTwo

private abbrev R := ZMod 4
private abbrev Q := Source R 2 ⧸ hankelIdeal R 2
private abbrev B := Target R
private def φ : Q →+* B := rawQuotientMap R 2
private def ε : Q →+* R := MvPolynomial.constantCoeff.comp φ

local instance : Algebra Q B := φ.toAlgebra
local instance : Module Q B := @Algebra.toModule _ _ _ _ φ.toAlgebra
local instance : Algebra Q R := ε.toAlgebra
local instance : Module Q R := @Algebra.toModule _ _ _ _ ε.toAlgebra

private def a : Q := Ideal.Quotient.mk (hankelIdeal R 2) (X 0)
private def b : Q := Ideal.Quotient.mk (hankelIdeal R 2) (X 1)
private def coordinateIdeal : Ideal Q := Ideal.span {a, b}
private def ia : coordinateIdeal := ⟨a, Ideal.subset_span (by simp)⟩
private def ib : coordinateIdeal := ⟨b, Ideal.subset_span (by simp)⟩

private theorem no_linear_exponent (i : Fin 3) (j : Fin 2) :
    ¬ coordinateExponent 2 i ≤ Finsupp.single j 1 := by
  fin_cases i <;> fin_cases j
  all_goals
    intro h
    have h0 := h (0 : Fin 2)
    have h1 := h (1 : Fin 2)
    norm_num [coordinateExponent] at h0 <;>
      norm_num [coordinateExponent] at h1

private theorem no_linear_raw (p : Source R 2) (j : Fin 2) :
    (rncMap R 2 p).coeff (Finsupp.single j 1) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hj : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single j 1 := by simp [eq_comm]
    simp [hj]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | mul_X p i _ =>
    rw [map_mul, rncMap_X, coeff_mul_monomial', ite_eq_right (no_linear_exponent i j)]

private theorem no_linear (q : Q) (j : Fin 2) :
    (φ q).coeff (Finsupp.single j 1) = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact no_linear_raw p j

private theorem constant_on_ideal (i : coordinateIdeal) : (φ i).coeff 0 = 0 := by
  have hker : coordinateIdeal ≤ RingHom.ker ε := by
    apply Ideal.span_le.mpr
    rintro q (rfl | rfl)
    · change (rncMap R 2 (X 0)).coeff 0 = 0
      simp [rncMap_X, coordinateExponent]
    · change (rncMap R 2 (X 1)).coeff 0 = 0
      simp [rncMap_X, coordinateExponent]
  change ε (i : Q) = 0
  exact RingHom.mem_ker.mp (hker i.property)

-- Only the two fixed coefficients needed by the detector occur here.
private def α : coordinateIdeal →ₗ[Q] R where
  toFun i := (φ i).coeff (Finsupp.single 0 2)
  map_add' i j := by
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Submodule.coe_add]
  map_smul' q i := by
    change (φ (q * (i : Q))).coeff (Finsupp.single 0 2) =
      ε q * (φ i).coeff (Finsupp.single 0 2)
    rw [map_mul]
    simp [coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ,
      Finset.sum_insert, Finset.sum_singleton, Finsupp.single_eq_single_iff,
      no_linear q 0, constant_on_ideal i, ε, MvPolynomial.constantCoeff_eq]

private def β : B →ₗ[Q] R where
  toFun p := p.coeff (Finsupp.single 1 1)
  map_add' p q := (MvPolynomial.coeffAddMonoidHom _).map_add p q
  map_smul' q p := by
    change (φ q * p).coeff (Finsupp.single 1 1) =
      ε q * p.coeff (Finsupp.single 1 1)
    simp [coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ,
      no_linear q 1, ε, MvPolynomial.constantCoeff_eq]

private def witness : coordinateIdeal ⊗[Q] B :=
  ia ⊗ₜ[Q] X 1 - ib ⊗ₜ[Q] X 0

private def detector : coordinateIdeal ⊗[Q] B →ₗ[Q] R :=
  (LinearMap.mul' Q R).comp (TensorProduct.map α β)

private theorem detector_witness : detector witness = 1 := by
  have hβ (p : B) : β p = p.coeff (Finsupp.single 1 1) := rfl
  simp [detector, witness, α, hβ, ia, ib, a, φ, rawQuotientMap_mk,
    rncMap_X, coordinateExponent]

private theorem witness_in_kernel : coordinateIdeal.subtype.rTensor B witness = 0 := by
  apply (TensorProduct.lid Q B).injective
  simp only [witness, map_sub, map_zero, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  change φ a * X 1 - φ b * X 0 = 0
  have ha : φ a = X (0 : Fin 2) ^ 2 := by
    simp [φ, a, rawQuotientMap_mk, rncMap_X, coordinateExponent, X_pow_eq_monomial]
  have hb : φ b = X (0 : Fin 2) * X 1 := by
    simp [φ, b, rawQuotientMap_mk, coordinateExponent, X,
      monomial_mul_monomial]
  rw [ha, hb, pow_two, mul_right_comm (X (0 : Fin 2)) (X 1) (X 0), sub_self]

private theorem not_flat : ¬ @Module.Flat Q B _ _ (@Algebra.toModule _ _ _ _ φ.toAlgebra) := by
  intro h
  let : Module.Flat Q B := h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
    coordinateIdeal.subtype Subtype.val_injective
  have hw : witness = 0 := hinj (by simpa only [map_zero] using witness_in_kernel)
  have hz : (1 : R) = 0 := by
    simpa only [detector_witness, map_zero] using congrArg detector hw
  exact (by decide : (1 : ZMod 4) ≠ 0) hz

private theorem two_ne_zero : (2 : ZMod 4) ≠ 0 := by decide
private theorem two_sq_eq_zero : (2 : ZMod 4) ^ 2 = 0 := by decide

end DegreeTwo

private theorem zero_ring_zero_flat : @Module.Flat (Source (ZMod 1) 0 ⧸ hankelIdeal (ZMod 1) 0)
    (Target (ZMod 1)) _ _
    (@Algebra.toModule _ _ _ _ (rawQuotientMap (ZMod 1) 0).toAlgebra) := by
  change (rawQuotientMap (ZMod 1) 0).Flat
  apply RingHom.Flat.of_bijective
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  · intro p
    exact ⟨0, Subsingleton.elim _ _⟩
