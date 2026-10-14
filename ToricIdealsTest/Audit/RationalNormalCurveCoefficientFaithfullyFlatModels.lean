/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.AxisProjection
import ToricIdeals.RationalNormalCurve.CoefficientAlgebra

/-!
# Faithfully flat coefficient modules of full Hankel quotients

The coefficient action on `Source R n ⧸ hankelIdeal R n` is the canonical
quotient-algebra action. The coefficient augmentation fixes constants and sends
all quotient variables to zero. Over `ZMod 4`, the quotient retains a nonzero
square-zero constant and is faithfully flat in degrees zero, one and two.
Integer coefficients and lifted integer coefficients give further examples.
Over `ZMod 1`, transport from finitely supported functions on a singleton gives
faithful flatness in every degree, although the full quotient is a subsingleton.

The degree-zero integer quotient retains its polynomial variable: the axis
projection and polynomial section are inverse, the augmentation kills the
variable, and the monomial parametrization sends it to `1`. Tensoring with the
degree-two quotient over `ZMod 4` preserves and reflects injectivity for arbitrary
linear maps between modules in independent universes, and detects the kernel of
multiplication by `2`.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.CoefficientAlgebra`,
  for freeness of the full quotient with its coefficient action.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Augmentation` and
  `ToricIdeals.RationalNormalCurve.AxisProjection`, for the coefficient
  augmentation and the polynomial section and projection.
* Mathlib contributors, `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, for faithfully flat free
  modules, transport along linear equivalences, and tensor injectivity.
-/

namespace ToricIdeals.RationalNormalCurve.CoefficientFaithfullyFlatModels

noncomputable section

universe u v w

/-- The augmentation splits the coefficient unit, and the scalar action is
multiplication by the canonical coefficient class. -/
private theorem coefficient_unit_and_action (R : Type u) [CommRing R] (n : ℕ)
    (r : R) (q : Source R n ⧸ hankelIdeal R n) :
    quotientAugmentation R n (algebraMap R (Source R n ⧸ hankelIdeal R n) r) = r ∧
      r • q = algebraMap R (Source R n ⧸ hankelIdeal R n) r * q := by
  refine ⟨?_, Algebra.smul_def r q⟩
  simpa only [Algebra.algebraMap_self_apply] using (quotientAugmentation R n).commutes r

/-- Non-domain coefficients have a nonzero square-zero constant in the full
quotient, in every degree. -/
private theorem mod_four_nilpotent_constants (n : ℕ) :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧ ¬ IsDomain (ZMod 4) ∧
      algebraMap (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) 2 ≠ 0 ∧
      (algebraMap (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) 2) ^ 2 = 0 := by
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨hne, hsq, ?_, ?_, ?_⟩
  · intro hR
    let : IsDomain (ZMod 4) := hR
    have hmul : (2 : ZMod 4) * 2 = 0 := by decide
    exact (mul_eq_zero.mp hmul).elim hne hne
  · intro hzero
    apply hne
    have h := congrArg (quotientAugmentation (ZMod 4) n) hzero
    simpa only [(coefficient_unit_and_action (ZMod 4) n 2 0).1, map_zero] using h
  · rw [← map_pow, hsq, map_zero]

/-- The full one-variable quotient over nonreduced coefficients is faithfully flat. -/
private theorem mod_four_degree_zero_quotient_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 4) (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let : Module.Free (ZMod 4) (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) :=
    quotient_free (ZMod 4) 0
  let : Nontrivial (Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) :=
    (quotientAugmentation (ZMod 4) 0).toRingHom.domain_nontrivial
  infer_instance

/-- The relation-free degree-one quotient over `ZMod 4` is faithfully flat. -/
private theorem mod_four_degree_one_quotient_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 4) (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let : Module.Free (ZMod 4) (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) :=
    quotient_free (ZMod 4) 1
  let : Nontrivial (Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) :=
    (quotientAugmentation (ZMod 4) 1).toRingHom.domain_nontrivial
  infer_instance

/-- The degree-two quotient, which has a Hankel relation, is faithfully flat
for its coefficient action over `ZMod 4`. -/
private theorem mod_four_degree_two_quotient_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let : Module.Free (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) :=
    quotient_free (ZMod 4) 2
  let : Nontrivial (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) :=
    (quotientAugmentation (ZMod 4) 2).toRingHom.domain_nontrivial
  infer_instance

/-- Over zero coefficients the full quotient is faithfully flat in every degree
and every quotient element is zero. -/
private theorem zero_coefficients_quotient_faithfullyFlat (n : ℕ) :
    Module.FaithfullyFlat (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) ∧
      ∀ q : Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n, q = 0 := by
  constructor
  · let : Module.FaithfullyFlat (ZMod 1) (Unit →₀ ZMod 1) :=
      Module.FaithfullyFlat.finsupp (ZMod 1) Unit
    exact Module.FaithfullyFlat.of_linearEquiv (ZMod 1) (Unit →₀ ZMod 1)
      (Module.subsingletonEquiv (ZMod 1)
        (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) Unit)
  · let : Subsingleton (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
      Module.subsingleton (ZMod 1) (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n)
    exact fun q => Subsingleton.elim q 0

/-- The full degree-zero quotient is faithfully flat over the integers. -/
private theorem integer_degree_zero_quotient_faithfullyFlat :
    Module.FaithfullyFlat ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) := by
  let : Module.Free ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) := quotient_free ℤ 0
  let : Nontrivial (Source ℤ 0 ⧸ hankelIdeal ℤ 0) :=
    (quotientAugmentation ℤ 0).toRingHom.domain_nontrivial
  infer_instance

/-- The degree-two integer quotient is faithfully flat for the coefficient action. -/
private theorem integer_degree_two_quotient_faithfullyFlat :
    Module.FaithfullyFlat ℤ (Source ℤ 2 ⧸ hankelIdeal ℤ 2) := by
  let : Module.Free ℤ (Source ℤ 2 ⧸ hankelIdeal ℤ 2) := quotient_free ℤ 2
  let : Nontrivial (Source ℤ 2 ⧸ hankelIdeal ℤ 2) :=
    (quotientAugmentation ℤ 2).toRingHom.domain_nontrivial
  infer_instance

/-- The coefficient universe may be lifted independently of the quotient degree. -/
private theorem lifted_integer_degree_two_quotient_faithfullyFlat :
    Module.FaithfullyFlat (ULift.{v} ℤ)
      (Source (ULift.{v} ℤ) 2 ⧸ hankelIdeal (ULift.{v} ℤ) 2) := by
  let : Module.Free (ULift.{v} ℤ)
      (Source (ULift.{v} ℤ) 2 ⧸ hankelIdeal (ULift.{v} ℤ) 2) :=
    quotient_free (ULift.{v} ℤ) 2
  let : Nontrivial (Source (ULift.{v} ℤ) 2 ⧸ hankelIdeal (ULift.{v} ℤ) 2) :=
    (quotientAugmentation (ULift.{v} ℤ) 2).toRingHom.domain_nontrivial
  infer_instance

/-- The degree-zero quotient is the full polynomial algebra: its variable
survives, although augmentation kills it and parametrization sends it to `1`. -/
private theorem integer_degree_zero_polynomial_variable :
    hankelIdeal ℤ 0 = ⊥ ∧
      (axisSection ℤ 0).comp (axisProjection ℤ 0) =
        AlgHom.id ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1)) ≠ 0 ∧
      quotientAugmentation ℤ 0
        (Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1))) = 0 ∧
      rncMap ℤ 0 (MvPolynomial.X (0 : Fin 1)) = 1 := by
  refine ⟨hankelIdeal_zero ℤ, axisSection_comp_axisProjection_zero ℤ, ?_, ?_, ?_⟩
  · intro hzero
    apply Polynomial.X_ne_zero (R := ℤ)
    apply axisSection_injective ℤ 0
    simpa only [axisSection_X, map_zero] using hzero
  · rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_X]
  · simp [rncMap_X, coordinateExponent]

/-- Tensoring with the degree-two `ZMod 4` quotient preserves and reflects
injectivity, with independent source and target module universes. -/
private theorem mod_four_degree_two_tensor_injective_iff
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 4) M] [Module (ZMod 4) N] (f : M →ₗ[ZMod 4] N) :
    Function.Injective (TensorProduct.map
      (LinearMap.id : (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) →ₗ[ZMod 4]
        (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2)) f) ↔ Function.Injective f := by
  let : Module.FaithfullyFlat (ZMod 4)
      (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) :=
    mod_four_degree_two_quotient_faithfullyFlat
  simpa only [LinearMap.lTensor_def] using
    Module.FaithfullyFlat.lTensor_injective_iff_injective (ZMod 4)
      (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) f

/-- The tensor unit is injective for any `ZMod 4` module, without a flatness
hypothesis on that module or an action by the quotient. -/
private theorem mod_four_degree_two_tensor_unit_injective
    (M : Type v) [AddCommGroup M] [Module (ZMod 4) M] :
    Function.Injective (TensorProduct.mk (ZMod 4)
      (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) M 1) := by
  let : Module.FaithfullyFlat (ZMod 4)
      (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) :=
    mod_four_degree_two_quotient_faithfullyFlat
  exact Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := ZMod 4) (B := Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) M

/-- Tensoring detects the nonzero kernel of multiplication by `2`, rather than
requiring the coefficient-linear map to be injective. -/
private theorem mod_four_degree_two_tensor_detects_double_kernel :
    ¬ Function.Injective (TensorProduct.map
      (LinearMap.id : (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) →ₗ[ZMod 4]
        (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2))
      ((2 : ZMod 4) • (LinearMap.id : ZMod 4 →ₗ[ZMod 4] ZMod 4))) := by
  intro hinj
  have hreflect := (mod_four_degree_two_tensor_injective_iff (ZMod 4) (ZMod 4) _).mp hinj
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  apply hne
  apply hreflect
  change (2 : ZMod 4) * 2 = 2 * 0
  decide

end

end ToricIdeals.RationalNormalCurve.CoefficientFaithfullyFlatModels
