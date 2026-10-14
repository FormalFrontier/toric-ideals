/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import ToricIdeals

/-!
# Coefficient extension reflects injectivity

The full Hankel quotient is faithfully flat for its canonical coefficient
action. These root-import clients install that theorem locally and directly
use Mathlib's tensor injectivity reflection and canonical unit injection.
The test modules have independent universes and need neither flatness nor an
action by the quotient. The unit sends `m` to `1 ⊗ₜ m`.

The integer degree-zero unit is nonzero, the degree-two unit over `ZMod 4`
retains the nonzero nilpotent coefficient `2`, and tensoring detects the kernel
of multiplication by `2`. Zero coefficients are also allowed in every degree.
These clients use the public theorem; the separate coefficient models retain
their independent proofs.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.CoefficientAlgebra`,
  for faithful flatness of the full quotient for the coefficient action.
* Mathlib contributors, `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, for tensor injectivity
  reflection and injectivity of the canonical tensor unit.
-/

namespace ToricIdeals.RationalNormalCurve.CoefficientFaithfullyFlatClients

noncomputable section

universe u v w

/-- Coefficient extension preserves and reflects injectivity for arbitrary
linear maps, in independent source and target module universes. -/
private theorem coefficient_tensor_injective_iff (R : Type u) [CommRing R] (n : ℕ)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Function.Injective (TensorProduct.map
      (LinearMap.id : (Source R n ⧸ hankelIdeal R n) →ₗ[R]
        (Source R n ⧸ hankelIdeal R n)) f) ↔ Function.Injective f := by
  let : Module.FaithfullyFlat R (Source R n ⧸ hankelIdeal R n) :=
    quotient_faithfullyFlat R n
  simpa only [LinearMap.lTensor_def] using
    Module.FaithfullyFlat.lTensor_injective_iff_injective R
      (Source R n ⧸ hankelIdeal R n) f

/-- The canonical tensor unit is injective without flatness of the test module
or a quotient action on it, also when its universe differs from that of `R`. -/
private theorem coefficient_tensor_unit_injective (R : Type u) [CommRing R] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (TensorProduct.mk R (Source R n ⧸ hankelIdeal R n) M 1) := by
  let : Module.FaithfullyFlat R (Source R n ⧸ hankelIdeal R n) :=
    quotient_faithfullyFlat R n
  exact Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := R) (B := Source R n ⧸ hankelIdeal R n) M

/-- The degree-zero full polynomial quotient gives a nonzero tensor unit. -/
private theorem integer_degree_zero_tensor_unit_nonzero :
    TensorProduct.mk ℤ (Source ℤ 0 ⧸ hankelIdeal ℤ 0) ℤ 1 1 ≠ 0 := by
  intro hzero
  apply (one_ne_zero : (1 : ℤ) ≠ 0)
  apply coefficient_tensor_unit_injective ℤ 0 ℤ
  simpa only [map_zero] using hzero

/-- Coefficient extension does not kill the nonzero square-zero coefficient `2`. -/
private theorem mod_four_degree_two_tensor_retains_two :
    TensorProduct.mk (ZMod 4)
      (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) (ZMod 4) 1 2 ≠ 0 := by
  intro hzero
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  apply htwo
  apply coefficient_tensor_unit_injective (ZMod 4) 2 (ZMod 4)
  simpa only [map_zero] using hzero

/-- The injectivity iff detects the nonzero kernel of multiplication by `2`. -/
private theorem mod_four_degree_two_tensor_detects_double_kernel :
    ¬ Function.Injective (TensorProduct.map
      (LinearMap.id : (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) →ₗ[ZMod 4]
        (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2))
      ((2 : ZMod 4) • (LinearMap.id : ZMod 4 →ₗ[ZMod 4] ZMod 4))) := by
  intro hinj
  have hreflect := (coefficient_tensor_injective_iff (ZMod 4) 2
    (ZMod 4) (ZMod 4) _).mp hinj
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  apply htwo
  apply hreflect
  change (2 : ZMod 4) * 2 = 2 * 0
  decide

/-- The public theorem also gives unit injection over zero coefficients in
all degrees; all elements of any such test module are zero. -/
private theorem zero_coefficients_tensor_unit (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (ZMod 1) M] :
    Function.Injective (TensorProduct.mk (ZMod 1)
      (Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) M 1) ∧
      ∀ m : M, m = 0 := by
  refine ⟨coefficient_tensor_unit_injective (ZMod 1) n M, ?_⟩
  let : Subsingleton M := Module.subsingleton (ZMod 1) M
  exact fun m => Subsingleton.elim m 0

end

end ToricIdeals.RationalNormalCurve.CoefficientFaithfullyFlatClients
