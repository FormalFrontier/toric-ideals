/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ToricIdeals.RationalNormalCurve.ParametrizationFinite

/-!
# A finite parametrization module after a closed quotient

Over `ZMod 4`, the degree-two parametrization target remains finite over
its full source after quotienting by the first target variable.
The scalar action is induced by the composite of the parametrization and
the quotient map. The second variable is not killed: this quotient is the
polynomial ring in that variable over `ZMod 4`. Evaluation at zero descends
to the same quotient and detects its nonzero square-zero constant `2`.

## References

* `ToricIdeals.RationalNormalCurve.ParametrizationFinite`, for
  `rncMap_moduleFinite_iff`.
* Mathlib contributors, `Mathlib.RingTheory.Finiteness.Basic` and
  `Mathlib.RingTheory.Ideal.Quotient.Defs`, for finiteness under a surjection
  and the quotient universal property.
-/

open ToricIdeals.RationalNormalCurve

private noncomputable abbrev axisIdeal : Ideal (Target (ZMod 4)) :=
  Ideal.span {MvPolynomial.X (0 : Fin 2)}

private abbrev AxisQuotient := Target (ZMod 4) ⧸ axisIdeal

/-- Closed-quotient stability for the degree-two parametrization. -/
private theorem axisQuotient_moduleFinite :
    @Module.Finite (Source (ZMod 4) 2) AxisQuotient _ _
      (@Algebra.toModule (Source (ZMod 4) 2) AxisQuotient _ _
        ((Ideal.Quotient.mk axisIdeal).comp (rncMap (ZMod 4) 2)).toAlgebra) := by
  let : Algebra (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    (rncMap (ZMod 4) 2).toAlgebra
  let : Algebra (Target (ZMod 4)) AxisQuotient :=
    (Ideal.Quotient.mk axisIdeal).toAlgebra
  let : Algebra (Source (ZMod 4) 2) AxisQuotient :=
    ((Ideal.Quotient.mk axisIdeal).comp (rncMap (ZMod 4) 2)).toAlgebra
  let : Module (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    @Algebra.toModule (Source (ZMod 4) 2) (Target (ZMod 4)) _ _
      (rncMap (ZMod 4) 2).toAlgebra
  let : Module (Target (ZMod 4)) AxisQuotient :=
    @Algebra.toModule (Target (ZMod 4)) AxisQuotient _ _
      (Ideal.Quotient.mk axisIdeal).toAlgebra
  let : Module (Source (ZMod 4) 2) AxisQuotient :=
    @Algebra.toModule (Source (ZMod 4) 2) AxisQuotient _ _
      ((Ideal.Quotient.mk axisIdeal).comp (rncMap (ZMod 4) 2)).toAlgebra
  let qAlg : Target (ZMod 4) →ₐ[Source (ZMod 4) 2] AxisQuotient :=
    { Ideal.Quotient.mk axisIdeal with
      commutes' := by intro s; rfl }
  let : Module.Finite (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    (rncMap_moduleFinite_iff (ZMod 4) 2).mpr (Or.inl (by decide))
  exact Module.Finite.of_surjective qAlg.toLinearMap Ideal.Quotient.mk_surjective

private def evalZero : Target (ZMod 4) →+* ZMod 4 :=
  MvPolynomial.eval₂Hom (RingHom.id (ZMod 4)) (fun _ => 0)

private theorem axisIdeal_le_evalZero_ker : axisIdeal ≤ RingHom.ker evalZero := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  simp [evalZero]

/-- Evaluation at zero factors through the closed quotient. -/
private noncomputable def quotientEvalZero : AxisQuotient →+* ZMod 4 :=
  Ideal.Quotient.lift axisIdeal evalZero fun p hp =>
    RingHom.mem_ker.mp (axisIdeal_le_evalZero_ker hp)

private noncomputable def quotientTwo : AxisQuotient :=
  Ideal.Quotient.mk axisIdeal (MvPolynomial.C (2 : ZMod 4))

private theorem quotientTwo_ne_zero : quotientTwo ≠ 0 := by
  intro h
  have htwo : (2 : ZMod 4) = 0 := by
    have heval := congrArg quotientEvalZero h
    simpa [quotientEvalZero, quotientTwo, evalZero] using heval
  exact (by decide : (2 : ZMod 4) ≠ 0) htwo

private theorem quotientTwo_sq : quotientTwo ^ 2 = 0 := by
  have htwo : (2 : ZMod 4) ^ 2 = 0 := by decide
  calc
    quotientTwo ^ 2 =
        Ideal.Quotient.mk axisIdeal (MvPolynomial.C ((2 : ZMod 4) ^ 2)) := by
      simp [quotientTwo]
    _ = 0 := by simp [htwo]

/-- The same quotient has a nonzero square-zero constant. -/
private theorem axisQuotient_nonzero_nilpotent :
    quotientTwo ≠ 0 ∧ quotientTwo ^ 2 = 0 :=
  ⟨quotientTwo_ne_zero, quotientTwo_sq⟩
