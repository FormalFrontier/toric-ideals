/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import ToricIdeals.RationalNormalCurve

/-!
# Fixed models for finite parametrization modules

The scalar semiring is the source polynomial semiring, acting on the two-variable
polynomial target through the monomial parametrization. In degree zero the
single source variable acts as one. These examples distinguish that action
from the coefficient action. Degree two over `ZMod 4` also gives a finite
module with a nonzero square-zero coefficient.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

private theorem nat_zero_not_finite :
    ¬ @Module.Finite (Source ℕ 0) (Target ℕ) _ _
      (@Algebra.toModule (Source ℕ 0) (Target ℕ) _ _
        (rncMap ℕ 0).toAlgebra) := by
  let e : Source ℕ 0 →+* ℕ :=
    eval₂Hom (RingHom.id ℕ) (fun _ => 1)
  have hfactor : rncMap ℕ 0 = C.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e]
    · intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      simp [e, coordinateExponent]
  have he : Function.Surjective e := by
    intro r
    exact ⟨C r, by simp [e]⟩
  let : Algebra (Source ℕ 0) ℕ := e.toAlgebra
  let : Algebra (Source ℕ 0) (Target ℕ) := (rncMap ℕ 0).toAlgebra
  let : Module (Source ℕ 0) ℕ :=
    @Algebra.toModule (Source ℕ 0) ℕ _ _ e.toAlgebra
  let : Module (Source ℕ 0) (Target ℕ) :=
    @Algebra.toModule (Source ℕ 0) (Target ℕ) _ _
      (rncMap ℕ 0).toAlgebra
  let : IsScalarTower (Source ℕ 0) ℕ (Target ℕ) :=
    IsScalarTower.of_algebraMap_eq' hfactor
  intro h
  let : Module.Finite (Source ℕ 0) (Target ℕ) := h
  let : Module.Finite ℕ (Target ℕ) :=
    Module.Finite.of_restrictScalars_finite (Source ℕ 0) ℕ (Target ℕ)
  have hf : Finite (Fin 2 →₀ ℕ) :=
    Module.Finite.finite_basis (MvPolynomial.basisMonomials (Fin 2) ℕ)
  exact Infinite.not_finite hf

private theorem nat_one_finite :
    @Module.Finite (Source ℕ 1) (Target ℕ) _ _
      (@Algebra.toModule (Source ℕ 1) (Target ℕ) _ _
        (rncMap ℕ 1).toAlgebra) := by
  have hid : rncMap ℕ 1 = RingHom.id (Target ℕ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      change rncMap ℕ 1 (X i) = X i
      rw [rncMap_X, ← rncExponent_single 1 i, rncExponent_one]
      rfl
  rw [hid]
  infer_instance

private theorem modFour_nonzero_square_zero :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  decide

private theorem modFour_two_finite :
    @Module.Finite (Source (ZMod 4) 2) (Target (ZMod 4)) _ _
      (@Algebra.toModule (Source (ZMod 4) 2) (Target (ZMod 4)) _ _
        (rncMap (ZMod 4) 2).toAlgebra) := by
  let f : Source (ZMod 4) 2 →+* Target (ZMod 4) := rncMap (ZMod 4) 2
  have hcomp : f.comp (C : ZMod 4 →+* Source (ZMod 4) 2) = C := by
    apply RingHom.ext
    intro r
    exact rncMap_C (ZMod 4) 2 r
  have htype : f.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType
      (f := (C : ZMod 4 →+* Source (ZMod 4) 2))
    rw [hcomp]
    change (algebraMap (ZMod 4) (Target (ZMod 4))).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let : Algebra (Source (ZMod 4) 2) (Target (ZMod 4)) := f.toAlgebra
  have hleft : IsIntegral (Source (ZMod 4) 2)
      (X (0 : Fin 2) : Target (ZMod 4)) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    have hx : f (X (0 : Fin 3)) = (X (0 : Fin 2)) ^ 2 := by
      simp [f, coordinateExponent, X_pow_eq_monomial]
    rw [← hx]
    exact isIntegral_algebraMap
  have hright : IsIntegral (Source (ZMod 4) 2)
      (X (1 : Fin 2) : Target (ZMod 4)) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    have hx : f (X (2 : Fin 3)) = (X (1 : Fin 2)) ^ 2 := by
      simp [f, coordinateExponent, X_pow_eq_monomial]
    rw [← hx]
    exact isIntegral_algebraMap
  have hint : f.IsIntegral := by
    intro p
    change IsIntegral (Source (ZMod 4) 2) p
    induction p using MvPolynomial.induction_on with
    | C r =>
        have hc : f (C r) = C r := rncMap_C (ZMod 4) 2 r
        rw [← hc]
        exact isIntegral_algebraMap
    | add p q hp hq => exact hp.add hq
    | mul_X p i hp =>
        apply hp.mul
        fin_cases i
        · exact hleft
        · exact hright
  exact hint.to_finite htype

private theorem zeroRing_zero_finite :
    @Module.Finite (Source (ZMod 1) 0) (Target (ZMod 1)) _ _
      (@Algebra.toModule (Source (ZMod 1) 0) (Target (ZMod 1)) _ _
        (rncMap (ZMod 1) 0).toAlgebra) := by
  let : Algebra (Source (ZMod 1) 0) (Target (ZMod 1)) :=
    (rncMap (ZMod 1) 0).toAlgebra
  have : Subsingleton (Target (ZMod 1)) := inferInstance
  exact Module.Finite.of_finite
