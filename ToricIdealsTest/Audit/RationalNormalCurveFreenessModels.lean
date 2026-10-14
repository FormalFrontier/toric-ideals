/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import ToricIdeals.RationalNormalCurve.Injectivity

/-!
# Source-module freeness models for rational normal parametrizations

These models use the full polynomial source as scalars and the full bivariate polynomial
semiring as the module. Scalar multiplication is induced by the monomial parametrization:
`p • q = rncMap R n p * q`.

The degree-zero and degree-two natural-number models are not free; degree one is free.
The same boundaries are tested over the additively noncancellative semiring `WithTop ℕ`.
Nonzero nilpotents in `ZMod 4` coexist with degree-one freeness, whereas `ZMod 1` gives
zero polynomial carriers and an empty basis in every degree. Lifted natural numbers
supply degree-one models in arbitrary coefficient universes.

These basis, collision and action arguments are independent of the freeness
classifier in `ToricIdeals.RationalNormalCurve.Freeness`. The separate
`RationalNormalCurveFreenessClient` module applies that classifier.

## References

* Mathlib's free-module, faithful-action and algebra-map APIs provide the basis and
  scalar-action arguments.
* `ToricIdeals.RationalNormalCurve.Injectivity` provides the injectivity obstruction
  for the full monomial parametrization over commutative semirings.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve.FreenessModels

universe u v

private theorem canonical_smul (R : Type u) [CommSemiring R] (n : ℕ)
    (p : Source R n) (q : Target R) :
    @SMul.smul (Source R n) (Target R)
      (@Algebra.toModule (Source R n) (Target R) inferInstance inferInstance
        (rncMap R n).toAlgebra).toSMul p q = rncMap R n p * q :=
  RingHom.smul_toAlgebra (rncMap R n) p q

private theorem degree_one_map_eq_id (R : Type u) [CommSemiring R] :
    rncMap R 1 = RingHom.id (Target R) := by
  have h : rncExponent 1 = AddMonoidHom.id (Fin 2 →₀ ℕ) := by
    apply AddMonoidHom.ext
    intro d
    exact rncExponent_one d
  rw [rncMap, h]
  simp only [AddMonoidAlgebra.mapDomainRingHom_id]

-- Identify the module data, rather than asking instance priority to identify the action.
private theorem degree_one_module_eq_self (R : Type u) [CommSemiring R] :
    @Algebra.toModule (Source R 1) (Target R) inferInstance inferInstance
      (rncMap R 1).toAlgebra = (inferInstance : Module (Target R) (Target R)) := by
  apply Module.ext'
  intro p q
  change rncMap R 1 p * q = p * q
  rw [degree_one_map_eq_id]
  rfl

private theorem nat_zero_collision :
    (MvPolynomial.X (0 : Fin 1) : Source ℕ 0) ≠ 1 ∧
      rncMap ℕ 0 (MvPolynomial.X (0 : Fin 1)) = rncMap ℕ 0 1 := by
  constructor
  · intro h
    have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
    have hc := congrArg
      (fun p : Source ℕ 0 ↦ p.coeff (Finsupp.single (0 : Fin 1) 1)) h
    rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_one, ite_eq_right (Ne.symm hs)] at hc
    exact one_ne_zero hc
  · simp [coordinateExponent]

private theorem nat_zero_not_free :
    ¬ @Module.Free (Source ℕ 0) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ 0) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 0).toAlgebra) := by
  let : Algebra (Source ℕ 0) (Target ℕ) := (rncMap ℕ 0).toAlgebra
  let : Module (Source ℕ 0) (Target ℕ) :=
    @Algebra.toModule (Source ℕ 0) (Target ℕ) inferInstance inferInstance
      (rncMap ℕ 0).toAlgebra
  intro h
  let : Module.Free (Source ℕ 0) (Target ℕ) := h
  let : Nontrivial (Target ℕ) := MvPolynomial.nontrivial_of_nontrivial (Fin 2) ℕ
  let : FaithfulSMul (Source ℕ 0) (Target ℕ) :=
    Module.Free.instFaithfulSMulOfNontrivial _ _
  have hi : Function.Injective (rncMap ℕ 0) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (FaithfulSMul.algebraMap_injective (Source ℕ 0) (Target ℕ))
  exact nat_zero_collision.1 (hi nat_zero_collision.2)

private theorem nat_one_free :
    @Module.Free (Source ℕ 1) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ 1) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 1).toAlgebra) := by
  rw [degree_one_module_eq_self]
  exact Module.Free.self _

private theorem nat_one_action_and_nonzero (p : Source ℕ 1) (q : Target ℕ) :
    @SMul.smul (Source ℕ 1) (Target ℕ)
      (@Algebra.toModule (Source ℕ 1) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 1).toAlgebra).toSMul p q = p * q ∧
      (MvPolynomial.X (0 : Fin 2) : Target ℕ) ≠ 0 := by
  constructor
  · rw [canonical_smul, degree_one_map_eq_id]
    rfl
  · exact MvPolynomial.X_ne_zero _

private theorem nat_two_not_free :
    ¬ @Module.Free (Source ℕ 2) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ 2) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 2).toAlgebra) := by
  let : Algebra (Source ℕ 2) (Target ℕ) := (rncMap ℕ 2).toAlgebra
  let : Module (Source ℕ 2) (Target ℕ) :=
    @Algebra.toModule (Source ℕ 2) (Target ℕ) inferInstance inferInstance
      (rncMap ℕ 2).toAlgebra
  intro h
  let : Module.Free (Source ℕ 2) (Target ℕ) := h
  let : Nontrivial (Target ℕ) := MvPolynomial.nontrivial_of_nontrivial (Fin 2) ℕ
  let : FaithfulSMul (Source ℕ 2) (Target ℕ) :=
    Module.Free.instFaithfulSMulOfNontrivial _ _
  have hi : Function.Injective (rncMap ℕ 2) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (FaithfulSMul.algebraMap_injective (Source ℕ 2) (Target ℕ))
  rcases (rncMap_injective_iff ℕ 2).mp hi with hn | hR
  · exact (by decide : (2 : ℕ) ≠ 1) hn
  · exact zero_ne_one (@Subsingleton.elim ℕ hR 0 1)

private theorem mod_four_nilpotent :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  constructor <;> decide

private theorem mod_four_one_free :
    @Module.Free (Source (ZMod 4) 1) (Target (ZMod 4)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 4) 1) (Target (ZMod 4)) inferInstance inferInstance
        (rncMap (ZMod 4) 1).toAlgebra) := by
  rw [degree_one_module_eq_self]
  exact Module.Free.self _

private theorem mod_four_two_not_free :
    ¬ @Module.Free (Source (ZMod 4) 2) (Target (ZMod 4)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 4) 2) (Target (ZMod 4)) inferInstance inferInstance
        (rncMap (ZMod 4) 2).toAlgebra) := by
  let : Algebra (Source (ZMod 4) 2) (Target (ZMod 4)) := (rncMap (ZMod 4) 2).toAlgebra
  let : Module (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    @Algebra.toModule (Source (ZMod 4) 2) (Target (ZMod 4)) inferInstance inferInstance
      (rncMap (ZMod 4) 2).toAlgebra
  intro h
  let : Module.Free (Source (ZMod 4) 2) (Target (ZMod 4)) := h
  let : Nontrivial (ZMod 4) := ⟨⟨2, 0, mod_four_nilpotent.1⟩⟩
  let : Nontrivial (Target (ZMod 4)) :=
    MvPolynomial.nontrivial_of_nontrivial (Fin 2) (ZMod 4)
  let : FaithfulSMul (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    Module.Free.instFaithfulSMulOfNontrivial _ _
  have hi : Function.Injective (rncMap (ZMod 4) 2) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (FaithfulSMul.algebraMap_injective (Source (ZMod 4) 2) (Target (ZMod 4)))
  rcases (rncMap_injective_iff (ZMod 4) 2).mp hi with hn | hR
  · exact (by decide : (2 : ℕ) ≠ 1) hn
  · exact mod_four_nilpotent.1 (@Subsingleton.elim (ZMod 4) hR 2 0)

private theorem mod_one_carriers_zero (n : ℕ)
    (p : Source (ZMod 1) n) (q : Target (ZMod 1)) : p = 0 ∧ q = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

private theorem mod_one_free (n : ℕ) :
    @Module.Free (Source (ZMod 1) n) (Target (ZMod 1)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 1) n) (Target (ZMod 1)) inferInstance inferInstance
        (rncMap (ZMod 1) n).toAlgebra) := by
  let : Module (Source (ZMod 1) n) (Target (ZMod 1)) :=
    @Algebra.toModule (Source (ZMod 1) n) (Target (ZMod 1)) inferInstance inferInstance
      (rncMap (ZMod 1) n).toAlgebra
  exact Module.Free.of_subsingleton (Source (ZMod 1) n) (Target (ZMod 1))

private theorem ulift_nat_one_free :
    @Module.Free (Source (ULift.{v} ℕ) 1) (Target (ULift.{v} ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (ULift.{v} ℕ) 1) (Target (ULift.{v} ℕ))
        inferInstance inferInstance (rncMap (ULift.{v} ℕ) 1).toAlgebra) := by
  rw [degree_one_module_eq_self]
  exact Module.Free.self _

private theorem withTop_nat_non_cancellation :
    (⊤ : WithTop ℕ) + 0 = ⊤ + 1 ∧ (0 : WithTop ℕ) ≠ 1 := by
  constructor
  · simp only [WithTop.top_add]
  · exact zero_ne_one

private theorem withTop_nat_zero_not_free :
    ¬ @Module.Free (Source (WithTop ℕ) 0) (Target (WithTop ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (WithTop ℕ) 0) (Target (WithTop ℕ))
        inferInstance inferInstance (rncMap (WithTop ℕ) 0).toAlgebra) := by
  let : Algebra (Source (WithTop ℕ) 0) (Target (WithTop ℕ)) :=
    (rncMap (WithTop ℕ) 0).toAlgebra
  let : Module (Source (WithTop ℕ) 0) (Target (WithTop ℕ)) :=
    @Algebra.toModule (Source (WithTop ℕ) 0) (Target (WithTop ℕ))
      inferInstance inferInstance (rncMap (WithTop ℕ) 0).toAlgebra
  intro h
  let : Module.Free (Source (WithTop ℕ) 0) (Target (WithTop ℕ)) := h
  let : Nontrivial (Target (WithTop ℕ)) :=
    MvPolynomial.nontrivial_of_nontrivial (Fin 2) (WithTop ℕ)
  let : FaithfulSMul (Source (WithTop ℕ) 0) (Target (WithTop ℕ)) :=
    Module.Free.instFaithfulSMulOfNontrivial _ _
  have hi : Function.Injective (rncMap (WithTop ℕ) 0) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (FaithfulSMul.algebraMap_injective (Source (WithTop ℕ) 0) (Target (WithTop ℕ)))
  rcases (rncMap_injective_iff (WithTop ℕ) 0).mp hi with hn | hR
  · exact (by decide : (0 : ℕ) ≠ 1) hn
  · exact withTop_nat_non_cancellation.2 (@Subsingleton.elim (WithTop ℕ) hR 0 1)

private theorem withTop_nat_one_free :
    @Module.Free (Source (WithTop ℕ) 1) (Target (WithTop ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (WithTop ℕ) 1) (Target (WithTop ℕ))
        inferInstance inferInstance (rncMap (WithTop ℕ) 1).toAlgebra) := by
  rw [degree_one_module_eq_self]
  exact Module.Free.self _

private theorem withTop_nat_two_not_free :
    ¬ @Module.Free (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (WithTop ℕ) 2) (Target (WithTop ℕ))
        inferInstance inferInstance (rncMap (WithTop ℕ) 2).toAlgebra) := by
  let : Algebra (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) :=
    (rncMap (WithTop ℕ) 2).toAlgebra
  let : Module (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) :=
    @Algebra.toModule (Source (WithTop ℕ) 2) (Target (WithTop ℕ))
      inferInstance inferInstance (rncMap (WithTop ℕ) 2).toAlgebra
  intro h
  let : Module.Free (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) := h
  let : Nontrivial (Target (WithTop ℕ)) :=
    MvPolynomial.nontrivial_of_nontrivial (Fin 2) (WithTop ℕ)
  let : FaithfulSMul (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) :=
    Module.Free.instFaithfulSMulOfNontrivial _ _
  have hi : Function.Injective (rncMap (WithTop ℕ) 2) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (FaithfulSMul.algebraMap_injective (Source (WithTop ℕ) 2) (Target (WithTop ℕ)))
  rcases (rncMap_injective_iff (WithTop ℕ) 2).mp hi with hn | hR
  · exact (by decide : (2 : ℕ) ≠ 1) hn
  · exact withTop_nat_non_cancellation.2 (@Subsingleton.elim (WithTop ℕ) hR 0 1)

end ToricIdeals.RationalNormalCurve.FreenessModels
