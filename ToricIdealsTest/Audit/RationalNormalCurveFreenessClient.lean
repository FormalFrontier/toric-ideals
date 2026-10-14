/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import ToricIdeals

/-!
# Clients of source-module freeness for rational normal curves

These clients apply the freeness classifier through the root import, with the
raw map's module argument explicit. Natural-number coefficients give freeness
in degree one and obstructions in degree zero and every degree at least two.
The nonreduced ring `ZMod 4` has the same degree-one/degree-two boundary, while
`ZMod 1` gives freeness in every degree. Lifted natural numbers exercise arbitrary
coefficient universes, and `WithTop ℕ` exercises noncancellative addition.

These are consequences of the classifier, separate from the independent
basis, collision and scalar-action models in `RationalNormalCurveFreenessModels`.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Freeness`, for the
  source-module freeness classifier.
* Mathlib contributors, for the coefficient semirings and their instances.
-/

namespace ToricIdeals.RationalNormalCurve.FreenessClient

universe v

private theorem nat_degree_zero_not_free :
    ¬ @Module.Free (Source ℕ 0) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ 0) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 0).toAlgebra) := by
  intro hfree
  rcases (rncMap_moduleFree_iff ℕ 0).mp hfree with hn | hR
  · exact (by decide : (0 : ℕ) ≠ 1) hn
  · exact zero_ne_one (@Subsingleton.elim ℕ hR 0 1)

private theorem nat_degree_one_free :
    @Module.Free (Source ℕ 1) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ 1) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ 1).toAlgebra) :=
  (rncMap_moduleFree_iff ℕ 1).mpr (Or.inl rfl)

private theorem nat_higher_degree_not_free (n : ℕ) :
    ¬ @Module.Free (Source ℕ (n + 2)) (Target ℕ) inferInstance inferInstance
      (@Algebra.toModule (Source ℕ (n + 2)) (Target ℕ) inferInstance inferInstance
        (rncMap ℕ (n + 2)).toAlgebra) := by
  intro hfree
  rcases (rncMap_moduleFree_iff ℕ (n + 2)).mp hfree with hn | hR
  · omega
  · exact zero_ne_one (@Subsingleton.elim ℕ hR 0 1)

private theorem mod_four_degree_one_free :
    @Module.Free (Source (ZMod 4) 1) (Target (ZMod 4)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 4) 1) (Target (ZMod 4)) inferInstance inferInstance
        (rncMap (ZMod 4) 1).toAlgebra) :=
  (rncMap_moduleFree_iff (ZMod 4) 1).mpr (Or.inl rfl)

private theorem mod_four_degree_two_not_free :
    ¬ @Module.Free (Source (ZMod 4) 2) (Target (ZMod 4)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 4) 2) (Target (ZMod 4)) inferInstance inferInstance
        (rncMap (ZMod 4) 2).toAlgebra) := by
  intro hfree
  rcases (rncMap_moduleFree_iff (ZMod 4) 2).mp hfree with hn | hR
  · exact (by decide : (2 : ℕ) ≠ 1) hn
  · exact (by decide : (0 : ZMod 4) ≠ 1) (@Subsingleton.elim (ZMod 4) hR 0 1)

private theorem zero_coefficients_free (n : ℕ) :
    @Module.Free (Source (ZMod 1) n) (Target (ZMod 1)) inferInstance inferInstance
      (@Algebra.toModule (Source (ZMod 1) n) (Target (ZMod 1)) inferInstance inferInstance
        (rncMap (ZMod 1) n).toAlgebra) :=
  (rncMap_moduleFree_iff (ZMod 1) n).mpr (Or.inr inferInstance)

private theorem ulift_nat_degree_one_free :
    @Module.Free (Source (ULift.{v} ℕ) 1) (Target (ULift.{v} ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (ULift.{v} ℕ) 1) (Target (ULift.{v} ℕ))
        inferInstance inferInstance (rncMap (ULift.{v} ℕ) 1).toAlgebra) :=
  (rncMap_moduleFree_iff (ULift.{v} ℕ) 1).mpr (Or.inl rfl)

private theorem withTop_nat_degree_two_not_free :
    ¬ @Module.Free (Source (WithTop ℕ) 2) (Target (WithTop ℕ)) inferInstance inferInstance
      (@Algebra.toModule (Source (WithTop ℕ) 2) (Target (WithTop ℕ))
        inferInstance inferInstance (rncMap (WithTop ℕ) 2).toAlgebra) := by
  intro hfree
  rcases (rncMap_moduleFree_iff (WithTop ℕ) 2).mp hfree with hn | hR
  · exact (by decide : (2 : ℕ) ≠ 1) hn
  · exact zero_ne_one (@Subsingleton.elim (WithTop ℕ) hR 0 1)

end ToricIdeals.RationalNormalCurve.FreenessClient
