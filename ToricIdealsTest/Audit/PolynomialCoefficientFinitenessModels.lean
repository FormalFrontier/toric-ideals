/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial coefficient-module finiteness boundaries

The integer polynomial ring is not finite over its coefficient ring. The same
obstruction holds over `ZMod 4`, which has a nonzero square-zero element, whereas
polynomials over the zero ring `ZMod 1` form a finite coefficient module.

Changing the scalar ring changes the finiteness question: the integer polynomial
ring is finite as its canonical module over itself. This uses self-module
finiteness without a Noetherian coefficient-ring hypothesis.

## References

* Mathlib contributors, `Mathlib.RingTheory.Polynomial.Basic`, for
  `Polynomial.not_finite` over every nontrivial semiring.
* Mathlib contributors, `Mathlib.RingTheory.Finiteness.Basic` and
  `Mathlib.Algebra.Module.Defs`, for self-module finiteness and finiteness of
  modules with subsingleton carriers.
-/

namespace Polynomial.CoefficientFinitenessModels

/-- Integer polynomials are not finite for the integer coefficient action. -/
private theorem integer_polynomials_not_finite :
    ¬ Module.Finite ℤ (Polynomial ℤ) :=
  Polynomial.not_finite

/-- A nonzero square-zero coefficient does not remove the polynomial obstruction. -/
private theorem mod_four_polynomials_not_finite :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      ¬ Module.Finite (ZMod 4) (Polynomial (ZMod 4)) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  exact ⟨by decide, by decide, Polynomial.not_finite⟩

/-- Polynomials over the zero coefficient ring form a finite coefficient module. -/
private theorem zero_coefficients_polynomials_finite :
    Module.Finite (ZMod 1) (Polynomial (ZMod 1)) := by
  let : Subsingleton (Polynomial (ZMod 1)) :=
    Module.subsingleton (ZMod 1) (Polynomial (ZMod 1))
  let : Finite (Polynomial (ZMod 1)) := inferInstance
  exact Module.Finite.of_finite

/-- The same integer polynomial carrier is finite when its scalars are itself. -/
private theorem integer_polynomial_self_module_finite :
    Module.Finite (Polynomial ℤ) (Polynomial ℤ) :=
  Module.Finite.self (Polynomial ℤ)

end Polynomial.CoefficientFinitenessModels
