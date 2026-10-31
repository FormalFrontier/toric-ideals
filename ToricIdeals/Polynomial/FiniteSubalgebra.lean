/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Polynomial rings finite over subalgebras containing a power

If an `R`-subalgebra `A` of `R[X]` contains `X ^ n` for a positive natural number `n`,
then `1, X, ..., X ^ (n - 1)` span `R[X]` as an `A`-module. Consequently `R[X]` is
finite as an `A`-module. The scalar action is multiplication by elements of `A`.

The argument uses division of natural exponents and works over commutative semirings;
it asserts neither linear independence nor freeness.
-/

@[expose] public section

universe u

namespace Polynomial

variable {R : Type u} [CommSemiring R]

/-- If a subalgebra contains a positive power of `X`, the lower powers span the
polynomial ring over that subalgebra. -/
theorem span_X_pow_eq_top_of_X_pow_mem (A : Subalgebra R R[X]) {n : ℕ}
    (hn : 0 < n) (hXn : (X : R[X]) ^ n ∈ A) :
    Submodule.span A (Set.range fun i : Fin n => (X : R[X]) ^ (i : ℕ)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial k c =>
      have hC : C c ∈ A := A.algebraMap_mem c
      let a : A := ⟨C c * (X ^ n) ^ (k / n), A.mul_mem hC (A.pow_mem hXn _)⟩
      have hr : (X : R[X]) ^ (k % n) ∈
          Submodule.span A (Set.range fun i : Fin n => (X : R[X]) ^ (i : ℕ)) :=
        Submodule.subset_span ⟨⟨k % n, Nat.mod_lt k hn⟩, rfl⟩
      have hm : monomial k c = a • (X : R[X]) ^ (k % n) := by
        change monomial k c = (C c * ((X : R[X]) ^ n) ^ (k / n)) * X ^ (k % n)
        rw [← pow_mul, mul_assoc, ← pow_add, Nat.div_add_mod, C_mul_X_pow_eq_monomial]
      rw [hm]
      exact Submodule.smul_mem _ a hr

/-- A polynomial ring is a finite module over any subalgebra containing a positive
power of `X`. -/
theorem moduleFinite_of_X_pow_mem (A : Subalgebra R R[X]) {n : ℕ}
    (hn : 0 < n) (hXn : (X : R[X]) ^ n ∈ A) : Module.Finite A R[X] := by
  apply Module.finite_def.mpr
  rw [← span_X_pow_eq_top_of_X_pow_mem A hn hXn]
  exact Submodule.fg_span (Set.finite_range _)

end Polynomial
