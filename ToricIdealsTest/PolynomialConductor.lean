/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.Conductor

/-!
# The two-generator conductor over the natural numbers

The subalgebra `ℕ[X², X³]` is proper, but contains the nonzero ambient ideal `(X²)`.
-/

@[expose] public section

namespace Polynomial

/-- The greatest-ideal theorem has a proper subalgebra and a nonzero ideal in the
case of exponents two and three over the natural numbers. -/
theorem cusp_conductor_nontrivial :
    IsGreatest
      {I : Ideal ℕ[X] | (I : Set ℕ[X]) ⊆
        (Algebra.adjoin ℕ ({X ^ 2, X ^ 3} : Set ℕ[X]) : Set ℕ[X])}
      (Ideal.span ({X ^ 2} : Set ℕ[X])) ∧
      (X ^ 2 : ℕ[X]) ≠ 0 ∧
      (X : ℕ[X]) ∉ Algebra.adjoin ℕ ({X ^ 2, X ^ 3} : Set ℕ[X]) := by
  constructor
  · simpa using (isGreatest_ideal_le_adjoin_X_pow_pair (R := ℕ)
      (by decide : Nat.Coprime 2 3))
  constructor
  · intro hzero
    have hc := congrArg (fun p : ℕ[X] => p.coeff 2) hzero
    simp at hc
  · intro hX
    have hmem := (mem_adjoin_X_pow_pair_iff (a := 2) (b := 3) (X : ℕ[X])).mp hX 1
      (by simp)
    obtain ⟨m, n, heq⟩ := (AddSubmonoid.mem_closure_pair 2 3 1).mp hmem
    simp only [Nat.nsmul_eq_mul] at heq
    omega

end Polynomial
