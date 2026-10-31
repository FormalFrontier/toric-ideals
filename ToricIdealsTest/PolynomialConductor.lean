/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.Polynomial.Conductor
public import ToricIdeals.Polynomial.FiniteSubalgebra

/-!
# The two-generator conductor over the natural numbers

The subalgebra `ℕ[X², X³]` is proper, but contains the nonzero ambient ideal `(X²)`.
In contrast, `ℕ[X², X⁴]` contains `X²` but no nonzero ambient ideal: the ideal
`(X²)` also contains `X³`, which is absent from this subalgebra. Nevertheless, the
ambient polynomial ring is finite over the even-power subalgebra.
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

/-- The even-power subalgebra is nonzero and proper, but its greatest contained
ambient ideal is zero; in particular, the ambient ideal `(X²)` is not contained. -/
theorem even_power_conductor_nontrivial :
    IsGreatest
      {I : Ideal ℕ[X] | (I : Set ℕ[X]) ⊆
        (Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) : Set ℕ[X])}
      (⊥ : Ideal ℕ[X]) ∧
      (X ^ 2 : ℕ[X]) ∈ Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) ∧
      (X ^ 2 : ℕ[X]) ≠ 0 ∧
      (X : ℕ[X]) ∉ Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) ∧
      (X ^ 3 : ℕ[X]) ∉ Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) ∧
      ¬ (Ideal.span ({X ^ 2} : Set ℕ[X]) : Set ℕ[X]) ⊆
        (Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) : Set ℕ[X]) := by
  have hodd (n : ℕ) (hn : n % 2 = 1) :
      (X ^ n : ℕ[X]) ∉ Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X]) := by
    intro hmem
    have hn' := (mem_adjoin_X_pow_pair_iff (a := 2) (b := 4) (X ^ n : ℕ[X])).mp
      hmem n (by simp)
    obtain ⟨i, j, hij⟩ := (AddSubmonoid.mem_closure_pair 2 4 n).mp hn'
    simp only [Nat.nsmul_eq_mul] at hij
    omega
  refine ⟨isGreatest_ideal_le_adjoin_X_pow_pair_of_not_coprime (by decide),
    Algebra.subset_adjoin (by simp), ?_, ?_, hodd 3 rfl, ?_⟩
  · intro hzero
    have hc := congrArg (fun p : ℕ[X] => p.coeff 2) hzero
    simp at hc
  · simpa only [pow_one] using hodd 1 rfl
  · intro hI
    apply hodd 3 rfl
    apply hI
    have hX2 : (X ^ 2 : ℕ[X]) ∈ Ideal.span ({X ^ 2} : Set ℕ[X]) :=
      Ideal.subset_span (by simp)
    simpa only [SetLike.mem_coe, ← pow_succ] using
      (Ideal.span ({X ^ 2} : Set ℕ[X])).mul_mem_right X hX2

-- Finiteness of the ambient module is compatible with a zero conductor.
example : Module.Finite (Algebra.adjoin ℕ ({X ^ 2, X ^ 4} : Set ℕ[X])) ℕ[X] :=
  moduleFinite_of_X_pow_mem _ (by decide : 0 < 2) even_power_conductor_nontrivial.2.1

end Polynomial
