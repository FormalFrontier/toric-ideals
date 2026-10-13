/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.SplitQuadric.Basic
public import ToricIdeals.SplitQuadric.Exponents
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Span

/-!
# Monomial normalization for the split quadric

Replacing all possible factors `wz` by `xy` changes a monomial by an element
of the determinant relation ideal. Its coefficient is arbitrary; no
cancellation or nonvanishing assumption on the coefficient ring is needed.

## References

* Formal Frontier Agents: the remainder-monomial factorization in the
  normal-form proof of the determinant kernel.
* Mathlib supplies monomial multiplication and powers, divisibility of a
  difference of powers, and membership in a principal ideal.
-/

@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

open ToricIdeals.SplitQuadric

variable {A : Type u} [CommRing A]

/-- Every coefficient monomial is congruent to its reduced representative
modulo the determinant relation, over any commutative ring. -/
theorem monomial_sub_normal_mem_relationIdeal (m : Fin 4 →₀ ℕ) (r : A) :
    MvPolynomial.monomial m r -
        MvPolynomial.monomial
          (normal (exponentMap m)) r ∈
      relationIdeal A := by
  let k := min (m 0) (m 3)
  let e : Fin 4 →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm ![m 0 - k, m 1, m 2, m 3 - k]
  have hk₀ := Nat.min_le_left (m 0) (m 3)
  have hk₃ := Nat.min_le_right (m 0) (m 3)
  have hm : e + (Finsupp.single 0 k + Finsupp.single 3 k) = m := by
    ext i
    fin_cases i
    · change (e + (Finsupp.single 0 k + Finsupp.single 3 k) : Fin 4 →₀ ℕ) (0 : Fin 4) = m 0
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 0 k + Finsupp.single 3 k) : Fin 4 →₀ ℕ) (1 : Fin 4) = m 1
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 0 k + Finsupp.single 3 k) : Fin 4 →₀ ℕ) (2 : Fin 4) = m 2
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 0 k + Finsupp.single 3 k) : Fin 4 →₀ ℕ) (3 : Fin 4) = m 3
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
  have hreduce : e + (Finsupp.single 1 k + Finsupp.single 2 k) =
      reduce m := by
    ext i
    fin_cases i
    · change (e + (Finsupp.single 1 k + Finsupp.single 2 k) : Fin 4 →₀ ℕ) (0 : Fin 4) =
        reduce m 0
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 1 k + Finsupp.single 2 k) : Fin 4 →₀ ℕ) (1 : Fin 4) =
        reduce m 1
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 1 k + Finsupp.single 2 k) : Fin 4 →₀ ℕ) (2 : Fin 4) =
        reduce m 2
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
    · change (e + (Finsupp.single 1 k + Finsupp.single 2 k) : Fin 4 →₀ ℕ) (3 : Fin 4) =
        reduce m 3
      simp [e, k, Finsupp.coe_equivFunOnFinite_symm]
  -- The coefficient stays in the remainder monomial throughout the factorization.
  have hfactor :
      MvPolynomial.monomial m r - MvPolynomial.monomial (reduce m) r =
        MvPolynomial.monomial e r *
          ((MvPolynomial.X 0 * MvPolynomial.X 3 : Polynomial A) ^ k -
            (MvPolynomial.X 1 * MvPolynomial.X 2 : Polynomial A) ^ k) := by
    rw [mul_sub]
    simp only [mul_pow, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, mul_one, hm, hreduce]
  have hd : relation A ∣
      (MvPolynomial.X 0 * MvPolynomial.X 3 : Polynomial A) ^ k -
        (MvPolynomial.X 1 * MvPolynomial.X 2 : Polynomial A) ^ k :=
    sub_dvd_pow_sub_pow _ _ k
  rw [relationIdeal, Ideal.mem_span_singleton,
    normal_exponentMap, hfactor]
  rcases hd with ⟨q, hq⟩
  refine ⟨MvPolynomial.monomial e r * q, ?_⟩
  rw [hq]
  exact mul_left_comm _ _ _

end SplitQuadric
