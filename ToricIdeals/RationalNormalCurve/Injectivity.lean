/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Defs
public import ToricIdeals.RationalNormalCurve

/-!
# Injectivity of the rational-normal-curve parametrization

The monomial parametrization `rncMap R n` sends `xᵢ` to `a^(n-i) b^i`.
On the full polynomial source `Source R n`, it is injective exactly when
`n = 1` or the coefficient semiring `R` is subsingleton.

At degree one the two source variables map to the two target variables.
Over a subsingleton coefficient semiring the polynomial source is also subsingleton,
so injectivity holds for every degree. Over a nontrivial coefficient semiring,
degree zero sends the sole variable to `1`, and degrees at least two identify
distinct quadratic monomials in the source.

This characterization concerns the map on the full polynomial source, not a
map from a quotient or the parametrization image, nor a restriction to endpoint variables.
It holds in every universe and for every natural-number degree over arbitrary
commutative semirings, including nonreduced rings and product rings. It requires no
nontriviality, domain, field, reducedness, or positive-degree hypothesis.

## References

- The earlier rational-normal-curve formalization in
  `ToricIdeals.RationalNormalCurve`, for the monomial parametrization, its
  degree-zero behavior, degree-one injectivity, and the equal-exponent and
  decreasing-energy arguments for a pair of Hankel columns.
- Mathlib's multivariate polynomial and additive monoid algebra formalizations,
  on which the polynomial semirings, coefficient identities, monomial separation,
  and subsingleton instances are based.

The classification strengthens the commutative-ring setting of the Hankel
presentation to commutative semirings. It is an elementary consequence of the
monomial parametrization and polynomial coefficient identities.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u

private theorem rncMap_zero_not_injective (R : Type u) [CommSemiring R] [Nontrivial R] :
    ¬ Function.Injective (rncMap R 0) := by
  intro hinj
  have hpoly : (MvPolynomial.X (0 : Fin 1) : Source R 0) = MvPolynomial.C 1 :=
    hinj (by simp [coordinateExponent])
  have hs : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
  have hcoeff := congrArg
    (fun f : Source R 0 ↦ f.coeff (Finsupp.single (0 : Fin 1) 1)) hpoly
  rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_of_ne_zero hs] at hcoeff
  exact one_ne_zero hcoeff

private theorem rncMap_not_injective_of_two_le (R : Type u) [CommSemiring R]
    [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) : ¬ Function.Injective (rncMap R n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let p : MinorIndex n := ⟨(a, b), by
    change 0 < 1
    decide⟩
  intro hinj
  -- Coefficient one separates the source monomials in every characteristic.
  have hpoly : (MvPolynomial.monomial (outerExponent n p) 1 : Source R n) =
      MvPolynomial.monomial (innerExponent n p) 1 :=
    hinj (by rw [rncMap_monomial, rncMap_monomial, rncExponent_outer_eq_inner])
  have hexponent : outerExponent n p = innerExponent n p :=
    MvPolynomial.monomial_left_injective (one_ne_zero : (1 : R) ≠ 0) hpoly
  have henergy := inner_energy_lt_outer_energy n p
  rw [hexponent] at henergy
  exact (Nat.lt_irrefl _) henergy

/-- The rational-normal-curve parametrization on the full polynomial source is
injective exactly in degree one or over a subsingleton coefficient semiring.
The equivalence holds for every natural-number degree over any commutative semiring,
including zero semirings, nonreduced rings, and product rings. -/
theorem rncMap_injective_iff (R : Type u) [CommSemiring R] (n : ℕ) :
    Function.Injective (rncMap R n) ↔ n = 1 ∨ Subsingleton R := by
  constructor
  · intro hinj
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let : Nontrivial R := hR
      left
      by_contra hn
      by_cases hzero : n = 0
      · subst n
        exact rncMap_zero_not_injective R hinj
      · exact rncMap_not_injective_of_two_le R n (by omega) hinj
  · rintro (rfl | hR)
    · exact rncMap_one_injective R
    · let : Subsingleton R := hR
      exact Function.injective_of_subsingleton (rncMap R n)

end ToricIdeals.RationalNormalCurve
