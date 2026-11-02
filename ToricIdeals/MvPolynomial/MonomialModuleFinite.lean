/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.AddMonoidAlgebra.MonomialFinite
public import ToricIdeals.MvPolynomial.MonomialSubalgebra

/-!
# Module-finite extensions of multivariate monomial adjoins

For additive exponent submonoids `S ≤ T` in `σ →₀ ℕ`, a finite left translate
cover `T ⊆ S + E` makes the inclusion of their monomial adjoins module-finite.
Over nontrivial coefficients this condition is also necessary. The action is
explicitly the one induced by the inclusion of these subalgebras.

These are specializations of the additive monoid-algebra results. The variables
and coefficients have independent universes; there is no finiteness assumption
on the variables or the exponent submonoids. The forward implication includes
the zero coefficient semiring.

## References

* Mathlib's multivariate-polynomial representation as an additive monoid algebra,
  by Johannes Hölzl, Johan Commelin, and Mario Carneiro.
* Mathlib's subalgebra inclusion API, by Kenny Lau and Yury Kudryashov.
-/

@[expose] public section

open scoped Pointwise

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- Inclusion of additive exponent submonoids induces inclusion of their
monomial-generated polynomial subalgebras. -/
theorem adjoin_monomial_mono {S T : AddSubmonoid (σ →₀ ℕ)} (hST : S ≤ T) :
    Algebra.adjoin R
      (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R)) ≤
    Algebra.adjoin R
      (Set.range fun t : T => monomial (t : σ →₀ ℕ) (1 : R)) := by
  exact AddMonoidAlgebra.adjoin_single_mono hST

/-- A finite left additive translate cover of exponents gives a finite module
for the inclusion of the corresponding polynomial monomial adjoins. -/
theorem moduleFinite_adjoin_monomial_of_subset_add
    {S T : AddSubmonoid (σ →₀ ℕ)} (hST : S ≤ T)
    {E : Set (σ →₀ ℕ)} (hE : E.Finite) (hET : E ⊆ (T : Set (σ →₀ ℕ)))
    (hcover : (T : Set (σ →₀ ℕ)) ⊆ (S : Set (σ →₀ ℕ)) + E) :
    @Module.Finite
      (Algebra.adjoin R
        (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R)))
      (Algebra.adjoin R
        (Set.range fun t : T => monomial (t : σ →₀ ℕ) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_monomial_mono (R := R) hST)).toRingHom.toModule := by
  exact AddMonoidAlgebra.moduleFinite_adjoin_single_of_subset_add hST hE hET hcover

/-- For nontrivial coefficients, a module-finite inclusion of polynomial
monomial adjoins gives a finite left additive translate cover of exponents. -/
theorem exists_finite_cover_of_moduleFinite_adjoin_monomial [Nontrivial R]
    {S T : AddSubmonoid (σ →₀ ℕ)} (hST : S ≤ T)
    (hfinite : @Module.Finite
      (Algebra.adjoin R
        (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R)))
      (Algebra.adjoin R
        (Set.range fun t : T => monomial (t : σ →₀ ℕ) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_monomial_mono (R := R) hST)).toRingHom.toModule) :
    ∃ E : Set (σ →₀ ℕ), E.Finite ∧ E ⊆ (T : Set (σ →₀ ℕ)) ∧
      (T : Set (σ →₀ ℕ)) ⊆ (S : Set (σ →₀ ℕ)) + E := by
  exact AddMonoidAlgebra.exists_finite_cover_of_moduleFinite_adjoin_single hST hfinite

/-- The canonical inclusion of multivariate monomial adjoins is module-finite
exactly when the exponents admit a finite left additive translate cover. -/
theorem moduleFinite_adjoin_monomial_iff [Nontrivial R]
    {S T : AddSubmonoid (σ →₀ ℕ)} (hST : S ≤ T) :
    @Module.Finite
      (Algebra.adjoin R
        (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R)))
      (Algebra.adjoin R
        (Set.range fun t : T => monomial (t : σ →₀ ℕ) (1 : R))) _ _
      (Subalgebra.inclusion (adjoin_monomial_mono (R := R) hST)).toRingHom.toModule ↔
    ∃ E : Set (σ →₀ ℕ), E.Finite ∧ E ⊆ (T : Set (σ →₀ ℕ)) ∧
      (T : Set (σ →₀ ℕ)) ⊆ (S : Set (σ →₀ ℕ)) + E := by
  exact AddMonoidAlgebra.moduleFinite_adjoin_single_iff hST

end MvPolynomial
