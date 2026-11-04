/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.MonomialFinite
public import ToricIdeals.Submonoid.FiniteCover

/-!
# Finite extensions of monomial subalgebras

The finite left translate cover criterion for inclusions of monomial subalgebras
is re-exported from `GroupRings.MonoidAlgebra.MonomialFinite`. For submonoids
`S ≤ T` of a monoid, a finite cover `T ⊆ S * E` with `E ⊆ T` makes the
`T`-monomial subalgebra a finite module over the `S`-monomial subalgebra.
Over a nontrivial coefficient semiring, the converse holds. The module structure
is the left action induced by inclusion of the subalgebras. Neither commutativity
nor cancellation of the exponent monoid is needed for this criterion.

For a cancellative commutative exponent monoid, this module further shows that
module finiteness implies either the coefficient semiring is subsingleton or one
positive exponent sends every element of `T` into `S`. This consequence uses
`ToricIdeals.Submonoid.FiniteCover` and the same inclusion-induced left action.

## References

* The finite-cover criterion in `GroupRings.MonoidAlgebra.MonomialFinite`,
  by Formal Frontier Agents.
* The cancellative power bound in `ToricIdeals.Submonoid.FiniteCover`,
  by Formal Frontier Agents.
* Mathlib's finite-generation API, by Johan Commelin.
* Mathlib's monoid-algebra module and support API, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison.
-/

@[expose] public section

namespace MonoidAlgebra

universe u v

/-- Finiteness of the left inclusion module between coefficient-one monomial
adjoins implies that either the coefficient semiring is subsingleton or one
positive exponent sends every target exponent into the source submonoid. -/
theorem subsingleton_or_exists_forall_pow_mem_of_moduleFinite_monomialSubalgebra
    {R : Type u} {M : Type v} [CommSemiring R] [CancelCommMonoid M]
    {S T : Submonoid M} (hST : S ≤ T)
    (hfinite : @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : M) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : M) (1 : R))) _ _
      (Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) :
    Subsingleton R ∨ ∃ n : ℕ, 0 < n ∧ ∀ t ∈ T, t ^ n ∈ S := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Or.inl hR
  · let : Nontrivial R := hR
    obtain ⟨E, hE, hET, hcover⟩ :=
      exists_finite_cover_of_moduleFinite_monomialSubalgebra hST hfinite
    refine Or.inr ⟨E.ncard.factorial, Nat.factorial_pos _, ?_⟩
    intro t ht
    exact Submonoid.pow_factorial_mem_of_finite_cover hE hET hcover ht

end MonoidAlgebra
