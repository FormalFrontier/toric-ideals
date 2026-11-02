/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.AddMonoidAlgebra.MonomialFinite
public import ToricIdeals.AddSubmonoid.NatFiniteRemainder

/-!
# Finite monomial extensions with natural-number exponents

For additive submonoids of the natural numbers, the canonical inclusion of
coefficient-one monomial adjoins is module-finite exactly when the coefficients
are subsingleton, the source exponent submonoid is nonzero, or the target
exponent submonoid is zero. Coefficients need only form a commutative semiring.
-/

@[expose] public section

namespace AddMonoidAlgebra

universe u

variable {R : Type u} [CommSemiring R]

/-- The canonical left module between natural-exponent monomial adjoins is
finite exactly when the coefficients are subsingleton, the source exponent
submonoid is nonzero, or the target exponent submonoid is zero. -/
theorem moduleFinite_adjoin_single_nat_iff
    {S T : AddSubmonoid ℕ} (hST : S ≤ T) :
    @Module.Finite
      (Algebra.adjoin R (Set.range fun s : S => single (s : ℕ) (1 : R)))
      (Algebra.adjoin R (Set.range fun t : T => single (t : ℕ) (1 : R))) _ _
      (Subalgebra.inclusion
        (adjoin_single_mono (R := R) hST)).toRingHom.toModule ↔
      Subsingleton R ∨ S ≠ ⊥ ∨ T = ⊥ := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : Subsingleton R := hR
    have : Subsingleton
        (Algebra.adjoin R (Set.range fun t : T => single (t : ℕ) (1 : R))) :=
      Module.subsingleton R _
    constructor
    · intro _
      exact Or.inl hR
    · intro _
      exact @Module.Finite.of_finite _ _ _ _
        (Subalgebra.inclusion
          (adjoin_single_mono (R := R) hST)).toRingHom.toModule _
  · let : Nontrivial R := hR
    refine (moduleFinite_adjoin_single_iff (R := R) hST).trans
      ((AddSubmonoid.exists_finite_subset_add_submonoid_iff S T).trans ?_)
    constructor
    · exact Or.inr
    · rintro (hR' | h)
      · let : Subsingleton R := hR'
        exact False.elim (zero_ne_one (Subsingleton.elim (0 : R) 1))
      · exact h

end AddMonoidAlgebra
