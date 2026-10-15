/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals

/-!
# Clients for flatness of the Hankel quotient parametrization

Coefficient flatness of the full Hankel quotient does not imply flatness
of its map to the full bivariate polynomial target. These clients contrast
the two scalar actions over arbitrary nontrivial commutative rings and
record their common positive behavior over zero coefficient rings.
Independent boundary controls live in `QuotientMapFlatnessModels`.
-/

@[expose] public section

namespace ToricIdealsTest.QuotientMapFlatness

open ToricIdeals.RationalNormalCurve

universe u

/-- In degree at least two, the quotient is flat over its coefficient ring,
but the full target is not flat over the quotient through its parametrization. -/
theorem coefficient_flat_and_quotientMap_not_flat
    (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) :
    Module.Flat R (Source R n ⧸ hankelIdeal R n) ∧
      ¬ (quotientMap R n).toRingHom.Flat := by
  refine ⟨quotient_flat R n, ?_⟩
  intro hflat
  rcases (quotientMap_flat_iff R n).mp hflat with hdegree | hzero
  · subst n
    exact (Nat.not_succ_le_self 1) hn
  · exact (zero_ne_one : (0 : R) ≠ 1) (@Subsingleton.elim R hzero (0 : R) 1)

/-- Zero coefficients give both coefficient flatness of the quotient and
flatness of its map to the full target, including in degree zero. -/
theorem zero_ring_flat_for_both_actions
    (R : Type u) [CommRing R] [Subsingleton R] (n : ℕ) :
    Module.Flat R (Source R n ⧸ hankelIdeal R n) ∧
      (quotientMap R n).toRingHom.Flat :=
  ⟨quotient_flat R n, (quotientMap_flat_iff R n).mpr (Or.inr inferInstance)⟩

end ToricIdealsTest.QuotientMapFlatness
