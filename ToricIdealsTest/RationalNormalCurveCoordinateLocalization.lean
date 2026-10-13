/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ToricIdeals.RationalNormalCurve.CoordinateRegularity

/-!
# Injective coordinate localization of Hankel quotients

For every coordinate class in `Source R n ⧸ hankelIdeal R n`, the canonical
`algebraMap` from this quotient to its `Localization.Away` is injective.
Inverting a coordinate therefore does not identify distinct quotient elements.
The proof uses coordinate regularity and Mathlib's characterization of
injective localization maps by regularity of their denominators: every
power of a regular coordinate class is regular.

The coefficient ring is any commutative ring, including the zero ring, and
all degrees and coordinates are covered. No domain, reducedness,
Noetherianity, nontriviality or positive-degree hypothesis is needed.
At degree zero the source is the quotient by the bottom Hankel ideal,
not the image of the monomial parametrization.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.CoordinateRegularity`,
  for regular coordinate classes in the Hankel quotient.
* Mathlib contributors, `Mathlib.RingTheory.Localization.Defs`,
  `Mathlib.RingTheory.Localization.Away.Basic`, `Mathlib.Algebra.Regular.Basic`
  and `Mathlib.Algebra.Group.Submonoid.Membership`, for the canonical
  localization, its injectivity criterion and regularity of powers.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- The canonical map from the Hankel quotient to its localization away from
any coordinate class is injective over every commutative coefficient ring
and in every degree, including degree zero. -/
theorem injective_algebraMap_away_quotient_X (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    Function.Injective
      (algebraMap (Source R n ⧸ hankelIdeal R n)
        (Localization.Away
          (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n)))) := by
  let x := Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n)
  apply (IsLocalization.injective_iff_isRegular
    (M := Submonoid.powers x) (S := Localization.Away x)).mpr
  intro s
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ x).mp s.property
  rw [← hk]
  exact _root_.IsRegular.pow k (isRegular_quotient_X R n i)

#print axioms ToricIdeals.RationalNormalCurve.injective_algebraMap_away_quotient_X

end ToricIdeals.RationalNormalCurve
