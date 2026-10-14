/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import ToricIdeals.RationalNormalCurve

/-!
# Dimensions of the degree-zero and degree-one Hankel quotients

Over a Noetherian commutative coefficient ring `R`, the full Hankel quotients
in degrees zero and one have Krull dimensions `ringKrullDim R + 1` and
`ringKrullDim R + 2`, respectively. In these degrees there are no Hankel
minors, so the quotients are polynomial rings in one and two variables.
In particular, the degree-zero quotient retains its sole variable; it is
not the image of the monomial parametrization.

The dimensions take values in `WithBot ℕ∞`. No nontriviality or finite-dimension
hypothesis is imposed on `R`, so the formulas also include zero rings and
coefficient rings of infinite Krull dimension.

## References

* `ToricIdeals.RationalNormalCurve` for the vanishing Hankel ideals.
* `Mathlib.RingTheory.KrullDimension.Polynomial` for the dimension formula
  for finite-variable polynomial rings over Noetherian coefficient rings.
-/

namespace ToricIdeals.RationalNormalCurve

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The full degree-zero Hankel quotient has one polynomial variable over `R`. -/
theorem ringKrullDim_quotient_hankelIdeal_zero :
    ringKrullDim (Source R 0 ⧸ hankelIdeal R 0) = ringKrullDim R + 1 := by
  rw [hankelIdeal_zero, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Source R 0))]
  simp [Source]

/-- The full degree-one Hankel quotient has two polynomial variables over `R`. -/
theorem ringKrullDim_quotient_hankelIdeal_one :
    ringKrullDim (Source R 1 ⧸ hankelIdeal R 1) = ringKrullDim R + 2 := by
  rw [hankelIdeal_one, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Source R 1))]
  simp [Source]

end

end ToricIdeals.RationalNormalCurve
