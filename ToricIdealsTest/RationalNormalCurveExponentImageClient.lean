/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
public import ToricIdeals.RationalNormalCurve.ExponentImage

/-!
# Selecting normal exponents from target arithmetic

For positive degree, divisibility of a target's total exponent ensures that the
existing `fiberNormalExponent` selects a terminal source exponent mapping back
to that target. No source preimage is supplied: the arithmetic image criterion
provides one, and the existing selection laws identify its normal representative.

The selector is specialized to `ℤ` only because its existing API carries a
commutative coefficient-ring parameter. No coefficient computation or domain
hypothesis enters these exponent statements. Positive degree is needed by the
existing selection law; the image criterion itself includes degree zero.

The mixed cubic family `(4m+2, 2m+1)` has total `6m+3`, so every member has a
selected normal preimage. In particular, the family includes the interior target
`(2,1)` and is not restricted to coordinatewise multiples of three.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and its
  `ExponentImage` module, for terminal-exponent selection and the arithmetic
  image criterion.
* Mathlib contributors, for `AddMonoidHom.mem_mrange`, `Finsupp.single` and
  natural-number arithmetic.
-/

namespace ToricIdeals.RationalNormalCurve.ExponentImageClient

@[expose] public noncomputable section

/-- For positive degree and a target whose total is divisible by that degree,
the existing fiber selector over `ℤ` is terminal and maps back to the target.
The coefficient-ring parameter is inherited from the selector's API; no source
preimage is required as input. -/
theorem fiberNormalExponent_normal_and_image_of_dvd (n : ℕ) (hn : 1 ≤ n)
    (t : Fin 2 →₀ ℕ) (hdiv : n ∣ (t 0 + t 1)) :
    Normal n (fiberNormalExponent ℤ n t) ∧
      rncExponent n (fiberNormalExponent ℤ n t) = t := by
  obtain ⟨d, hd⟩ := AddMonoidHom.mem_mrange.mp
    ((mem_mrange_rncExponent_iff n t).mpr hdiv)
  rw [← hd, fiberNormalExponent_image ℤ n hn d]
  exact ⟨normalSourceExponent_normal ℤ n d, normalSourceExponent_rncExponent ℤ n d⟩

private theorem cubic_mixed_family_normal_and_image (m : ℕ) :
    Normal 3 (fiberNormalExponent ℤ 3
      (Finsupp.single (0 : Fin 2) (4 * m + 2) +
        Finsupp.single (1 : Fin 2) (2 * m + 1))) ∧
      rncExponent 3 (fiberNormalExponent ℤ 3
        (Finsupp.single (0 : Fin 2) (4 * m + 2) +
          Finsupp.single (1 : Fin 2) (2 * m + 1))) =
        Finsupp.single (0 : Fin 2) (4 * m + 2) +
          Finsupp.single (1 : Fin 2) (2 * m + 1) := by
  apply fiberNormalExponent_normal_and_image_of_dvd 3 (by decide)
  refine ⟨2 * m + 1, ?_⟩
  simp
  ring


end

end ToricIdeals.RationalNormalCurve.ExponentImageClient
