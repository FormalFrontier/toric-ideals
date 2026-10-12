/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.FiberNormalization
public import ToricIdeals.RationalNormalCurve
public import ToricIdeals.RationalNormalCurve.Noetherian
public import ToricIdeals.SplitQuadric.Exponents

/-!
# Toric ideals

Root import for reusable Lean theory of monomial maps, toric ideals, and
rational normal curves. Import the leaves directly when only one part is needed:
`ToricIdeals.MonoidAlgebra.FiberNormalization` supplies the independent-universe
coefficientwise kernel principle, while `ToricIdeals.RationalNormalCurve`
supplies the Hankel-minor kernel calculation for positive degree, its small-degree
boundaries, a quotient-to-image equivalence, and domain-dependent consequences.
For every `(R : Type u) [CommRing R]` and every `n : ℕ`,
`quotient_isReduced_iff` says that the quotient by the Hankel minors is reduced
exactly when `R` is reduced; `hankelIdeal_isRadical_iff` characterizes ideal
radicality by the same condition. Neither characterization needs a nontriviality,
domain, field, cancellation or positive-degree assumption.
At degree zero they concern the one-variable polynomial quotient by `⊥`, not
the parametrization kernel or image. They include zero rings and reduced
coefficient rings with zero divisors; radicality asserts neither properness nor
primality.

`ToricIdeals.SplitQuadric.Exponents` gives the natural-number exponent map of
`(w, x, y, z) ↦ (W, WT, Y, YT)`, its image cone `t ≤ u + v`, and a unique
reduced representative in each fiber over that cone. It also supplies reduction
and the total selector, with its right-inverse law restricted to the image cone.
-/
