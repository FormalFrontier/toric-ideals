/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.FiberNormalization
public import ToricIdeals.RationalNormalCurve

/-!
# Toric ideals

Root import for reusable Lean theory of monomial maps, toric ideals, and
rational normal curves. Import the leaves directly when only one part is needed:
`ToricIdeals.MonoidAlgebra.FiberNormalization` supplies the independent-universe
coefficientwise kernel principle, while `ToricIdeals.RationalNormalCurve`
supplies the Hankel-minor kernel calculation for positive degree, its small-degree
boundaries, a quotient-to-image equivalence, and domain-dependent consequences.
-/
