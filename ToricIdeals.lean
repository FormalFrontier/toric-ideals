/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.FiberNormalization
public import ToricIdeals.RationalNormalCurve
public import ToricIdeals.RationalNormalCurve.Artinian
public import ToricIdeals.RationalNormalCurve.Augmentation
public import ToricIdeals.RationalNormalCurve.AxisProjection
public import ToricIdeals.RationalNormalCurve.BaseChange
public import ToricIdeals.RationalNormalCurve.CoefficientAlgebra
public import ToricIdeals.RationalNormalCurve.CoefficientFiniteness
public import ToricIdeals.RationalNormalCurve.CoordinateRegularity
public import ToricIdeals.RationalNormalCurve.Dimension
public import ToricIdeals.RationalNormalCurve.EndpointMap
public import ToricIdeals.RationalNormalCurve.ExponentImage
public import ToricIdeals.RationalNormalCurve.Freeness
public import ToricIdeals.RationalNormalCurve.Homogeneous
public import ToricIdeals.RationalNormalCurve.HomogeneousBasis
public import ToricIdeals.RationalNormalCurve.Injectivity
public import ToricIdeals.RationalNormalCurve.Jacobson
public import ToricIdeals.RationalNormalCurve.MapFlatness
public import ToricIdeals.RationalNormalCurve.MapSurjectivity
public import ToricIdeals.RationalNormalCurve.Noetherian
public import ToricIdeals.RationalNormalCurve.ParametrizationFinite
public import ToricIdeals.SplitQuadric.Exponents
public import ToricIdeals.SplitQuadric

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

`ToricIdeals.RationalNormalCurve.MapSurjectivity` provides
`rncMap_surjective_iff`: over every commutative semiring and in every degree,
the raw map reaches the full bivariate polynomial target exactly when the
degree is one or the coefficients are subsingleton. This is not a statement
about the Hankel quotient or a map onto the parametrization image.

`ToricIdeals.RationalNormalCurve.Freeness` provides `rncMap_moduleFree_iff`:
over every commutative semiring and in every degree, the full bivariate target
is free over the full source through the raw map exactly when the degree is one
or the coefficients are subsingleton. Its explicit module argument fixes the
action `p • q = rncMap R n p * q`. This is arbitrary-basis freeness, not finite
rank or coefficient-module freeness of the target or Hankel quotient.

`ToricIdeals.RationalNormalCurve.MapFlatness` provides `rncMap_flat_iff`:
over every commutative ring and in every degree, the full bivariate target is
flat over the full source through the raw map exactly when the degree is one
or the coefficients are subsingleton. Its source action is induced by
`rncMap`, not the coefficient action on the target or Hankel quotient.

`ToricIdeals.RationalNormalCurve.CoefficientAlgebra` provides
`quotient_free`, `quotient_flat` and `quotient_faithfullyFlat`: for every
`(R : Type u) [CommRing R]` and `n : ℕ`, the full Hankel quotient
`Source R n ⧸ hankelIdeal R n` is free, flat and faithfully flat for its
canonical coefficient `R`-action. Zero rings and degree zero are included,
with the full one-variable polynomial quotient in degree zero. Faithful
flatness permits direct use of Mathlib's tensor injectivity reflection and
canonical tensor-unit injection for arbitrary coefficient modules, without
a flatness hypothesis or quotient action on those modules. This coefficient
action is distinct from the raw-source actions classified above.

`ToricIdeals.RationalNormalCurve.HomogeneousBasis` provides
`quotientHomogeneousBasis`: the degree-`d` submodule of the full Hankel
quotient has an explicit coefficient basis indexed by `Fin (n * d + 1)`
over every commutative ring, including zero rings and `n = 0`.
`quotientHomogeneousCoordinates` gives finite coordinates and reconstruction.
For positive `n` these are target coefficients of degree `n*d`; for `n = 0`
the basis is the class of `X 0 ^ d` in the full polynomial quotient.
No field hypothesis or claim of distinct vectors over a zero ring is needed.

`ToricIdeals.RationalNormalCurve.CoefficientFiniteness` provides
`quotient_moduleFinite_iff`: in every degree over every commutative ring `R`,
the full Hankel quotient is finite for its canonical coefficient `R`-action
exactly when `R` is a zero ring. This is distinct from finiteness over the
polynomial algebra of endpoint coordinates or over the quotient itself.

`ToricIdeals.SplitQuadric.Exponents` gives the natural-number exponent map of
`(w, x, y, z) ↦ (W, WT, Y, YT)`, its image cone `t ≤ u + v`, and a unique
reduced representative in each fiber over that cone. It also supplies reduction
and the total selector, with its right-inverse law restricted to the image cone.

`ToricIdeals.SplitQuadric` re-exports the coordinate algebra of `wz - xy = 0`
for every commutative coefficient ring. Its `SplitQuadric` namespace provides
the kernel equality, injective quotient parametrization, equivalence with the
range, domain and primality criteria, coefficient retraction, and the comparison
of independently chosen localization models of the `w`- and `W`-charts.
-/
