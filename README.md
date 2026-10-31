# toric-ideals

Authors: Formal Frontier Agents. Original Formal Frontier contributions are
licensed under Apache-2.0; see the complete root `LICENSE` file. The project
uses AI-assisted formalization and review.

Reusable Lean 4 theory of coefficientwise normalization over rings, monomial-map
kernels, the Hankel ideal of the rational normal curve over arbitrary
commutative coefficient rings, and natural-number exponent normal forms for
the split quadric, together with its coordinate algebra and localization charts,
and finiteness of polynomial rings over subalgebras containing a positive power.

## Headline results

Write `Q(R,n) = R[X₀,…,Xₙ]/I(R,n)` for the full quotient by the `2 × 2` Hankel
minors and `f = rncMap R n : Source R n →+* Target R` for `Xᵢ ↦ U^(n-i)V^i`.
Unless stated otherwise, `R` is any commutative ring and `n : ℕ` includes zero.
In particular, `Q(R,0) = R[X₀]`, **not** the raw parametrization image `R`.
Here `Subsingleton R` means the zero coefficient ring or semiring.

- **Two-generator polynomial conductor:** For a commutative semiring `R` and
  coprime natural numbers `a, b`, the greatest ideal of `R[X]` contained in
  the canonical subalgebra `R[X^a, X^b]` is `(X^((a - 1)*(b - 1)))`.
  If `a, b` are not coprime, the greatest contained ambient ideal is zero.
  These statements concern every ambient polynomial ideal, include exponents
  zero and one (also `(a, b) = (0, 0)`), and permit the zero semiring.
  Membership in the subalgebra is also characterized by the additive submonoid
  containing the support. See
  [the conductor theorem](ToricIdeals/Polynomial/Conductor.lean) and its
  [natural-coefficient examples](ToricIdealsTest/PolynomialConductor.lean).
- **Polynomial subalgebras containing a power:** For every commutative semiring
  `R : Type u`, `A : Subalgebra R R[X]`, and positive natural number `n` with
  `X ^ n ∈ A`, `Polynomial.span_X_pow_eq_top_of_X_pow_mem` shows that the first
  `n` powers of `X` span `R[X]` for the canonical multiplication action of `A`.
  `Polynomial.moduleFinite_of_X_pow_mem` consequently gives `Module.Finite A R[X]`.
  No ring, domain, nontriviality or Noetherian hypothesis is needed, and no basis
  or freeness is asserted. See [finite polynomial subalgebras](ToricIdeals/Polynomial/FiniteSubalgebra.lean).
- **Coefficient change on full Hankel quotients:** For commutative rings
  `R : Type u`, `S : Type v` in independent universes and any `φ : R →+* S`, the
  induced stock ideal quotient map `Q(R,n) →+* Q(S,n)` is injective exactly when
  `φ` is injective, and surjective exactly when `φ` is surjective, in every degree.
  No flatness, domain, nontriviality or `Algebra R S` is assumed. See the
  [coefficient-map criteria](ToricIdeals/RationalNormalCurve/CoefficientMap.lean).
- **Coefficientwise normalization and monomial kernels:** Over any ring, an
  additive source monoid and an arbitrary index function to a bare type, suppose
  **every monomial and coefficient** is congruent modulo a left ideal to the term
  at a source exponent chosen by its target index. Elements whose coefficients
  sum to zero along fibers then belong to the ideal, in independent universes.
  Additive exponent homomorphisms give kernel containment; equality and a
  membership criterion additionally need the reverse ideal inclusion. No
  commutativity, section or surjectivity is needed; an arbitrary index function
  need not induce a ring map. See the [normalization contract](docs/FiberNormalization.md).
- **Coprime weighted fibers:** In `AddMonoidAlgebra R (Fin 2 →₀ ℕ)` for any
  ring `R`, `Nat.Coprime a b` and equal weights
  `b*d(0)+a*d(1) = b*e(0)+a*e(1)` imply that
  `single d c - single e c` belongs to the principal **left** ideal generated
  by `X₀^a - X₁^b`, for every `c : R`. Noncommutative coefficient rings, zero
  rings and the coprime axes `(0,1)` and `(1,0)` are included. See
  [`single_sub_single_mem_span_of_coprime_weight_eq`](ToricIdeals/MonoidAlgebra/CoprimeWeights.lean).
  The same module proves
  `ker_mapDomainRingHom_weight_eq_span_of_coprime`: the kernel of the stock
  `Finsupp.weight` pushforward for weights `(b,a)` is exactly this left ideal.
  `mem_span_iff_mapDomain_weight_eq_zero_of_coprime` detects membership by
  vanishing of that image. No full-target surjectivity is asserted: weights
  `(3,2)` miss `1`.
- **Gcd-reduced natural-weight kernels:** For any `R : Type u` with `[Ring R]`
  and `a,b : ℕ` with `a ≠ 0 ∨ b ≠ 0`, the same stock pushforward for weights
  `(b,a)` has kernel generated as a **left** ideal by
  `X₀^(a / Nat.gcd a b) - X₁^(b / Nat.gcd a b)`.
  [`ker_mapDomainRingHom_weight_eq_span`](ToricIdeals/MonoidAlgebra/NaturalWeights.lean)
  and `mem_span_iff_mapDomain_weight_eq_zero` include noncommutative rings,
  zero rings and both axes: `(0,b)` gives `1-X₁` for `b ≠ 0`, and `(a,0)`
  gives `X₀-1` for `a ≠ 0`. Weights `(6,4)` give `X₀²-X₁³`.
  The pair `(0,0)` is excluded; its kernel generally needs both `X₀-1` and
  `X₁-1`. No full-target surjectivity is assumed or asserted.
- **Hankel presentation:** For `1 ≤ n`,
  [`hankelIdeal_eq_ker`](ToricIdeals/RationalNormalCurve.lean) identifies `I(R,n)`
  with the kernel of `f` and the quotient with its **image subring**, not the
  full target. At `n = 0` the inclusion is strict for nontrivial `R`; at `n = 1`
  the raw map is injective. The module proves energy-decreasing reduction and
  terminal uniqueness; chosen representatives are classical, not executable canonical forms.
- **Raw-map injectivity, surjectivity and freeness:** Over any **commutative
  semiring** `R`, each holds exactly when `n = 1 ∨ Subsingleton R`
  ([injectivity](ToricIdeals/RationalNormalCurve/Injectivity.lean),
  [surjectivity](ToricIdeals/RationalNormalCurve/MapSurjectivity.lean),
  [freeness](ToricIdeals/RationalNormalCurve/Freeness.lean)). Source and target are
  the full polynomial semirings. Freeness uses `p • q = f(p) * q` and an arbitrary,
  not necessarily finite, basis. At degree zero `X₀` maps to `1`.
- **Relative finiteness and flatness:** Over commutative semirings, the raw map
  is [of finite type in every degree](ToricIdeals/RationalNormalCurve/ParametrizationFinite.lean);
  its full target is a finite **source**-module iff `n ≠ 0 ∨ Subsingleton R`.
  Over commutative rings, [raw-map flatness](ToricIdeals/RationalNormalCurve/MapFlatness.lean)
  and [formal unramifiedness](ToricIdeals/RationalNormalCurve/MapUnramified.lean)
  each hold iff `n = 1 ∨ Subsingleton R`, via `f.toAlgebra`, not coefficient-`R`
  or quotient scalars. The [full-quotient-to-full-target map](ToricIdeals/RationalNormalCurve/QuotientMapFlatness.lean)
  has the same flatness criterion, with action `q • p = quotientMap R n q * p`.
- **Coefficient modules and endpoints:** `Q(R,n)` is
  [free and faithfully flat over `R`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean)
  in every degree. Coefficient-module finite generation, Noetherianity and
  Artinianity each hold iff `Subsingleton R`. The
  [endpoint map](ToricIdeals/RationalNormalCurve/EndpointMap.lean) makes it integral
  and finite over `MvPolynomial (Fin 2) R` in every degree; for `1 ≤ n` it is
  injective with `Fin n`-indexed basis `1, X₁, …, Xₙ₋₁`, using exactly
  `Algebra.toModule` for `endpointMap.toAlgebra`: `p • q = endpointMap n p * q`.
  The [augmentation](ToricIdeals/RationalNormalCurve/Augmentation.lean) kills **all**
  variables and retracts `R`; the separate [axis projection](ToricIdeals/RationalNormalCurve/AxisProjection.lean)
  retains `X₀`, splits onto `R[X]`, and is an isomorphism at `n = 0`.
- **Ring criteria and regular coordinates:** In every degree `Q(R,n)` is a
  domain, reduced, Noetherian or Jacobson iff `R` has the respective property;
  primality and radicality of `I(R,n)` detect a domain and a reduced ring.
  Artinianity **over itself** holds iff `Subsingleton R`, not merely if `R` is
  Artinian. Every [coordinate class is regular](ToricIdeals/RationalNormalCurve/CoordinateRegularity.lean),
  even over nilpotent coefficients and zero rings: both multiplication maps are
  injective, not a regular-sequence assertion. [Detailed criteria](docs/Results.md).
- **Integral closedness and dimension:** For a **commutative domain** `R`,
  [`quotient_isIntegrallyClosed_iff`](ToricIdeals/RationalNormalCurve/IntegralClosure.lean)
  says `Q(R,n)` is integrally closed iff `R` is. For a **Noetherian commutative
  ring** `R`, [Krull dimension](ToricIdeals/RationalNormalCurve/Dimension.lean) is
  `ringKrullDim Q(R,n) = ringKrullDim R + (if n = 0 then 1 else 2)` in `WithBot ℕ∞`,
  including zero rings of dimension `⊥` and infinite coefficient dimension.
- **Formal smoothness over coefficients:** For every commutative ring `R`,
  [`quotient_formallySmooth_iff`](ToricIdeals/RationalNormalCurve/FormallySmooth.lean)
  states `Algebra.FormallySmooth R Q(R,n) ↔ n ≤ 1 ∨ Subsingleton R` for the canonical
  coefficient algebra. This includes `Q(R,0) = R[X₀]`, zero rings and characteristic
  two; it is not formal unramifiedness of the raw map over its full source.
- **Grading, homogeneous coordinates and vertex cotangents:** The
  [source Hankel ideal is homogeneous](ToricIdeals/RationalNormalCurve/Homogeneous.lean).
  The full quotient has its standard multiplicative grading and unique finite
  homogeneous reconstruction. Its degree-`d` component has a coefficient basis
  indexed by `Fin (n*d+1)`; at `n = 0` its vector is `[X₀^d]`. The augmentation
  kernel `J` has cotangent module `J/J²` with a `Fin (n+1)`-indexed coefficient
  basis of variable classes; coordinates are raw linear coefficients of
  representatives with zero constant coefficient. At `n = 0` its vector is `[X₀]`.
  Indexed bases over zero rings assert no numerical rank. Both
  [GradedAlgebra](ToricIdeals/RationalNormalCurve/GradedAlgebra.lean) and
  [Cotangent](ToricIdeals/RationalNormalCurve/Cotangent.lean) require **direct imports**.
- **Arbitrary base change:** For commutative rings `R`, `S` with `[Algebra R S]`
  in independent universes, [`S ⊗[R] Q(R,n) ≃ₐ[S] Q(S,n)`](ToricIdeals/RationalNormalCurve/BaseChange.lean)
  in every degree, without flatness or injectivity. [Homogeneous-component bases](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean)
  retain their indices under arbitrary coefficient change; their scalar-extension
  equivalences commute with inclusions into the full quotients and base change.
  Zero and nilpotent coefficients are included.
- **Arithmetic exponent image:** The [coefficient-free criterion](ToricIdeals/RationalNormalCurve/ExponentImage.lean)
  for a target `t : Fin 2 →₀ ℕ` is `n ∣ (t 0 + t 1)`, including `n = 0`,
  when only the zero target occurs.
- **The split quadric:** For any commutative ring `A`, substitution
  `(w,x,y,z) ↦ (W,WT,Y,YT)` has kernel `(wz - xy)`; the quotient identifies with
  the **range**, not the whole target. Its domain/primality criterion is `IsDomain A`.
  The coefficient-free exponent image is `t ≤ u+v`, with unique reduced
  representatives; the total selector is a preimage only there and is not additive.
  The `w`- and `W`-charts are equivalent for independent localization models with
  both `A`-scalar towers, without domain or nontriviality hypotheses. See the
  [split-quadric guide](docs/SplitQuadric.md).

This library does not classify general toric ideals or prove rational-normal-curve
results outside the stated parametrization and hypotheses. Source-passage
correspondence and coverage are tracked separately, not claimed here. See the
[full result statements and scalar conventions](docs/Results.md).

## Modules

The root import `ToricIdeals` re-exports the leaves below except
`ToricIdeals.RationalNormalCurve.Cotangent` and
`ToricIdeals.RationalNormalCurve.GradedAlgebra`, which require direct imports.

| Module | Contents |
| --- | --- |
| [`ToricIdeals`](ToricIdeals.lean) | Root import for the re-exported public APIs |
| [`ToricIdeals.HomogeneousImage`](ToricIdeals/HomogeneousImage.lean) | Transport of internal submodule decompositions under surjective linear maps with homogeneous kernel |
| [`ToricIdeals.MonoidAlgebra.FiberNormalization`](ToricIdeals/MonoidAlgebra/FiberNormalization.lean) | Coefficientwise normalization and kernel criteria |
| [`ToricIdeals.MonoidAlgebra.CoprimeWeights`](ToricIdeals/MonoidAlgebra/CoprimeWeights.lean) | Coprime two-variable weight kernels and all-coefficient binomial membership over any ring |
| [`ToricIdeals.MonoidAlgebra.NaturalWeights`](ToricIdeals/MonoidAlgebra/NaturalWeights.lean) | Gcd-reduced two-variable natural-weight kernels and membership criteria over any ring |
| [`ToricIdeals.Polynomial.FiniteSubalgebra`](ToricIdeals/Polynomial/FiniteSubalgebra.lean) | Finite spanning powers and module finiteness over a subalgebra containing a positive power of `X`, over any commutative semiring |
| [`ToricIdeals.RationalNormalCurve`](ToricIdeals/RationalNormalCurve.lean) | Hankel presentation, reduction, kernel and quotient criteria |
| [`ToricIdeals.RationalNormalCurve.Augmentation`](ToricIdeals/RationalNormalCurve/Augmentation.lean) | Coefficient augmentation, its variable-span kernel and membership criterion in every degree |
| [`ToricIdeals.RationalNormalCurve.Cotangent`](ToricIdeals/RationalNormalCurve/Cotangent.lean) | Coefficient-ring basis of the augmentation kernel modulo its square, prescribed quotient-variable vectors and raw linear coordinates; direct import |
| [`ToricIdeals.RationalNormalCurve.CoefficientAlgebra`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean) | Freeness, flatness and faithful flatness of the full Hankel quotient for its canonical coefficient action in every degree |
| [`ToricIdeals.RationalNormalCurve.CoefficientMap`](ToricIdeals/RationalNormalCurve/CoefficientMap.lean) | Injectivity and surjectivity of full Hankel quotient coefficient maps in every degree |
| [`ToricIdeals.RationalNormalCurve.Dimension`](ToricIdeals/RationalNormalCurve/Dimension.lean) | Full Hankel quotient dimension in every degree over Noetherian commutative coefficient rings, with degree-zero and degree-one specializations |
| [`ToricIdeals.RationalNormalCurve.EndpointMap`](ToricIdeals/RationalNormalCurve/EndpointMap.lean) | Endpoint evaluation, all-degree integrality and finiteness, positive-degree injectivity, full-quotient endpoint basis and coordinate API |
| [`ToricIdeals.RationalNormalCurve.ExponentImage`](ToricIdeals/RationalNormalCurve/ExponentImage.lean) | Arithmetic characterization of the natural exponent image in every degree |
| [`ToricIdeals.RationalNormalCurve.FormallySmooth`](ToricIdeals/RationalNormalCurve/FormallySmooth.lean) | All-degree formal-smoothness criterion for the full Hankel quotient over arbitrary commutative coefficients |
| [`ToricIdeals.RationalNormalCurve.Freeness`](ToricIdeals/RationalNormalCurve/Freeness.lean) | All-degree full-source module freeness criterion over commutative semirings |
| [`ToricIdeals.RationalNormalCurve.GradedAlgebra`](ToricIdeals/RationalNormalCurve/GradedAlgebra.lean) | Standard multiplicative grading of the full Hankel quotient and degree-zero projection compatibility with coefficient augmentation; direct import |
| [`ToricIdeals.RationalNormalCurve.Homogeneous`](ToricIdeals/RationalNormalCurve/Homogeneous.lean) | Standard source-graded homogeneity of the Hankel ideal |
| [`ToricIdeals.RationalNormalCurve.HomogeneousBasis`](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean) | Internal homogeneous decomposition of the full Hankel quotient, finite coefficient bases and coordinates of its components, preserved with their indices under arbitrary coefficient change |
| [`ToricIdeals.RationalNormalCurve.Injectivity`](ToricIdeals/RationalNormalCurve/Injectivity.lean) | All-degree raw parametrization injectivity over commutative semirings |
| [`ToricIdeals.RationalNormalCurve.IntegralClosure`](ToricIdeals/RationalNormalCurve/IntegralClosure.lean) | In every degree, the full Hankel quotient over a commutative domain is integrally closed if and only if its coefficient ring is |
| [`ToricIdeals.RationalNormalCurve.MapFlatness`](ToricIdeals/RationalNormalCurve/MapFlatness.lean) | All-degree full-source ring-map flatness criterion over commutative rings |
| [`ToricIdeals.RationalNormalCurve.MapSurjectivity`](ToricIdeals/RationalNormalCurve/MapSurjectivity.lean) | All-degree full-target raw parametrization surjectivity over commutative semirings |
| [`ToricIdeals.RationalNormalCurve.MapUnramified`](ToricIdeals/RationalNormalCurve/MapUnramified.lean) | All-degree formal unramifiedness over the full raw parametrization source, via its induced algebra structure, over commutative rings |
| [`ToricIdeals.RationalNormalCurve.QuotientMap`](ToricIdeals/RationalNormalCurve/QuotientMap.lean) | Full Hankel quotient parametrization and representative formulas in every degree |
| [`ToricIdeals.RationalNormalCurve.QuotientMapFlatness`](ToricIdeals/RationalNormalCurve/QuotientMapFlatness.lean) | All-degree flatness criterion for the full target over the full Hankel quotient |
| [`ToricIdeals.RationalNormalCurve.ParametrizationFinite`](ToricIdeals/RationalNormalCurve/ParametrizationFinite.lean) | All-degree finite type and relative finite-module criterion for the full raw parametrization over commutative semirings |
| [`ToricIdeals.RationalNormalCurve.Noetherian`](ToricIdeals/RationalNormalCurve/Noetherian.lean) | All-degree Noetherian ring and left coefficient-module criteria |
| [`ToricIdeals.RationalNormalCurve.Jacobson`](ToricIdeals/RationalNormalCurve/Jacobson.lean) | All-degree coefficient criterion for quotient Jacobsonness |
| [`ToricIdeals.RationalNormalCurve.Artinian`](ToricIdeals/RationalNormalCurve/Artinian.lean) | All-degree Artinian ring and left coefficient-module criteria |
| [`ToricIdeals.RationalNormalCurve.AxisProjection`](ToricIdeals/RationalNormalCurve/AxisProjection.lean) | Coordinate-axis algebra map, split surjection and characteristic universal property |
| [`ToricIdeals.RationalNormalCurve.CoefficientFiniteness`](ToricIdeals/RationalNormalCurve/CoefficientFiniteness.lean) | All-degree finiteness criterion for the canonical coefficient module |
| [`ToricIdeals.RationalNormalCurve.BaseChange`](ToricIdeals/RationalNormalCurve/BaseChange.lean) | Scalar base change of the full Hankel quotient over arbitrary commutative rings in every degree |
| [`ToricIdeals.RationalNormalCurve.CoordinateRegularity`](ToricIdeals/RationalNormalCurve/CoordinateRegularity.lean) | Regularity of every coordinate class over arbitrary commutative rings in every degree |
| [`ToricIdeals.SplitQuadric.Exponents`](ToricIdeals/SplitQuadric/Exponents.lean) | Exponent reduction, image cone and unique reduced representatives |

The split-quadric interface is re-exported by [`ToricIdeals.SplitQuadric`](ToricIdeals/SplitQuadric.lean);
see its [leaf imports and namespaces](docs/Results.md#split-quadric-imports-and-namespaces).

## Use

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "toric-ideals"
git = "https://github.com/FormalFrontier/toric-ideals.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the latest release when
first added or updated; `lake-manifest.json` locks that commit until the next
update. To pin a release, replace `main` with a full commit from that history.
Libraries used together must share a compatible Mathlib revision and toolchain;
see [build](#build) for this checkout's pinned environment.

Import `ToricIdeals` or a leaf directly. For vertex cotangents or quotient grading,
import `ToricIdeals.RationalNormalCurve.Cotangent` or
`ToricIdeals.RationalNormalCurve.GradedAlgebra` directly, respectively.
This complete example is stored verbatim in
[`ToricIdealsTest/ReadmeKernel.lean`](ToricIdealsTest/ReadmeKernel.lean), built by the default test target:

```lean
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals.RationalNormalCurve

/-! # README example: the positive-degree kernel through a direct leaf import -/

open ToricIdeals.RationalNormalCurve

universe u

private theorem readme_degree_two_kernel (k : Type u) [CommRing k] :
    hankelIdeal k 2 = RingHom.ker (rncMap k 2) :=
  hankelIdeal_eq_ker k 2 (by decide)
```

The root-import client in
[`ToricIdealsTest/CoprimeWeights.lean`](ToricIdealsTest/CoprimeWeights.lean)
uses the weighted-image membership criterion at `(a,b)=(2,3)` for the distinct
exponents `(5,1)` and `(1,7)`. It proves ideal membership by vanishing under
the weight pushforward and nonvanishing of the integer binomial, whose common
weight is `17`.

See the [API guide](docs/README.md) for theorem usage and stored boundary examples.

## Build

Use the repository's `lean-toolchain` and pinned `lake-manifest.json`. Fetch the
matching precompiled mathlib cache before building:

```sh
lake exe cache get
lake build
```

The default build includes `ToricIdeals` and all registered `ToricIdealsTest`
modules. Focused checks are `lake build ToricIdeals` or `lake build ToricIdealsTest`
after fetching the same cache. The [selected-module reference](docs/API.md) and
its [input manifest](docs/api-manifest.json) describe an earlier, limited input
set, not all current declarations. Documentation ships as Markdown, without an
interactive dependency website.

## Conventions and limitations

Raw Source/Target APIs use universe-polymorphic commutative semirings; Hankel
ideals and quotients use commutative rings. In degrees zero and one the Hankel
ideal is `⊥`, giving the full polynomial rings on `Fin 1` and `Fin 2`. Quotient,
raw-source, coefficient and endpoint scalar actions are distinct; see the
[detailed conventions and examples](docs/Results.md#scalar-conventions).

## References and credits

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
2025 draft, Exercise 3.6.F) motivates the Hankel presentation, not the Jacobson
criterion. No source text or PDF is reproduced; the citation implies neither
participation nor endorsement. Dependencies are mathlib, multivariate-polynomials
and minimal-primes, all Apache-2.0. The [full credits](docs/Credits.md) preserve
proof-family attributions, dependency and complete-license links, and tool/AI
credit. Lean and doc-gen4 are separately credited tools, not bundled sources.
`Authors: Formal Frontier Agents` is collective credit, not a copyright-ownership claim.
