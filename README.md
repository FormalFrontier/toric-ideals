# toric-ideals

Authors: Formal Frontier Agents. Original Formal Frontier contributions are
licensed under Apache-2.0; see the complete root `LICENSE` file. The project
uses AI-assisted formalization and review.

Reusable Lean 4 theory of coefficientwise normalization over rings, monomial-map
kernels, the Hankel ideal of the rational normal curve over arbitrary
commutative coefficient rings, and natural-number exponent normal forms for
the split quadric, together with its coordinate algebra and localization charts.

## Headline results

- **Integral closedness of full Hankel quotients:** For any commutative domain
  `R` and every `n : ℕ`,
  [`quotient_isIntegrallyClosed_iff`](ToricIdeals/RationalNormalCurve/IntegralClosure.lean)
  states `IsIntegrallyClosed (Source R n ⧸ hankelIdeal R n) ↔ IsIntegrallyClosed R`,
  using the canonical quotient and integral-closedness predicate. At `n = 0` the
  full quotient is `R[X₀]`, not the raw parameterization image `R`.

- **Coefficientwise fiber normalization:** When *every* source monomial and
  coefficient is congruent modulo a left ideal to a source exponent chosen by
  its target index, an element whose coefficients sum to zero along target
  fibers belongs to that ideal. The [generic theorem](ToricIdeals/MonoidAlgebra/FiberNormalization.lean)
  works over any ring with an additive source monoid and an arbitrary index
  function to a bare type, in independent universes. For additive exponent
  homomorphisms between additive monoids it gives kernel containment; if the
  ideal is also contained in that kernel, it gives equality and a membership
  characterization. No commutativity, surjectivity, section or domain hypothesis
  is needed. The raw index function is not asserted to induce a ring map.
- **Raw parametrization injectivity:** For every `(R : Type u) [CommSemiring R]`
  and `n : ℕ`, [`rncMap_injective_iff`](ToricIdeals/RationalNormalCurve/Injectivity.lean)
  says `Function.Injective (rncMap R n) ↔ n = 1 ∨ Subsingleton R` on
  the full `Source R n = MvPolynomial (Fin (n + 1)) R`.
  This includes zero semirings and degree zero, without a field or domain premise.
- **Raw parametrization surjectivity:** For every `(R : Type u) [CommSemiring R]`
  and `n : ℕ`,
  [`rncMap_surjective_iff`](ToricIdeals/RationalNormalCurve/MapSurjectivity.lean)
  says `Function.Surjective (rncMap R n) ↔ n = 1 ∨ Subsingleton R` onto
  the full `Target R = MvPolynomial (Fin 2) R`. Degree zero has constant
  image and sends its sole source variable to `1`; it is onto only for zero
  coefficients. This concerns the raw map, not the Hankel quotient or its
  image equivalence. See the [surjectivity guide](docs/README.md#raw-parametrization-surjectivity).
- **Freeness over the raw parametrization source:** For every
  `(R : Type u) [CommSemiring R]` and `n : ℕ`,
  [`rncMap_moduleFree_iff`](ToricIdeals/RationalNormalCurve/Freeness.lean)
  says that the full `Target R = MvPolynomial (Fin 2) R` is free over the
  full `Source R n = MvPolynomial (Fin (n + 1)) R` exactly when
  `n = 1 ∨ Subsingleton R`. The theorem explicitly supplies the module
  `@Algebra.toModule ... (rncMap R n).toAlgebra`, whose action is
  `p • q = rncMap R n p * q`; this matters even when the carriers coincide
  in degree one. Freeness means existence of an arbitrary basis, not a finite
  basis. Zero semirings and degree zero are included: the full source variable
  still maps to `1`. No ring, domain, Noetherianity, nontriviality or
  positive-degree premise is needed. This differs from coefficient-module
  freeness of the Hankel quotient and from the ring-map flatness result below.
  [Stored clients](ToricIdealsTest/Audit/RationalNormalCurveFreenessClient.lean)
  use both directions, alongside
  [independent models](ToricIdealsTest/Audit/RationalNormalCurveFreenessModels.lean).
- **Raw parametrization flatness:** For every `(R : Type u) [CommRing R]`
  and `n : ℕ`,
  [`rncMap_flat_iff`](ToricIdeals/RationalNormalCurve/MapFlatness.lean)
  says `(rncMap R n).Flat ↔ n = 1 ∨ Subsingleton R`. This is genuine
  ring-map flatness of the full `Target R = MvPolynomial (Fin 2) R` over
  the full `Source R n = MvPolynomial (Fin (n + 1)) R`, with
  `p • q = rncMap R n p * q`. Zero rings and degree zero are included,
  without a domain, Noetherianity or positive-degree premise. This is
  distinct from coefficient-flatness of the Hankel quotient; see the
  [flatness guide](docs/README.md#raw-parametrization-flatness).
- **Formal unramifiedness over the raw parametrization source:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`,
  [`rncMap_formallyUnramified_iff`](ToricIdeals/RationalNormalCurve/MapUnramified.lean)
  says `RingHom.FormallyUnramified (rncMap R n) ↔ n = 1 ∨ Subsingleton R`.
  The base is the full `Source R n = MvPolynomial (Fin (n + 1)) R` through
  `(rncMap R n).toAlgebra`, and the target is the full bivariate polynomial
  ring `Target R`. This is not formal unramifiedness over the coefficient
  ring `R`, nor a property of the Hankel quotient or parametrization image.
  Degree zero retains the source `R[X₀]` and sends `X₀` to `1`, not `0`;
  the property is false for every nonzero `R`. Degree one is the identity,
  and zero coefficient rings give formal unramifiedness in every degree.
  No domain, nontriviality or positive-degree hypothesis is needed.
- **Flatness over the full Hankel quotient:** For every
  `(R : Type u) [CommRing R]` and every `n : ℕ`,
  [`quotientMap_flat_iff`](ToricIdeals/RationalNormalCurve/QuotientMapFlatness.lean)
  says `(quotientMap R n).toRingHom.Flat ↔ n = 1 ∨ Subsingleton R`.
  Here [`quotientMap`](ToricIdeals/RationalNormalCurve/QuotientMap.lean) goes
  from the full `Source R n ⧸ hankelIdeal R n` to the full bivariate
  `Target R`, not to the parametrization image. Its scalar action is
  `q • p = quotientMap R n q * p`. No domain, nontriviality or
  positive-degree assumption is needed. Degree zero retains its source
  variable in the quotient although its image is `1`; degree one is flat
  over every coefficient ring, and zero coefficients give flatness in all
  degrees. For nontrivial coefficients and `2 ≤ n`, the
  [named clients](ToricIdealsTest/QuotientMapFlatnessType.lean) contrast
  coefficient-`R` flatness of the full quotient with nonflatness of this
  quotient-to-target map. The
  [independent boundary controls](ToricIdealsTest/QuotientMapFlatnessModels.lean)
  use a separate quotient lift and include nilpotent `ZMod 4` coefficients.
- **Raw parametrization finite type and module finiteness:** For every
  `(R : Type u) [CommSemiring R]` and `n : ℕ`, let
  `f = rncMap R n : Source R n →+* Target R`, with `Xᵢ ↦ U^(n-i)V^i`.
  [`rncMap_finiteType`](ToricIdeals/RationalNormalCurve/ParametrizationFinite.lean)
  gives `Algebra.FiniteType (Source R n) (Target R)` via `f.toAlgebra`
  in every degree.
  [`rncMap_moduleFinite_iff`](ToricIdeals/RationalNormalCurve/ParametrizationFinite.lean)
  gives `Module.Finite (Source R n) (Target R) ↔ n ≠ 0 ∨ Subsingleton R`
  via `f.toAlgebra.toModule`: `s • t = f(s) * t`.
  These are finite-generation properties for algebras and modules, also over
  semirings. The scalars are the full source, not `R` or the Hankel quotient;
  no ring, Noetherian, nontriviality or positive-degree hypothesis is needed.
  Degree zero retains `X₀` in the source but sends it to `1`: the target is
  of finite type, yet not a finite source-module for nontrivial `R`.
  In degree one the map is an isomorphism.
- **Hankel presentation of a rational normal curve:** For `1 ≤ n`, the
  parametrization `xᵢ ↦ a^(n-i)b^i` has kernel exactly the ideal generated by
  the `2 × 2` Hankel minors, over *any* commutative coefficient ring
  ([`hankelIdeal_eq_ker`](ToricIdeals/RationalNormalCurve.lean)).
  At `n = 0` the inclusion is strict when the ring is nontrivial, while a
  stored subsingleton client gives equality; at `n = 1` the map is injective
  without a field or domain hypothesis. The [curve module](ToricIdeals/RationalNormalCurve.lean)
  develops the decreasing-energy reduction and uniqueness *among terminal
  exponents*; its choices are classical, not executable canonical algorithms.
- **Free and faithfully flat coefficient modules in every degree:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`,
  [`quotient_free`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean)
  says that the full Hankel quotient `Source R n ⧸ hankelIdeal R n` is free
  for its canonical coefficient action, and
  [`quotient_flat`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean)
  gives flatness as a consequence.
  [`quotient_faithfullyFlat`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean)
  gives genuine `Module.FaithfullyFlat R (Source R n ⧸ hankelIdeal R n)`.
  All coefficient universes and zero rings are included; no domain,
  Noetherianity, nontriviality or positive-degree assumption is needed.
  At `n = 0` this is the full one-variable polynomial quotient by `⊥`: the variable survives, unlike
  the raw parametrization `X₀ ↦ 1`; the quotient is not replaced by the
  parametrization image.
  The [coefficient-module clients](ToricIdealsTest/CoefficientAlgebraUses.lean)
  use freeness to cancel integer doubling and flatness to preserve
  injectivity under tensoring. The
  [faithfully-flat clients](ToricIdealsTest/Audit/RationalNormalCurveCoefficientFaithfullyFlatClients.lean)
  directly use Mathlib's tensor injectivity **iff** and injection
  `m ↦ 1 ⊗ m` for arbitrary coefficient modules in independent universes,
  without flatness of those modules or an action by the quotient. These
  coefficient-module properties are distinct from freeness and flatness
  over the full raw-parametrization source above.
  The [coefficient augmentation](ToricIdeals/RationalNormalCurve/Augmentation.lean)
  has kernel exactly the ideal spanned by all variable classes, also in degree
  zero and over zero rings. The [quotient clients](ToricIdealsTest/Audit/RationalNormalCurveAugmentationKernel.lean)
  use Mathlib's first isomorphism theorem to recover the coefficient algebra by
  quotienting this span; nonzero square-zero coefficients are retained.
- **Vertex cotangent coordinates:** For every `(R : Type u) [CommRing R]` and
  `n : ℕ`,
  [`quotientAugmentationCotangentBasis`](ToricIdeals/RationalNormalCurve/Cotangent.lean)
  is a `Fin (n + 1)`-indexed coefficient-ring basis of Mathlib's module `I/I²`,
  where `I` is the kernel of the coefficient augmentation of the full Hankel
  quotient. Its vectors are the classes of the quotient variables, and the
  coordinates of every representative with zero constant coefficient are its
  raw linear coefficients. The action is the inherited canonical coefficient
  action. At `n = 0` the vector is `[X₀]`, not `1`; over zero rings this is an
  indexed basis, not a numerical rank assertion. Import
  `ToricIdeals.RationalNormalCurve.Cotangent` directly for this API.
- **Scalar base change in every degree:** For arbitrary commutative rings
  `R : Type u` and `S : Type v` with `[Algebra R S]`, write
  $Q_{R,n}=R[X_0,\ldots,X_n]/I_{R,n}$, where $I_{R,n}$ is the Hankel-minor ideal.
  For every `n : ℕ`,
  [`quotientBaseChangeAlgEquiv`](ToricIdeals/RationalNormalCurve/BaseChange.lean)
  gives $S\otimes_R Q_{R,n}\simeq_S Q_{S,n}$ as an `S`-algebra equivalence.
  No flatness, injectivity, domain, Noetherianity, nontriviality or
  positive-degree hypothesis is needed, and `u` and `v` are independent.
  This is the full Hankel quotient, including the polynomial cases `n = 0, 1`,
  not a replacement by the parametrization image; see
  [base change and its representative formula](docs/README.md#scalar-base-change-of-hankel-quotients).
- **Endpoint coordinates, basis and finite Hankel quotient:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`, the Hankel quotient
  `Source R n ⧸ hankelIdeal R n` is integral and a finite module over
  `MvPolynomial (Fin 2) R` through
  [`endpointMap`](ToricIdeals/RationalNormalCurve/EndpointMap.lean)
  ([`endpointMap_isIntegral`](ToricIdeals/RationalNormalCurve/EndpointMap.lean),
  [`endpointMap_finite`](ToricIdeals/RationalNormalCurve/EndpointMap.lean)).
  For `1 ≤ n`, the endpoint map is injective
  ([`endpointMap_injective`](ToricIdeals/RationalNormalCurve/EndpointMap.lean)), and
  [`endpointBasis`](ToricIdeals/RationalNormalCurve/EndpointMap.lean) is a
  `Fin n`-indexed basis of the full quotient with vectors `1, X₁, …, Xₙ₋₁`.
  Its module is exactly `Algebra.toModule` for `endpointMap.toAlgebra`, so
  scalars act by `p • q = endpointMap n p * q`. The `repr` API
  (`endpointBasis_repr_one`, `endpointBasis_repr_X`,
  `endpointBasis_repr_endpointMap` and `endpointBasis_repr_endpointMap_mul`)
  gives the coordinates of the unit, interior variable classes and endpoint
  polynomials, and computes multiplication by endpoint polynomials coordinatewise.
  These statements allow arbitrary commutative coefficient rings, including
  the zero ring; the indexed basis makes no numerical rank or normality claim.
  Finite freeness and flatness over the endpoint polynomial ring alone do not
  prove normality.
  At `n = 0`, the Hankel ideal is `⊥`: the target is the full one-variable
  polynomial quotient, retaining all `X₀^d`, and both endpoints map to its
  single variable class, rather than using the raw parametrization `X₀ ↦ 1`.
- **Finite coefficient modules in every degree:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`,
  [`quotient_moduleFinite_iff`](ToricIdeals/RationalNormalCurve/CoefficientFiniteness.lean)
  says `Module.Finite R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R`
  for the canonical coefficient action. Thus every nonzero coefficient ring
  gives a quotient that is not finitely generated over `R`, even in degree
  zero, with its full one-variable polynomial quotient. No Noetherian, domain
  or positive-degree hypothesis is needed. This does not contradict
  `endpointMap_finite`: its scalars are `MvPolynomial (Fin 2) R`, not `R`.
  See the [coefficient-module guide](docs/README.md#finite-coefficient-modules-of-hankel-quotients).
- **Arithmetic exponent image:** For every `n : ℕ` and natural-valued target
  `t : Fin 2 →₀ ℕ`,
  [`mem_mrange_rncExponent_iff`](ToricIdeals/RationalNormalCurve/ExponentImage.lean)
  says that `t` lies in the additive image exactly when `n ∣ (t 0 + t 1)`.
  At degree zero only the zero target occurs. The
  [independent small-degree examples](ToricIdealsTest/RationalNormalCurveExponentImageModels.lean)
  include mixed conic and cubic images and excluded targets. For `1 ≤ n`, the
  [selector client](ToricIdealsTest/RationalNormalCurveExponentImageClient.lean)
  derives terminality and the preimage law for `fiberNormalExponent ℤ n t`
  from divisibility alone, including the cubic family `(4m+2, 2m+1)`.
  Here `ℤ` only instantiates the existing selector's coefficient-ring parameter;
  the image criterion itself is coefficient-free.
- **Primality and quotient domains in every degree:** For any commutative
  coefficient ring `R` and every `n : ℕ`, including zero,
  [`hankelIdeal_isPrime_iff`](ToricIdeals/RationalNormalCurve.lean) and
  [`quotient_isDomain_iff`](ToricIdeals/RationalNormalCurve.lean) say that the
  Hankel ideal is prime and its quotient is a domain, respectively, **if and only
  if `R` is a domain**. Neither criterion assumes nontriviality or positive degree.
- **Positive-degree quotient image and spectrum:** For `1 ≤ n`,
  [`quotientEquivRange`](ToricIdeals/RationalNormalCurve.lean) identifies the
  quotient by the Hankel ideal with the **image subring** of the monomial map,
  not the whole target ring. With the *additional* assumption `[IsDomain k]`,
  the positive-degree corollaries
  [`hankelIdeal_isPrime`](ToricIdeals/RationalNormalCurve.lean),
  [`quotient_isDomain`](ToricIdeals/RationalNormalCurve.lean) and
  [`spectrum_irreducible`](ToricIdeals/RationalNormalCurve.lean) give the
  prime-ideal, quotient-domain and irreducible-prime-spectrum consequences.
- **Reduced quotient and radical ideal in every degree:** For every
  `(R : Type u) [CommRing R]` and every `n : ℕ`,
  [`quotient_isReduced_iff`](ToricIdeals/RationalNormalCurve.lean) says that
  the quotient by the Hankel minors is reduced exactly when `R` is reduced;
  [`hankelIdeal_isRadical_iff`](ToricIdeals/RationalNormalCurve.lean) gives the
  same characterization of ideal radicality. No nontriviality, domain, field,
  cancellation or positive-degree assumption is needed.
- **Homogeneous Hankel ideal in every degree:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`,
  [`hankelIdeal_isHomogeneous`](ToricIdeals/RationalNormalCurve/Homogeneous.lean)
  says that the original Hankel-minor ideal is `Ideal.IsHomogeneous` for
  Mathlib's standard natural-number grading of the source polynomial ring.
  Thus every homogeneous component of a member again belongs to the ideal,
  and membership is equivalent to membership of all components. Zero rings
  and `n = 0, 1` are included, with no nontriviality or positive-degree premise.
  This result constructs no quotient grading; finite homogeneous components
  are described by the coefficient bases below.
- **Unique finite homogeneous reconstruction:** For every
  `(R : Type u) [CommRing R]` and every `n : ℕ`,
  [`quotientHomogeneousSubmodule_isInternal`](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean)
  identifies the full Hankel quotient with the internal direct sum of its
  homogeneous image submodules. Every quotient element has a unique finitely
  supported family of homogeneous components, whose sum is that element.
  Mathlib's `chooseDecomposition`, `decomposeLinearEquiv` and reconstruction
  operations provide the corresponding decomposition data. Zero rings,
  nilpotent coefficients and `n = 0` are included; at `n = 0` the components
  retain the powers of the surviving polynomial variable. No field, domain,
  nontriviality, flatness or positive-degree premise is required.
- **Standard graded algebra of the full Hankel quotient:** For every
  `(R : Type u) [CommRing R]` and `n : ℕ`,
  [`quotientHomogeneousGradedAlgebra`](ToricIdeals/RationalNormalCurve/GradedAlgebra.lean)
  supplies `GradedAlgebra (quotientHomogeneousSubmodule R n)` on the existing
  full quotient and its canonical coefficient action. Mathlib's decomposition
  algebra equivalence, typed graded products and projections are then available
  directly. `quotientHomogeneous_projZeroRingHom` identifies the quotient-valued
  degree-zero ring homomorphism with coefficient inclusion after
  `quotientAugmentation`; the degree-zero piece is the coefficient image.
  At parameter `n = 0`, the full quotient is `R[X₀]`, with `X₀` in homogeneous
  degree one, projected to zero rather than to its parametrization image `1`.
  Zero rings and nilpotent coefficients are included, without a field, domain
  or nontriviality assumption. The [degree-zero examples](ToricIdealsTest/Audit/RationalNormalCurveHomogeneousBasisClients.lean)
  use the integer conic and retain the nonzero variable at parameter zero and
  the nonzero square-zero coefficient `2` over `ZMod 4`.
- **Explicit homogeneous-component bases:** For every
  `(R : Type u) [CommRing R]` and all `n d : ℕ`,
  [`quotientHomogeneousBasis`](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean)
  is a `Module.Basis (Fin (n * d + 1)) R` of the image of the standard
  degree-`d` polynomial submodule in the **full Hankel quotient**. The action
  is the canonical coefficient action through `Ideal.Quotient.mkₐ`.
  `quotientHomogeneousCoordinates` supplies finite coordinates, an inverse
  finite-sum formula and reconstruction. For positive `n`, the `i`th coordinate
  of a representative is its parametrization coefficient at `(n*d-i, i)`,
  and the vectors are the existing terminal monomials. At `n = 0` the single
  vector is the surviving class of `X 0 ^ d`, not its parametrization image.
  Degree zero, zero rings and nilpotent coefficients are included, without
  field, domain, nontriviality or Noetherian assumptions. A basis indexed by
  `Fin (n*d+1)` over a zero ring does not assert distinct vectors or a numerical
  rank. The [coordinate clients](ToricIdealsTest/Audit/RationalNormalCurveHomogeneousBasisClients.lean)
  reconstruct a bivariate quadratic and retain a nonzero square-zero
  coefficient in the five-coordinate conic component over `ZMod 4`.
  [`quotientMap_quotientHomogeneousBasis`](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean)
  preserves every basis vector and its index under coefficient change along
  any homomorphism `R →+* S` of commutative rings in independent universes.
  The equality is in the full Hankel quotient, including `n = 0`, `d = 0`
  and zero rings, with no injectivity or flatness premise. The
  [coefficient-change clients](ToricIdealsTest/Audit/RationalNormalCurveHomogeneousBasisNaturality.lean)
  show how a nilpotent coefficient perturbation is erased by `ZMod 4 → ZMod 2`
  and retain the cubic variable class at `n = 0`.
  For any commutative `R`-algebra `S`,
  [`quotientHomogeneousBaseChangeEquiv`](ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean)
  identifies the scalar-extended component `S ⊗[R] H(R,n,d)` with `H(S,n,d)`
  as `S`-modules, where `H` denotes this homogeneous quotient submodule.
  It extends finite basis coordinates, sends `s ⊗ₜ bᵢ` to `s • bᵢ`, and
  commutes with the inclusions into the full quotients and their scalar-change
  equivalence, without flatness or injectivity assumptions.
- **Krull dimension in every degree:** For every
  `(R : Type u) [CommRing R] [IsNoetherianRing R]` and `n : ℕ`,
  [`ringKrullDim_quotient_hankelIdeal`](ToricIdeals/RationalNormalCurve/Dimension.lean)
  gives the full Hankel quotient formula
  `ringKrullDim (Source R n ⧸ hankelIdeal R n) = ringKrullDim R + (if n = 0 then 1 else 2)`.
  The equality takes values in `WithBot ℕ∞`, including zero rings (dimension
  `⊥`) and coefficients of infinite dimension. No field, domain, nontriviality,
  finite-dimension or positive-degree hypothesis is imposed. Degree zero retains
  its one polynomial variable; the quotient is not the raw parametrization image.
  The specializations
  [`ringKrullDim_quotient_hankelIdeal_zero`](ToricIdeals/RationalNormalCurve/Dimension.lean)
  and [`ringKrullDim_quotient_hankelIdeal_one`](ToricIdeals/RationalNormalCurve/Dimension.lean)
  give `ringKrullDim R + 1` and `ringKrullDim R + 2`, respectively.
- **Noetherian quotient in every degree:** For any `(R : Type u) [CommRing R]` and every
  `n : ℕ`, including zero,
  [`quotient_isNoetherianRing_iff`](ToricIdeals/RationalNormalCurve/Noetherian.lean)
  says that the quotient by the Hankel minors is Noetherian **if and only if
  `R` is Noetherian**. No field, domain, nontriviality or positive-degree
  assumption is needed. For the canonical left coefficient action,
  [`quotient_isNoetherian_iff`](ToricIdeals/RationalNormalCurve/Noetherian.lean)
  instead says `IsNoetherian R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R`.
  Thus a nonzero Noetherian coefficient ring gives a Noetherian quotient ring,
  but not a Noetherian coefficient module, in any degree.
- **Jacobson quotient in every degree:** For every `(R : Type u) [CommRing R]`
  and `n : ℕ`,
  [`quotient_isJacobsonRing_iff`](ToricIdeals/RationalNormalCurve/Jacobson.lean)
  says that the full quotient by the Hankel minors is Jacobson **if and only
  if `R` is Jacobson**. Zero rings and degrees zero and one are included;
  no Noetherian, domain, field, reducedness or positive-degree hypothesis is
  required.
- **Artinian quotient in every degree:** For any `(R : Type u) [CommRing R]`
  and every `n : ℕ`,
  [`quotient_isArtinianRing_iff`](ToricIdeals/RationalNormalCurve/Artinian.lean)
  says that the quotient by the Hankel minors is Artinian over itself **if and
  only if `R` is a zero ring**, expressed by `Subsingleton R`. This includes
  degrees zero and one, with their full polynomial quotients. For the canonical
  left coefficient action,
  [`quotient_isArtinian_iff`](ToricIdeals/RationalNormalCurve/Artinian.lean)
  says `IsArtinian R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R` as well.
  In particular, finite Artinian nonzero coefficients such as `ZMod 4` do not
  suffice for either Artinian criterion.
- **Coordinate-axis quotient in every degree:** For any `(R : Type u) [CommRing R]`
  and every `n : ℕ`,
  [`axisProjection`](ToricIdeals/RationalNormalCurve/AxisProjection.lean) maps
  `Source R n ⧸ hankelIdeal R n` to `Polynomial R`, preserving coefficients,
  retaining `X₀` as `Polynomial.X` and killing every other coordinate.
  Its polynomial section makes it a split surjection in every degree;
  the section is injective. At `n = 0` the projection is bijective, retaining
  the full one-variable polynomial quotient, not the parametrization image.
  For any semiring `R`-algebra in an independent universe and any element `x`,
  there is a unique algebra map killing the other coordinates and sending
  the first coordinate to `x`; the target need not be commutative.
- **Regular coordinates in every degree:** For any `[CommRing R]`, every
  `n : ℕ` and `i : Fin (n + 1)`,
  [`isRegular_quotient_X`](ToricIdeals/RationalNormalCurve/CoordinateRegularity.lean)
  says that multiplication by the class of `X i` in the Hankel quotient is
  injective on both sides, including over nilpotent coefficients and zero rings.
  At degree zero this is the full one-variable quotient by `⊥`, not the
  parametrization image. The [coordinate guide](docs/README.md#regular-coordinates-and-localization)
  explains cancellation, independent boundary models and the stored client
  proving injectivity of localization away from each coordinate class.
- **Split-quadric exponent normal forms:** For the substitution
  `(w, x, y, z) ↦ (W, WT, Y, YT)`, the additive exponent map is
  `E(a, b, c, d) = (a+b, c+d, b+d)`. Its image is exactly the cone
  `t ≤ u+v`, and each target exponent in that cone has a unique preimage
  reduced in the sense `a = 0 ∨ d = 0`
  ([`existsUnique_reduced_preimage_iff`](ToricIdeals/SplitQuadric/Exponents.lean)).
  Reduction preserves the image; the total selector `normal` is reduced
  everywhere but selects a preimage only on the cone. These are coefficient-free
  exponent results, not a polynomial-kernel or quotient-ring theorem.
- **Split-quadric coordinate algebra:** For every `[CommRing A]`, the kernel of
  `(w, x, y, z) ↦ (W, WT, Y, YT)` is `(wz - xy)`. The induced quotient map is
  injective and identifies the coordinate algebra with the range, not the whole
  target. The coordinate algebra is a domain, and the relation ideal is prime,
  exactly when `A` is a domain. The [split-quadric guide](docs/SplitQuadric.md)
  also describes the coefficient retraction and the equivalence of the `w`- and
  `W`-charts for independently chosen localization models, without domain or
  nontriviality assumptions.

This library does not classify general toric ideals or prove rational-normal-curve
results outside the stated parametrization and hypotheses. It is organized for
reuse independently of its source motivation; source-passage correspondence and
coverage are tracked separately and not claimed by this README.

## Modules

The root import `ToricIdeals` re-exports the leaves below except
`ToricIdeals.RationalNormalCurve.Cotangent` and
`ToricIdeals.RationalNormalCurve.GradedAlgebra`, which require direct imports.

| Module | Contents |
| --- | --- |
| [`ToricIdeals`](ToricIdeals.lean) | Root import for the re-exported public APIs |
| [`ToricIdeals.HomogeneousImage`](ToricIdeals/HomogeneousImage.lean) | Transport of internal submodule decompositions under surjective linear maps with homogeneous kernel |
| [`ToricIdeals.MonoidAlgebra.FiberNormalization`](ToricIdeals/MonoidAlgebra/FiberNormalization.lean) | Coefficientwise normalization and kernel criteria |
| [`ToricIdeals.RationalNormalCurve`](ToricIdeals/RationalNormalCurve.lean) | Hankel presentation, reduction, kernel and quotient criteria |
| [`ToricIdeals.RationalNormalCurve.Augmentation`](ToricIdeals/RationalNormalCurve/Augmentation.lean) | Coefficient augmentation, its variable-span kernel and membership criterion in every degree |
| [`ToricIdeals.RationalNormalCurve.Cotangent`](ToricIdeals/RationalNormalCurve/Cotangent.lean) | Coefficient-ring basis of the augmentation kernel modulo its square, prescribed quotient-variable vectors and raw linear coordinates; direct import |
| [`ToricIdeals.RationalNormalCurve.CoefficientAlgebra`](ToricIdeals/RationalNormalCurve/CoefficientAlgebra.lean) | Freeness, flatness and faithful flatness of the full Hankel quotient for its canonical coefficient action in every degree |
| [`ToricIdeals.RationalNormalCurve.Dimension`](ToricIdeals/RationalNormalCurve/Dimension.lean) | Full Hankel quotient dimension in every degree over Noetherian commutative coefficient rings, with degree-zero and degree-one specializations |
| [`ToricIdeals.RationalNormalCurve.EndpointMap`](ToricIdeals/RationalNormalCurve/EndpointMap.lean) | Endpoint evaluation, all-degree integrality and finiteness, positive-degree injectivity, full-quotient endpoint basis and coordinate API |
| [`ToricIdeals.RationalNormalCurve.ExponentImage`](ToricIdeals/RationalNormalCurve/ExponentImage.lean) | Arithmetic characterization of the natural exponent image in every degree |
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

The split-quadric interface is re-exported by
[`ToricIdeals.SplitQuadric`](ToricIdeals/SplitQuadric.lean). Its independent leaves
are `Basic`, `Exponents`, `MonomialReduction`, `ExponentParametrization`,
`CoefficientRetraction`, `Kernel`, `Consequences`, and `Examples`, under
`ToricIdeals.SplitQuadric`. Coordinate-algebra declarations retain the namespace
`SplitQuadric`; exponent declarations use `ToricIdeals.SplitQuadric`.

## Use

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "toric-ideals"
git = "https://github.com/FormalFrontier/toric-ideals.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the latest release when
this dependency is first added or updated; `lake-manifest.json` locks the resolved
commit until the next update. To pin a particular release, replace `main` with a
full commit from that history. Libraries used together must share a compatible
Mathlib revision and toolchain; see [build](#build) for this checkout's pinned
environment.

Import `ToricIdeals` for the re-exported public APIs, or import a leaf module
directly. For the vertex cotangent basis or standard quotient grading, import
`ToricIdeals.RationalNormalCurve.Cotangent` or
`ToricIdeals.RationalNormalCurve.GradedAlgebra` directly, respectively, as noted
in [Modules](#modules).
The following complete module is stored verbatim in
[`ToricIdealsTest/ReadmeKernel.lean`](ToricIdealsTest/ReadmeKernel.lean) and built
by the default test target:

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

The [API guide](docs/README.md) describes theorem usage and stored examples,
including the [Jacobson criterion and its root-import clients](docs/README.md#jacobson-hankel-quotients).
Those clients use both directions of the criterion; coefficient models include
nilpotents, zero divisors, zero rings, and a Noetherian non-Jacobson boundary.
For coordinate cancellation and the canonical localization map, see
[regular coordinates and localization](docs/README.md#regular-coordinates-and-localization).

## Build

Use the repository's `lean-toolchain` and pinned `lake-manifest.json`. Fetch the
matching precompiled mathlib cache before building:

```sh
lake exe cache get
lake build
```

The default build includes both `ToricIdeals` and all registered
`ToricIdealsTest` modules. For a focused check, use `lake build ToricIdeals`
or `lake build ToricIdealsTest` after fetching the same cache. See the
[mathematical API and examples](docs/README.md), the
[normalization guide](docs/FiberNormalization.md), and the
[selected-module reference](docs/API.md). The latter's
[input manifest](docs/api-manifest.json) describes its earlier, limited input
set, not all current declarations. Documentation ships as Markdown, without an
interactive dependency website.

## Conventions and limitations

The raw curve parametrization uses universe-polymorphic commutative semirings;
the Hankel ideal and quotient results use commutative rings. The
Hankel quotient always means `Source R n ⧸ hankelIdeal R n`. In degrees zero
and one its ideal is `⊥`, giving the full polynomial rings on `Fin 1` and
`Fin 2`. Only positive-degree results identify this quotient with the
parametrization image. Jacobsonness and Noetherianity each have their own
coefficient criterion; neither property is substituted for the other.
The ring criteria take scalars in the quotient itself: Noetherianity detects
`IsNoetherianRing R`, while Artinianity detects `Subsingleton R`. For the
canonical left coefficient action, finite generation, Noetherianity and
Artinianity each detect `Subsingleton R`, without a finite-rank or
positive-degree premise. Finiteness over the endpoint polynomial algebra has
different scalars and holds for every coefficient ring. The
[root-import clients](ToricIdealsTest/RootClient.lean) contrast zero coefficients
with finite nonreduced `ZMod 4` coefficients in every degree. See the
[guide](docs/README.md) for theorem usage and boundary examples.

## References and credits

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
2025 draft, Exercise 3.6.F) motivates the Hankel presentation, not the Jacobson
criterion. No source text or PDF is reproduced, and the citation implies
neither participation nor endorsement. The curve definitions, descent,
terminal-exponent uniqueness and normalization proofs are Formal Frontier
work. The Jacobson proof follows the constant-coefficient augmentation argument
of this library's Noetherian module and uses the Jacobson providers in
`Mathlib.RingTheory.Jacobson.Ring`. The left coefficient-module criteria use
this library's coordinate-axis surjection, the polynomial coefficient-module
criteria in [multivariate-polynomials](https://github.com/FormalFrontier/multivariate-polynomials),
and Mathlib's Noetherian and Artinian module theory. Coefficient-module
finiteness uses the same coordinate-axis surjection and directly reuses
Mathlib's `Polynomial.not_finite`, surjective-image finiteness and finiteness
of subsingleton modules. Raw-map surjectivity combines this library's
exponent-image divisibility criterion and coefficient-vanishing API with
Mathlib's `Finsupp.mapDomain_surjective`, monoid-algebra coefficient equivalence
and subsingleton-target surjectivity. Freeness over the raw source composes
this library's semiring injectivity criterion and degree-one map identity with
Mathlib's free-module faithfulness, faithful algebra-map injectivity, singleton
basis and empty basis APIs. Coefficient faithful flatness reuses the existing
coefficient augmentation and freeness, together with Mathlib's nontrivial
free-module result and transport from nonempty-index finitely supported
functions for zero coefficients. Its tensor clients directly reuse Mathlib's
faithfully-flat injectivity reflection and canonical unit injection. The
quotient-map flatness proof uses the origin derivative on a two-generated quotient ideal and a linear
coefficient functional on the target to exhibit the obstruction to flatness
of the quotient parametrization. That argument combines this library's
exponent-image criterion and coefficient-vanishing API with Mathlib's partial
derivations, additive quotient descent, tensor maps and flat-module
preservation of injections. The boundary degrees use the bijective quotient
projection and this library's raw-map flatness criterion. This flatness
classification is independent of the cited source motivation for the Hankel
presentation. The
augmentation-kernel description reuses the evaluation-ideal theorem in
multivariate-polynomials and Mathlib's ideal map/comap APIs; the coefficient
quotient clients instantiate Mathlib's first isomorphism theorem. Homogeneous-basis
coefficient change uses the library's characteristic representative laws and
Hankel kernel theorem, together with Mathlib's polynomial and quotient maps;
independent terminal choices are compared through their images. The Hankel
quotient dimension formula combines this library's endpoint map with the
injective-integral dimension theorem in
[minimal-primes](https://github.com/FormalFrontier/minimal-primes/blob/537058e2a3f4610d3126f22af057a1f6cd96c886/MinimalPrimes/RingTheory/KrullDimension/Integral.lean),
whose finite-chain proof uses incomparability, lying-over and going-up,
and Mathlib's Noetherian polynomial dimension formula. The code depends on
mathlib, multivariate-polynomials and minimal-primes (all Apache-2.0; see the
[complete minimal-primes license](https://github.com/FormalFrontier/minimal-primes/blob/537058e2a3f4610d3126f22af057a1f6cd96c886/LICENSE)).
Lean and doc-gen4 are separately credited tools, not bundled sources. The Markdown adapter follows earlier
Formal Frontier documentation tooling.
Contributions use AI-assisted development and independent agent review;
`Authors: Formal Frontier Agents` is collective author credit, not a
copyright-ownership claim.

Responsible maintainer: Almanac.
