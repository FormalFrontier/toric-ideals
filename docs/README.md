# Mathematical API and guides

## Raw parametrization injectivity

For every `(R : Type u) [CommSemiring R]` and `n : ℕ`,
[`rncMap_injective_iff`](../ToricIdeals/RationalNormalCurve/Injectivity.lean) says
`Function.Injective (rncMap R n) ↔ n = 1 ∨ Subsingleton R`. The source is the
full `MvPolynomial (Fin (n + 1)) R`, and the target is `MvPolynomial (Fin 2) R`.
The carriers, `rncMap_C`, `rncMap_X`, `rncMap_monomial` and
`rncMap_one_injective` are available over commutative semirings in the
[curve module](../ToricIdeals/RationalNormalCurve.lean); the root re-exports both modules.

At degree zero the sole variable maps to `1`, so raw injectivity fails for
nontrivial coefficients. Subsingleton coefficients give injectivity in every
degree. This is distinct from the Hankel quotient's domain criterion over
`[CommRing R]`: its degree-zero ideal is `⊥`, and the quotient remains the full
one-variable polynomial ring, not the parametrization image.

The private [`natural_conic_no_left_inverse` root-import client](../ToricIdealsTest/RootClient.lean)
uses the nonring semiring `ℕ` in degree two: no function `Target ℕ → Source ℕ 2`
can recover every source polynomial. A left inverse would give injectivity by
`Function.LeftInverse.injective`, contradicting the classifier. This rules out
arbitrary recovery functions, not just homomorphisms.

## Raw parametrization surjectivity

Import `ToricIdeals.RationalNormalCurve.MapSurjectivity`, or the root
`ToricIdeals`. The public theorem is in `ToricIdeals.RationalNormalCurve`:

```lean
theorem rncMap_surjective_iff (R : Type u) [CommSemiring R] (n : ℕ) :
    Function.Surjective (rncMap R n) ↔ n = 1 ∨ Subsingleton R
```

The source is the full `MvPolynomial (Fin (n + 1)) R`; the target is the full
`MvPolynomial (Fin 2) R`, not the image subsemiring or a finite collection of
monomials. The theorem includes degree zero and zero coefficients, in every
coefficient universe. It needs no ring, domain, Noetherianity, nontriviality or
positive-degree premise.

Use `(rncMap_surjective_iff R n).mpr` with a proof of `n = 1` or
`Subsingleton R` to obtain a preimage of any target polynomial. Use `.mp` to
recover that alternative from surjectivity. The private
[root-import clients](../ToricIdealsTest/Audit/RationalNormalCurveSurjectivityClient.lean)
apply `.mpr` to arbitrary full target polynomials over `ZMod 1` in every degree,
and `.mp` to exclude surjectivity over `ℕ` in degrees zero and two. The separate
[boundary models](../ToricIdealsTest/Audit/RationalNormalCurveSurjectivityModels.lean)
compute the constant image in degree zero, an interior conic monomial and a
missed target variable, including nonreduced coefficients and a lifted
coefficient universe. They use the polynomial and exponent APIs independently
of the classifier.

The degree-one proof composes `rncExponent_one` with Mathlib's
`Finsupp.mapDomain_surjective` and the monoid-algebra coefficient equivalence.
For the converse over nontrivial coefficients, the first target variable has
coefficient one at `Finsupp.single (0 : Fin 2) 1`. The characteristic API
`coeff_rncMap_of_not_mem_range R n p t ht` says that `(rncMap R n p).coeff t = 0`
when `t` is outside the exponent-map image. The coefficient-free,
all-degree `mem_mrange_rncExponent_iff` then forces `n ∣ 1`, hence `n = 1`.
For subsingleton coefficients, Mathlib's subsingleton-target surjectivity
applies directly.

At degree zero the raw map sends `X₀` to `1` and has constant image; this is
not the full degree-zero Hankel quotient `R[X₀]`. The injectivity classifier
has the same numerical criterion, but it is not used to prove surjectivity.
The quotient-to-image equivalence is likewise not an identification with the
full bivariate target.

## Raw parametrization flatness

Import `ToricIdeals.RationalNormalCurve.MapFlatness`, or the root
`ToricIdeals`. The public theorem is in `ToricIdeals.RationalNormalCurve`:

```lean
theorem rncMap_flat_iff (R : Type u) [CommRing R] (n : ℕ) :
    (rncMap R n).Flat ↔ n = 1 ∨ Subsingleton R
```

This is genuine commutative-ring morphism flatness in every coefficient
universe and every degree, including zero. Mathlib's `RingHom.Flat` equips
the full `Target R = MvPolynomial (Fin 2) R` with the module structure over
the full `Source R n = MvPolynomial (Fin (n + 1)) R` induced by
`(rncMap R n).toAlgebra`. Its action is `p • q = rncMap R n p * q`.
There is no domain, Noetherianity, nontriviality or positive-degree premise,
and no replacement of either carrier by a quotient, range or endpoint ring.

Use `(rncMap_flat_iff R n).mpr` with degree one or subsingleton coefficients
to obtain flatness of the ring map. Use `.mp` to recover that alternative
from flatness. The private
[root-import clients](../ToricIdealsTest/Audit/RationalNormalCurveFlatnessClient.lean)
apply `.mpr` over `ZMod 1` in every degree and `.mp` to exclude flatness
of the conic parametrization over `ZMod 4`. The latter ring has the nonzero
square-zero coefficient `2`, but its degree-one map is flat. Separate
[boundary models](../ToricIdealsTest/Audit/RationalNormalCurveFlatnessModels.lean)
check integer degrees zero through three, nilpotent coefficients, reduced
product coefficients with zero divisors, zero coefficients and a lifted
coefficient universe independently of the classifier.

The degree-one exponent identity identifies the polynomial map with the
identity, and a subsingleton target module is flat. For the converse,
`X₀ - 1` in degree zero and `X₁² - X₀ X₂` in degrees at least two are
regular source scalars with zero image. A variable-selection equivalence
makes each relation monic over a polynomial coefficient ring, so Mathlib's
monic regularity applies even when the original coefficients have zero
divisors. Vanishing of the quadratic relation reuses `minor_mem` and
`hankelIdeal_le_ker`. Mathlib's
`Module.Flat.isSMulRegular_of_isRegular` then forces this scalar to act
injectively on the full target, contradicting its annihilation of the unit
over nontrivial coefficients. This does not assume that flat ring maps
are injective in general.

This result is distinct from `quotient_free` and `quotient_flat`, which
concern the full Hankel quotient as a coefficient `R`-module in every degree.
At degree zero that quotient is `R[X₀]`, while the raw map sends `X₀` to
`1` and is not flat for nontrivial coefficients. The ring-map theorem does
not classify Mathlib's broader semiring `Module.Flat`, whose meaning is
preservation of tensor monomorphisms rather than genuine finite-limit
flatness over arbitrary semirings.

## Scalar base change of Hankel quotients

Import `ToricIdeals.RationalNormalCurve.BaseChange`, or the root `ToricIdeals`.
The public names are in `ToricIdeals.RationalNormalCurve`. For commutative rings
`R : Type u` and `S : Type v` with `[Algebra R S]`, write
$Q_{R,n}:=R[X_0,\ldots,X_n]/I_{R,n}$, where $I_{R,n}$ is
[`hankelIdeal R n`](../ToricIdeals/RationalNormalCurve.lean).
The equivalence
[`quotientBaseChangeAlgEquiv R S n`](../ToricIdeals/RationalNormalCurve/BaseChange.lean)
expresses scalar base change as

$$
S\otimes_R Q_{R,n}\simeq_S Q_{S,n}.
$$

This is an `S`-algebra equivalence for every `n : ℕ`, with independent universes
`u` and `v`. No flatness, injectivity, domain, Noetherianity, nontriviality or
positive-degree assumption is needed. Both sides use the full quotient by the
Hankel minors, not a replacement by the parametrization image. Since
`hankelIdeal R 0 = ⊥` and `hankelIdeal R 1 = ⊥`, degrees zero and one are the
usual base-change equivalences for the full polynomial rings `R[X₀]` and
`R[X₀, X₁]`.

For `s : S` and `p : Source R n`, the simp lemma
[`quotientBaseChangeAlgEquiv_tmul_mk`](../ToricIdeals/RationalNormalCurve/BaseChange.lean)
gives the representative formula

$$
s\otimes[p]\longmapsto
  [s\mathbin{\bullet}\operatorname{map}(\operatorname{algebraMap}_{R,S})(p)].
$$

Here `[p]` denotes the quotient class, `map` is
`MvPolynomial.map (algebraMap R S)`, and `s • q` is the canonical `S`-action
on polynomial coefficients, equivalently `MvPolynomial.C s * q`.
When starting from a ring homomorphism `f : R →+* S`, use the algebra
structure `f.toAlgebra`, so `algebraMap R S` is `f`, with its corresponding
canonical scalar actions throughout.

For a tower of commutative coefficient algebras `R → S → T` with
`[Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]`,
[`quotientBaseChangeAlgEquiv_tower`](../ToricIdeals/RationalNormalCurve/BaseChange.lean)
states that the square

$$
\begin{array}{ccc}
T\otimes_S(S\otimes_R Q_{R,n}) & \xrightarrow{\;1\otimes B_{R,S}\;} &
T\otimes_S Q_{S,n} \\
\downarrow\scriptstyle{\operatorname{cancelBaseChange}} &&
\downarrow\scriptstyle{B_{S,T}} \\
T\otimes_R Q_{R,n} & \xrightarrow{\;B_{R,T}\;} & Q_{T,n}
\end{array}
$$

commutes, where `B` is `quotientBaseChangeAlgEquiv`. The left arrow is
Mathlib's `Algebra.TensorProduct.cancelBaseChange`, which combines the tensor
associator with scalar-unit cancellation. The top arrow is
`Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
  (quotientBaseChangeAlgEquiv R S n)`.
On `t ⊗ (s ⊗ [p])`, both routes give
`[(algebraMap S T s * t) • MvPolynomial.map (algebraMap R T) p]`.
The coefficient universes `u`, `v`, `w` are independent, and the statement
includes every degree and zero rings without any flatness hypothesis.
No new quotient carrier or base-change map is needed.

The private [root-import client](../ToricIdealsTest/RootClient.lean) over
`ℤ → ZMod 4` in degree one sends `2 ⊗ [X₀ + X₁]` to the nonzero class
`[C 2 * (X₀ + X₁)]`, detected by evaluation at `(1, 0)`. Thus a nonzero
nilpotent scalar is included. The independent
[nonflat coefficient models](../ToricIdealsTest/RationalNormalCurveBaseChangeNonflatModels.lean)
show that this coefficient map is neither injective nor flat, and that its
conic quotient map kills the nonzero class `[C 4]` and sends `[C 2]` to a
nonzero square-zero class. Their tensor-tower client for
`ℤ → ZMod 4 → ZMod 2` uses the coherence theorem to compute both routes on
`1 ⊗ (3 ⊗ [1 + X₀])`, giving the nonzero class `[1 + X₀]` in every degree.
The surviving square-zero conic class `[C 2]` over `ZMod 4` becomes zero after
further tensor base change to `ZMod 2`. Nonflatness of `ℤ → ZMod 4` is proved
using Mathlib's regular-scalar criterion, not inferred merely from
noninjectivity. A zero-target tower also specializes a nonzero integer
constant to zero. These clients use the pure-tensor and augmentation lemmas,
without unfolding either construction. The
[small-degree, product and zero-ring models](../ToricIdealsTest/RationalNormalCurveBaseChangeSmallModels.lean)
use polynomial and quotient APIs independently of the base-change equivalence;
the [tensor models](../ToricIdealsTest/RationalNormalCurveBaseChangeTensorModels.lean)
compute the polynomial and tensor-quotient equivalences separately.
These clients and models are private examples, not additional public API.

## Finite coefficient modules of Hankel quotients

Import `ToricIdeals.RationalNormalCurve.CoefficientFiniteness`, or the root
`ToricIdeals`. The public theorem is in `ToricIdeals.RationalNormalCurve`:

```lean
theorem quotient_moduleFinite_iff (R : Type u) [CommRing R] (n : ℕ) :
    Module.Finite R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R
```

This concerns finite generation for the canonical coefficient `R`-module
action on the full Hankel quotient, in every degree and every coefficient
universe. At degree zero the ideal is `⊥`, so the quotient retains its
polynomial indeterminate rather than becoming the parametrization image.
No Noetherian, Artinian, domain, nontriviality or positive-degree premise is
needed. A nonzero finite coefficient ring, such as `ZMod 4`, still gives a
quotient that is not finite as a coefficient module.

Use `(quotient_moduleFinite_iff R n).mp` to recover `Subsingleton R` from
finite generation, and `.mpr` to obtain finite generation for zero
coefficients. The private
[criterion clients](../ToricIdealsTest/Audit/RationalNormalCurveCoefficientFinitenessClient.lean)
rule out finite generation over `ℤ` in degree zero and give finite modules
over `ZMod 1` in every degree. The separate
[polynomial models](../ToricIdealsTest/Audit/PolynomialCoefficientFinitenessModels.lean)
and [Hankel quotient models](../ToricIdealsTest/Audit/RationalNormalCurveCoefficientFinitenessModels.lean)
use only the polynomial and axis APIs. They include nonreduced coefficients,
a surviving square-zero constant, zero coefficients and a higher-universe
coefficient ring.

The proof uses the coefficient-linear surjection `axisProjection R n` onto
`Polynomial R`. A surjective image of a finite module is finite, contradicting
Mathlib's `Polynomial.not_finite` for nontrivial coefficients. For zero
coefficients, `Module.subsingleton` makes the quotient carrier subsingleton,
and Mathlib's finite-carrier module result applies.

The [endpoint theorem](../ToricIdeals/RationalNormalCurve/EndpointMap.lean)
`endpointMap_finite` instead uses `MvPolynomial (Fin 2) R` as scalars, and
holds for every commutative coefficient ring. Every quotient is also finite
as its canonical module over itself. Neither statement asserts coefficient
finiteness. The Noetherian and Artinian coefficient-module criteria are
separate chain conditions; this proof does not infer finite generation from
Noetherianity of the coefficient ring or quotient ring.

## Jacobson Hankel quotients

Import `ToricIdeals.RationalNormalCurve.Jacobson`, or the root `ToricIdeals`.
The module's public theorem is in `ToricIdeals.RationalNormalCurve`:

```lean
theorem quotient_isJacobsonRing_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsJacobsonRing (Source R n ⧸ hankelIdeal R n) ↔ IsJacobsonRing R
```

This is the theorem signature from the
[Jacobson criterion module](../ToricIdeals/RationalNormalCurve/Jacobson.lean#L43),
with arbitrary universe `u`. It concerns the full Hankel quotient ring itself,
not its coefficient-module structure or a substitute parametrization quotient.
The zero ring is included. At `n = 0` and `n = 1`, respectively, the source is
`MvPolynomial (Fin 1) R` and `MvPolynomial (Fin 2) R`, and the Hankel ideal is
`⊥`. No Noetherian, domain, field, reducedness, nontriviality or positive-degree
assumption is needed.

Use `(quotient_isJacobsonRing_iff R n).mpr` with a proof of `IsJacobsonRing R`;
use `.mp` to recover that property from the quotient. The
[root-import clients](../ToricIdealsTest/RationalNormalCurveJacobsonClient.lean)
import `Mathlib.Algebra.Field.Rat` alongside `ToricIdeals`.
`rational_quotient_isJacobsonRing` applies
`(quotient_isJacobsonRing_iff ℚ n).mpr inferInstance` in every degree.
`radical_eq_jacobson_of_quotient_isJacobsonRing` assumes only a Jacobson
instance on the quotient, uses `.mp` to obtain one on `R`, and then applies
`Ideal.radical_eq_jacobson I` to each coefficient ideal. These declarations
are private tests, not part of the public API.

The proof descends constant-coefficient evaluation to the quotient: every
minor evaluates to zero, and the class of `MvPolynomial.C r` maps to `r`,
making the map surjective. Mathlib's Jacobson descent gives the coefficient
property. Conversely, the finite-variable polynomial ring over Jacobson
coefficients is Jacobson, as is its quotient. The augmentation argument follows
the library's [Noetherian criterion](../ToricIdeals/RationalNormalCurve/Noetherian.lean).
The generic Jacobson providers come from `Mathlib.RingTheory.Jacobson.Ring`.

The [coefficient models](../ToricIdealsTest/RationalNormalCurveJacobsonModels.lean)
include zero rings, the rational field, the finite nonreduced ring `ZMod 4`,
and the product `ℚ × ℚ`. The last two have, respectively, a surviving nonzero
square-zero constant and nonzero orthogonal constant classes. Their quotients
are Jacobson without being Artinian over themselves. The
[power-series models](../ToricIdealsTest/RationalNormalCurveJacobsonModels/PowerSeries.lean)
show that `PowerSeries ℚ` and all its Hankel quotients are Noetherian but not
Jacobson. Thus Noetherianity alone does not imply the Jacobson property.

## Regular coordinates and localization

Import `ToricIdeals.RationalNormalCurve.CoordinateRegularity`, or the root
`ToricIdeals`. The public theorem is in `ToricIdeals.RationalNormalCurve`:

```lean
theorem isRegular_quotient_X (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    _root_.IsRegular
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n))
```

This is the signature from the
[coordinate-regularity module](../ToricIdeals/RationalNormalCurve/CoordinateRegularity.lean#L59).
It applies in every degree to every coordinate over any commutative coefficient
ring, including rings with zero divisors or nilpotents and the zero ring.
The root `IsRegular` means that multiplication by this class is injective
on both sides; it is element regularity, not a regular-sequence assertion.
No domain, reducedness, Noetherianity, nontriviality or positive-degree
hypothesis is needed. At degree zero the quotient is the full one-variable
polynomial ring by `⊥`, not the parametrization kernel or image; at degree
one it is the full two-variable polynomial ring.

A standalone root-import use of the public theorem is:

```lean
module

import ToricIdeals

open ToricIdeals.RationalNormalCurve

universe u

example (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    _root_.IsRegular
      (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n)) :=
  isRegular_quotient_X R n i
```

Use `(isRegular_quotient_X R n i).left` to cancel the coordinate class on the
left and `.right` to cancel it on the right. The first and last coordinates
are `i = 0` and `i = Fin.last n`; they coincide at degree zero. The independent
[coefficient and boundary models](../ToricIdealsTest/RationalNormalCurveCoordinateRegularityModels.lean)
use only the existing Hankel presentation and generic polynomial and quotient
APIs. They cover the zero ring in every degree, full degree-zero and degree-one
quotients, nonreduced `ZMod 4` coefficients, a nonzero square-zero constant,
orthogonal product constants, and nonzero integer coordinate classes,
including the interior coordinate in degree two.

The stored [coordinate-localization client](../ToricIdealsTest/RationalNormalCurveCoordinateLocalization.lean#L45)
imports the producer directly and provides this public theorem in the same
namespace:

```lean
theorem injective_algebraMap_away_quotient_X (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    Function.Injective
      (algebraMap (Source R n ⧸ hankelIdeal R n)
        (Localization.Away
          (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i : Source R n))))
```

This is the canonical map from the same Hankel quotient to its localization
away from the same coordinate class, with the same hypotheses. Inverting the
coordinate does not identify distinct quotient elements. To use this client
by name, import `ToricIdealsTest.RationalNormalCurveCoordinateLocalization`;
it is a test-root theorem, not re-exported by the library root `ToricIdeals`.
These results assert injectivity, not a Laurent-chart formula, rank, flatness
or dimension calculation.

## Mathematical API

The declarations listed in this section are public. The generic theorem is in
namespace `ToricIdeals`; the curve names are in `ToricIdeals.RationalNormalCurve`, and the split-quadric
names are in `ToricIdeals.SplitQuadric`. All leaf modules are also re-exported
by `ToricIdeals`.

- **Generic fibers:** `AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero` says that
  if, for *every* source exponent `m` and coefficient `r`, its basis term is
  congruent modulo `I` to the term at `normal (exponentMap m)`, then anything
  mapped to zero by `AddMonoidAlgebra.mapDomain exponentMap` lies in `I`.
  It works over any `[Ring R]` with `[AddMonoid M]`, a bare target type `N`, and
  `exponentMap : M → N`, in independent universes. `normal` is arbitrary, not
  necessarily a preimage selector; no injectivity or finiteness is assumed.
  With `[AddMonoid N]` and `exponentMap : M →+ N`, `ker_mapDomainRingHom_le`
  packages kernel containment. `ideal_eq_ker_mapDomainRingHom` and
  `mem_ideal_iff_mapDomain_eq_zero` additionally require `I ≤ RingHom.ker` of
  the existing induced ring map. See [normalization and its kernel API](FiberNormalization.md).
- **Parametrization and generators:** `Source`, `Target`,
  `coordinateExponent`, `rncExponent`, `rncMap`, `MinorIndex`, `hankelMinor`,
  `hankelIdeal` give the `n+1` source variables, two target variables, the map
  `xᵢ ↦ a^(n-i)b^i`, ordered column pairs `i < j` in the `2 × n` Hankel matrix,
  and the ideal generated by its `2 × 2` minors. `rncExponent_single`,
  `rncMap_X`, `minor_exponents_agree`, `minor_mem`, `hankelIdeal_le_ker` give
  basis images, the generating relation and the inclusion valid for *all* `n`.
- **Small degrees:** `hankelIdeal_zero`, `hankelIdeal_one` show that both
  minor ideals are zero. `hankelIdeal_zero_lt_ker` needs `[Nontrivial k]`:
  at `n = 0` the sole variable maps to `1`, so the inclusion is strict.
  For `[Subsingleton k]`, the stored root-import client instead proves equality
  by subsingleton elimination. At `n = 1`, `rncExponent_one`,
  `rncMap_one_injective`, `hankelIdeal_one_eq_ker` give an injective map and
  equality without an extra hypothesis on `k`.
- **Raw-map flatness:** For `(R : Type u) [CommRing R]` and every
  `n : ℕ`, `rncMap_flat_iff R n` states
  `(rncMap R n).Flat ↔ n = 1 ∨ Subsingleton R` for the full target over
  the full source through this map; see the
  [criterion and scalar distinction](#raw-parametrization-flatness).
- **Decreasing reduction:** `sourceDegree`, `sourceWeight`, `sourceEnergy`,
  `outerExponent`, `innerExponent`, `reduceExponent` describe a move from a
  separated occupied pair toward adjacent positions. `monomial_add_one`,
  `monomial_outer_sub_inner`, `rncExponent_outer_eq_inner`,
  `inner_energy_lt_outer_energy`, `reduceExponent_preserves_rncExponent`,
  `reduceExponent_energy_lt`, `monomial_sub_reduceExponent_mem` establish that
  each applicable move preserves the target exponent, strictly decreases a
  natural-number energy and changes the monomial only modulo `hankelIdeal`.
- **Terminal exponents:** `Normal` forbids applicable separated pairs.
  `Normal.index_le_add_one`, `Normal.mem_support_eq_or_val_eq_add_one`,
  `Normal.degree_weight_eq_min_add_succ`,
  `Normal.eq_single_add_single_succ`, `Normal.eq_single_of_min_eq_last`,
  `Normal.min_val_eq_weight_div_degree`, `Normal.eq_of_degree_weight_eq`
  establish adjacent support and uniqueness from degree and weighted index.
  `exists_normal` obtains a terminal representative by energy induction.
- **Target invariants and choices:** `rncExponent_second`, `rncExponent_total`
  identify the second target exponent with source weight and the sum of the
  two target exponents with `n * sourceDegree`. Hence
  `rncExponent_injective_on_normal` recovers the degree for `1 ≤ n` and proves
  injectivity *on terminal exponents*, not on all source exponents.
  `normalSourceExponent`, `normalSourceExponent_normal`,
  `normalSourceExponent_rncExponent`,
  `monomial_sub_normalSourceExponent_mem`,
  `normalSourceExponent_eq_of_rncExponent_eq`, `fiberNormalExponent`,
  `fiberNormalExponent_image` select congruent terminal/fiber representatives.
  These selections use classical noncomputable choice (including a coefficient
  ring parameter); they are not an executable or universally canonical normal
  form. By definition `fiberNormalExponent` returns zero outside the image.
- **Primality and quotient domains:** For `(R : Type u) [CommRing R]` and
  every `n : ℕ`, `hankelIdeal_isPrime_iff` states
  `(hankelIdeal R n).IsPrime ↔ IsDomain R`, and `quotient_isDomain_iff` states
  `IsDomain (Source R n ⧸ hankelIdeal R n) ↔ IsDomain R`.
  There is no additional nontriviality, domain, field, cancellation or
  positive-degree hypothesis. At `n = 0`, `hankelIdeal_zero` gives the zero
  ideal and the quotient is a one-variable polynomial ring. Over a coefficient
  domain this ideal is prime and the quotient is a domain, while
  `hankelIdeal_zero_lt_ker` still gives strict containment in the parametrization
  kernel for `[Nontrivial R]`. These criteria concern the Hankel quotient,
  not a replacement by the parametrization kernel or range. For the zero
  coefficient ring, both primality and the domain property fail.
- **Positive-degree kernel, quotient image and geometry:** `ker_le_hankelIdeal`
  and `hankelIdeal_eq_ker` give the reverse inclusion and equality for `1 ≤ n`
  over any `[CommRing k]`. With that same positive-degree premise,
  `quotientEquivRange` identifies `Source k n ⧸ hankelIdeal k n` with the
  **image subring** `(rncMap k n).range`, not all of `Target k`. In general its
  dependent transport does not provide an `rfl`/`simp` evaluation on arbitrary
  quotient representatives; the unit evaluation in the stored client uses
  `map_one`. With `[IsDomain k]` and `1 ≤ n`, `hankelIdeal_isPrime`,
  `quotient_isDomain`, `spectrum_irreducible` give the prime, quotient-domain
  and topological consequences. No algebraic-closedness, characteristic,
  smoothness, scheme-isomorphism or general toric-ideal classification is asserted.
- **Reducedness and radicality:** For `(R : Type u) [CommRing R]` and all
  `n : ℕ`, `quotient_isReduced_iff R n` gives
  `IsReduced (Source R n ⧸ hankelIdeal R n) ↔ IsReduced R`, and
  `hankelIdeal_isRadical_iff R n` gives
  `(hankelIdeal R n).IsRadical ↔ IsReduced R`. At `n = 0`, `hankelIdeal_zero`
  makes this the **one-variable polynomial quotient by `⊥`**, not a replacement
  by the parametrization kernel or image. Reduced rings with zero divisors are
  included. The zero ring is reduced and its Hankel ideal is radical even
  though it equals `⊤` and is neither proper nor prime; its quotient is not a
  domain. These are characterizations, not assertions of a nonempty or
  irreducible spectrum.
- **Homogeneity:** For `(R : Type u) [CommRing R]` and all `n : ℕ`,
  `hankelIdeal_isHomogeneous R n` states
  `Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  (hankelIdeal R n)`. The canonical grading is selected with
  `attribute [local instance] MvPolynomial.gradedAlgebra`; no new global
  instance is introduced. At `n = 0` the source is the full one-variable
  polynomial ring with ideal `⊥`, not the parametrization kernel or image;
  at `n = 1` it is a two-variable polynomial ring with ideal `⊥`.
  The theorem includes the zero coefficient ring and rings with zero divisors
  or nilpotents. A minor's homogeneous degree label `2` does not assert total
  degree `2` when the polynomial is zero.
- **Noetherianity:** For `(R : Type u) [CommRing R]` and every `n : ℕ`,
  `quotient_isNoetherianRing_iff R n` states
  `IsNoetherianRing (Source R n ⧸ hankelIdeal R n) ↔ IsNoetherianRing R`.
  At degree zero this is the full one-variable polynomial quotient by `⊥`,
  not the parametrization kernel or image. The zero coefficient ring is
  included, as are Noetherian rings with zero divisors or nilpotents.
- **Coefficient-module finiteness:** For `(R : Type u) [CommRing R]` and
  every `n : ℕ`, `quotient_moduleFinite_iff R n` states
  `Module.Finite R (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R` for the
  canonical coefficient action; see the
  [criterion and scalar contrast](#finite-coefficient-modules-of-hankel-quotients).
- **Jacobsonness:** `quotient_isJacobsonRing_iff R n` characterizes the
  full quotient in every degree by `IsJacobsonRing R`; see the
  [criterion, proof and coefficient examples](#jacobson-hankel-quotients).
- **Artinianity:** For `(R : Type u) [CommRing R]` and every `n : ℕ`,
  `quotient_isArtinianRing_iff R n` states
  `IsArtinianRing (Source R n ⧸ hankelIdeal R n) ↔ Subsingleton R`.
  Artinianity means the quotient is Artinian as a module over itself, not
  over `R`. At degrees zero and one the quotients are the full one-variable
  and two-variable polynomial presentations. Every nonzero coefficient ring
  gives a non-Artinian quotient, even when it is finite, Artinian or nonreduced.
- **Coordinate cancellation:** `isRegular_quotient_X R n i` is root
  `IsRegular` of `Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)`.
  Its `.left` and `.right` fields provide the two multiplication injections
  for every coordinate, with no extra ring or degree hypothesis; see
  [regular coordinates and localization](#regular-coordinates-and-localization).
- **Split-quadric reduction:** `exponentMap` maps `Fin 4 →₀ ℕ` additively to
  `Fin 3 →₀ ℕ` with coordinates `E(a, b, c, d) = (a+b, c+d, b+d)`.
  `reduce` replaces
  `k = min(a, d)` copies of `wz` by `xy`, giving
  `(a-k, b+k, c+k, d-k)`. `Reduced` and `reduced_iff` characterize the
  condition `a = 0 ∨ d = 0`. Coordinate laws evaluate the map, reduction and
  selector; single-exponent laws give the map's basis images, without unfolding
  the definitions.
  `exponentMap_reduce` preserves the image, and `reduce_reduced` proves
  reducedness. `reduce_eq_self_iff` characterizes fixed points;
  `reduce_reduce` gives idempotence; `reduce_eq_reduce_iff` says that two
  reductions agree exactly when the images agree.
  `eq_of_reduced_of_exponentMap_eq` gives uniqueness among reduced exponents.
- **Split-quadric selector and image cone:** For `(u, v, t)`, `normal` uses
  `b = min(u, t)` and `d = t-b` to return `(u-b, b, v-d, d)`, with natural
  subtraction truncating at zero. `normal_reduced` holds for every target.
  `exponentMap_normal` gives a preimage under the material hypothesis
  `t ≤ u+v`, while `normal_exponentMap` agrees with reduction for every source.
  `mem_mrange_iff` characterizes `AddMonoidHom.mrange exponentMap` by that
  inequality, and `existsUnique_reduced_preimage_iff` gives the same criterion
  for existence of a unique reduced preimage. No coefficient-ring or domain
  hypothesis is involved. Neither `normal` nor `reduce` is additive, and
  reduced exponents are not closed under ordinary addition.

## Examples and theorem usage

`ToricIdealsTest.RootClient` stores further independent-universe generic,
low-degree, quotient/range and domain/spectrum examples using just the root import;
`ToricIdealsTest.Audit` stores named boundary clients.
The coefficient-ring examples in
[`ToricIdealsTest.RationalNormalCurveDomainModels`](../ToricIdealsTest/RationalNormalCurveDomainModels.lean)
use namespace `ToricIdeals.RationalNormalCurve.DomainModels`. Their integer
bundles give prime ideals and domain quotients in degrees zero, one and two;
the degree-zero quotient retains a nonzero class of `X₀ - 1` even though
`X₀ ↦ 1`. In degree two over `ℤ × ℤ`, the Hankel ideal is proper but not prime,
and its quotient is not a domain: the nonzero orthogonal coefficients `(1, 0)`
and `(0, 1)` survive as nonzero constant classes with zero product. For the zero
coefficient ring `ZMod 1`, the degree-zero and degree-two quotients have `1 = 0`;
the ideals are not prime and the quotients are not domains.
These are stored tests, not extra library declarations. Leaf-module users can
import `ToricIdeals.MonoidAlgebra.FiberNormalization`,
`ToricIdeals.RationalNormalCurve` or `ToricIdeals.SplitQuadric.Exponents`
directly. Keep `1 ≤ n` for the positive-degree kernel and quotient/range
results; the positive-degree domain/spectrum corollaries also require
`[IsDomain k]`. The two primality/domain `_iff` criteria apply to every `n`
over `[CommRing R]` alone.

The [stored split-quadric models](../ToricIdealsTest/SplitQuadricModels.lean)
include clients of `ToricIdeals.SplitQuadric` alongside a private independent
model. They reduce `(5, 2, 3, 7)` to `(0, 7, 8, 2)`, preserving the image
`(7, 10, 9)`, and use the general laws to establish reducedness, fixed points,
fiber equality and unique reduced preimages. The distinct exponents of `wz`
and `xy` both map to `(1, 1, 1)` and reduce to the exponent of `xy`.
Outside the cone, `normal (0, 0, 1) = (0, 0, 0, 1)` has image `(0, 1, 1)`,
not `(0, 0, 1)`; that target has no preimage. The models also demonstrate
nonadditivity of the selector even on the cone, and reduced summands whose
sum is not reduced.

For reducedness and radicality, use `(quotient_isReduced_iff R n).mpr` and
`(hankelIdeal_isRadical_iff R n).mpr` with a proof of `IsReduced R`;
`.mp` recovers coefficient reducedness from either conclusion. No positive-degree
or domain hypothesis is needed. The stored
[reducedness models](../ToricIdealsTest/RationalNormalCurveReducedModels.lean)
use both characterizations with concrete witnesses:

- `integer_degree_zero_reduced_radical_with_strict_kernel`: over `ℤ` at degree
  zero, the quotient is reduced and the ideal radical; the classes of `X₀` and
  `X₀ - 1` are nonzero, and the Hankel ideal is strictly below the parametrization
  kernel.
- `integer_product_reduced_radical_orthogonal_classes`: over `ℤ × ℤ` at degrees
  zero and two, the nonzero orthogonal idempotents `(1, 0)` and `(0, 1)` survive
  as constant classes. The quotients are reduced but not domains, and the ideals
  are radical.
- `two_mod_four_nonreduced_nonradical_square_zero`: over `ZMod 4` at degrees
  zero and two, the class of `C 2` is nonzero with square zero. The quotients are
  nonreduced and the ideals are not radical.
- `zero_coefficients_reduced_radical_unit_zero`: over `ZMod 1` at degrees zero
  and two, the quotient units equal zero. The quotients are reduced but not
  domains, and the ideals are radical.

For Noetherianity, import `ToricIdeals.RationalNormalCurve.Noetherian` or the
root module. Apply `(quotient_isNoetherianRing_iff R n).mpr` to a proof of
`IsNoetherianRing R`; `.mp` recovers coefficient Noetherianity. The stored
[positive models](../ToricIdealsTest/RationalNormalCurveNoetherianModels.lean)
use both directions over arbitrary commutative rings and specialize the
criterion to `ZMod 4`, `ZMod 1` and `ℤ × ℤ`. The
[negative models](../ToricIdealsTest/RationalNormalCurveNoetherianNegativeModels.lean)
show that `ℕ → ZMod 2` is not Noetherian using a strictly ascending chain of
coordinate-unit ideals, and hence that its Hankel quotient is non-Noetherian
in every degree, including zero.

For Artinianity, import `ToricIdeals.RationalNormalCurve.Artinian` or the
root module. The forward direction `.mp` recovers `Subsingleton R`; `.mpr`
gives Artinianity for zero coefficients. The stored root-import clients in
[`ToricIdealsTest.Audit`](../ToricIdealsTest/Audit.lean) apply the criterion to
`ZMod 1` and `ZMod 4` in every degree. The independent
[Artinian models](../ToricIdealsTest/RationalNormalCurveArtinianModels.lean)
cover integers, nilpotent and product coefficients, full small-degree
polynomial quotients and the conic relation using the Hankel presentation.

For homogeneity, import `ToricIdeals.RationalNormalCurve.Homogeneous` or the
root module and select Mathlib's canonical source grading locally:

```lean
attribute [local instance] MvPolynomial.gradedAlgebra
```

Given `hf : f ∈ hankelIdeal R n`, use
`MvPolynomial.homogeneousComponent_mem_of_mem (hankelIdeal_isHomogeneous R n) hf d`
to obtain membership of the degree-`d` component. The theorem
`MvPolynomial.mem_iff_homogeneousComponent_mem (hankelIdeal_isHomogeneous R n) f`
gives the componentwise membership criterion. The stored
[homogeneity clients](../ToricIdealsTest/RationalNormalCurveHomogeneityClient.lean)
apply both primitives to `g + X₀*g`, where `g = X₀X₂ - X₁²`, over arbitrary
commutative rings. Over `ℤ` its quadratic component is the nonzero minor `g`
and belongs to the ideal. The independent
[coefficient models](../ToricIdealsTest/RationalNormalCurveHomogeneityModels.lean)
also cover the small-degree boundaries, characteristic two, nilpotent and
product coefficients, and the zero coefficient ring. These concern the
standard source grading, not a constructed quotient grading.

## Selected-module API reference

[`FiberNormalization.md`](FiberNormalization.md) describes the **current** general
ring/arbitrary-function normalization contract and its kernel criteria. See the
[mathematical overview](../README.md) for the library's scope.

[`API.md`](API.md) covers 58 public declarations from the earlier
commutative normalization specialization and the curve module, together with
the root import and three private example modules. Its source revision is
`74622e47c5bd8b98c1bc72a5bf2a768805fa52ed`. It retains displayed
signatures (including implicit arguments, abbreviations and noncomputable
modifiers) and the original project docstrings. In particular, it displays the
commutative normalization specialization, not the current general contract or its
kernel criteria. Its source-line anchors refer to that earlier input layout and
need not identify the corresponding declaration lines in this checkout. This
selected-module reference is not a complete signature index or exact-input
manifest for the current checkout, and it does not include the Jacobson module. No
JavaScript, fonts, remote styles, source PDF, external documentation text or
interactive dependency website is shipped.

## Reproducing the selected-module reference

The nine exact Lean/configuration input hashes and six doc-gen4 record
hashes, 58-name inventory, analyzed revision and original generated-output SHA256
are in the **unchanged** [`api-manifest.json`](api-manifest.json);
`proof_certification: false`. Its output hash applies to the **original generated
API bytes**: 28,197 bytes, SHA256
`141e10522619aa70ce502261ac40bce834953e35fe37902b452108cfacebb065`.
The opening of `API.md` is a selected-module scope annotation; every byte
from its first `## Module` heading onward is the original extraction. The annotated
file does **not** match that original output hash, and the manifest does not bind
this checkout's current generalized sources.

The `frozenSource` input binding, displayed signatures and source
anchors belong to the original inputs in prior official release
`852dc998e56222e6c9fbba565e07cb9307614fd6`, not to the current normalization API.
For exact-input reproduction, use a **separate checkout of that original release**,
not this checkout:

```sh
git clone https://github.com/FormalFrontier/toric-ideals.git /path/to/toric-api-original
cd /path/to/toric-api-original
git checkout --detach 852dc998e56222e6c9fbba565e07cb9307614fd6
```

Run the commands below in that separate checkout. Do not run the fixed-list
generator with current inputs or rehash them into the old manifest. For the specified input
layout, header-only normalization leaves the displayed signatures, docstrings and
source-line anchors unchanged; it does not provide a new extraction or
describe the current general-ring/arbitrary-function API. Changes to their content
or locations are outside this reference.

At that exact original-release checkout, when the specified source commit is
present, its Git objects must match every source input. When that object is
absent in a parentless checkout, the freshly reproduced manifest must instead
equal that original checkout's committed manifest byte-for-byte: all nine
source/configuration hashes, six doc-gen4 record
hashes, module/public inventories, tool revision and output hash. Every input must
also equal that release's own committed file. Present wrong objects, stale inputs,
altered doc-gen4 records and uncommitted manifests are refused. This binds inspected
inputs and output, not provenance or tool execution; it does not promise the
source revision is available at GitHub.

Build doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its
committed dependency manifest and Lean `v4.34.0-rc2` in a separate checkout using
`lake build doc-gen4`. This core-only tool must not change this library's pins.
In the **original-release checkout**, fetch its matching mathlib cache, then build
all six modules as in that release's root README. Use fresh analysis/render
directories and a full immutable analyzed revision, not a moving branch. Repeat
`single` for each module in `scripts/generate_api.py`, with its corresponding source
path. Create the output directories first: the SQLite opener does not
create them.

```sh
mkdir /tmp/toric-analysis /tmp/toric-render
lake env /path/to/doc-gen4 single --build /tmp/toric-analysis ToricIdeals.MonoidAlgebra.FiberNormalization api.db https://github.com/FormalFrontier/toric-ideals/blob/FULL_SOURCE_COMMIT/ToricIdeals/MonoidAlgebra/FiberNormalization.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/toric-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/toric-render --manifest /tmp/toric-render/manifest.json /tmp/toric-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/toric-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/toric-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

Only the Markdown reference and manifest are distributed, not intermediate HTML,
assets or dependency pages. Doc-gen4 source URIs identify the analyzed revision;
the Markdown's checkout-relative source links and anchors refer to the specified
source layout, not necessarily this checkout.

## Technical checks and attribution

The fixed-list adapter requires six module records and exactly
the expected 58 names, declaration kinds and origins. Doc-gen4 metadata calls abbreviations
`def`; their displayed signatures retain `abbrev`. The exact display inventory is
four abbreviations, 13 noncomputable definitions, the predicate `Normal` and 40
theorems. Every header text token is retained, normalizing whitespace only. Module
documentation comes from the exact simple single module-comment block in each
specified source. Missing docstrings, malformed markup, unsafe/partial/incorrect
kinds, source/pin drift and invalid links are refused. The adapter is not a Lean
parser, tool-output authenticator or proof checker.

The bounded renderer follows earlier Formal Frontier documentation adapters.
Collective credit and Apache-2.0 terms are preserved. The original library's
signatures and docstrings retain their attribution; Lean, mathlib and doc-gen4
are separately credited tools/dependencies, not copied documentation.
