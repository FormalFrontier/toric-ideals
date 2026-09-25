# Generated API reference

Complete public API of toric-ideals: 58 declarations in two mathematical leaves.
Import `ToricIdeals` for both leaves. Three test modules contain private checked
clients and README examples, not additional public API.

Signatures below are native doc-gen4 display signatures with all displayed implicit
arguments retained, not declarations with proof bodies. Short names use the source
namespace and imports; universe parameters are arbitrary. Module documentation
is extracted verbatim from the exact source. All source links are relative to this
checkout. See [generation and provenance](README.md), [exact input manifest](api-manifest.json)
and the [mathematical overview](../README.md).

## Module `ToricIdeals.MonoidAlgebra.FiberNormalization`

> # Fiberwise normalization for additive monoid algebras
>
> This file packages the coefficient-collision step common to elementary proofs
> of monomial-map kernels.  If every basis monomial is congruent modulo an ideal
> to a representative selected solely from its target exponent, then every
> element killed by the induced monomial map belongs to that ideal. The proof
> expresses the difference from the normalized sum as a finite sum of assumed
> ideal members; `mapDomain` sends the normalized sum to zero when the original
> sum maps to zero. This does not need `normal` to be additive or a right inverse.

[Module source](../ToricIdeals/MonoidAlgebra/FiberNormalization.lean)

### ToricIdeals.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero

```lean
theorem ToricIdeals.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommMonoid M] [AddCommMonoid N] (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N) (normal : N → M) (basis_sub_normal_mem : ∀ (m : M) (r : R), AddMonoidAlgebra.single m r - AddMonoidAlgebra.single (normal (exponentMap m)) r ∈ I) {f : AddMonoidAlgebra R M} (hf : AddMonoidAlgebra.mapDomain (⇑exponentMap) f = 0) : f ∈ I
```

A coefficientwise fiber-normalization principle for monomial maps.

For a commutative coefficient ring `R` and additive commutative exponent monoids
`M`, `N` in independent universes, the function `normal : N → M` need not
preserve addition or select a preimage of every target exponent. The input is
the displayed congruence for every source exponent and *every coefficient*.
The conclusion is kernel membership, not injectivity or finite generation.

[Source](../ToricIdeals/MonoidAlgebra/FiberNormalization.lean#L34) (line 34).

## Module `ToricIdeals.RationalNormalCurve`

> # The toric ideal of a rational normal curve
>
> For `n ≥ 1`, this file identifies the ideal of `2 × 2` minors of the
> Hankel matrix with rows `x₀, …, xₙ₋₁` and `x₁, …, xₙ` with the
> kernel of `xᵢ ↦ a^(n-i) b^i`, over an arbitrary commutative ring.
>
> The easy inclusion follows by evaluating each generator. For the reverse
> inclusion, a Hankel relation moves an occupied separated pair inward, preserves
> the target exponent, and strictly decreases natural-number energy. Repeating
> this move yields adjacent support; degree and weight determine the terminal
> exponent. Positive `n` lets the target exponents recover source degree, so
> terminal representatives can be selected by target fiber. The generic
> coefficientwise normalization theorem then handles arbitrary coefficients.
> These representatives use classical choice, not a computable reduction API.
>
> The degree-zero exception, degree-one equality, quotient-to-*range* equivalence,
> and domain-dependent consequences are stated separately below.

[Module source](../ToricIdeals/RationalNormalCurve.lean)

### ToricIdeals.RationalNormalCurve.Source

```lean
abbrev ToricIdeals.RationalNormalCurve.Source (k : Type u) [CommRing k] (n : ℕ) : Type u
```

The polynomial ring in `x₀, …, xₙ`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L44) (line 44).

### ToricIdeals.RationalNormalCurve.Target

```lean
abbrev ToricIdeals.RationalNormalCurve.Target (k : Type u) [CommRing k] : Type u
```

The polynomial ring in the two target variables `a` and `b`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L47) (line 47).

### ToricIdeals.RationalNormalCurve.coordinateExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.coordinateExponent (n : ℕ) (i : Fin (n + 1)) : Fin 2 →₀ ℕ
```

The exponent pair `(n-i, i)` of the image of `xᵢ`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L50) (line 50).

### ToricIdeals.RationalNormalCurve.rncExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.rncExponent (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ Fin 2 →₀ ℕ
```

The additive exponent map induced by `xᵢ ↦ a^(n-i) b^i`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L55) (line 55).

### ToricIdeals.RationalNormalCurve.rncMap

```lean
noncomputable def ToricIdeals.RationalNormalCurve.rncMap (k : Type u) [CommRing k] (n : ℕ) : Source k n →+* Target k
```

The monomial parametrization `xᵢ ↦ a^(n-i) b^i`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L59) (line 59).

### ToricIdeals.RationalNormalCurve.MinorIndex

```lean
abbrev ToricIdeals.RationalNormalCurve.MinorIndex (n : ℕ) : Type
```

Ordered pairs of distinct columns of the `2 × n` Hankel matrix.

[Source](../ToricIdeals/RationalNormalCurve.lean#L63) (line 63).

### ToricIdeals.RationalNormalCurve.hankelMinor

```lean
noncomputable def ToricIdeals.RationalNormalCurve.hankelMinor (k : Type u) [CommRing k] (n : ℕ) (p : MinorIndex n) : Source k n
```

The minor `x_i*x_(j+1) - x_(i+1)*x_j` for columns `i < j`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L66) (line 66).

### ToricIdeals.RationalNormalCurve.hankelIdeal

```lean
noncomputable def ToricIdeals.RationalNormalCurve.hankelIdeal (k : Type u) [CommRing k] (n : ℕ) : Ideal (Source k n)
```

The ideal generated by all `2 × 2` minors of the Hankel matrix.

[Source](../ToricIdeals/RationalNormalCurve.lean#L70) (line 70).

### ToricIdeals.RationalNormalCurve.rncExponent_single

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_single (n : ℕ) (i : Fin (n + 1)) : (rncExponent n) (Finsupp.single i 1) = coordinateExponent n i
```

A source variable has exactly its designated target exponent.

[Source](../ToricIdeals/RationalNormalCurve.lean#L74) (line 74).

### ToricIdeals.RationalNormalCurve.rncMap_X

```lean
theorem ToricIdeals.RationalNormalCurve.rncMap_X (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n + 1)) : (rncMap k n) (MvPolynomial.X i) = (MvPolynomial.monomial (coordinateExponent n i)) 1
```

The parametrization takes `X i` to the monomial of exponent `(n-i,i)`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L80) (line 80).

### ToricIdeals.RationalNormalCurve.minor_exponents_agree

```lean
theorem ToricIdeals.RationalNormalCurve.minor_exponents_agree (n : ℕ) (p : MinorIndex n) : coordinateExponent n (↑p).1.castSucc + coordinateExponent n (↑p).2.succ = coordinateExponent n (↑p).1.succ + coordinateExponent n (↑p).2.castSucc
```

The two products in an ordered Hankel minor have equal target exponents.

[Source](../ToricIdeals/RationalNormalCurve.lean#L89) (line 89).

### ToricIdeals.RationalNormalCurve.minor_mem

```lean
theorem ToricIdeals.RationalNormalCurve.minor_mem (k : Type u) [CommRing k] (n : ℕ) (p : MinorIndex n) : hankelMinor k n p ∈ hankelIdeal k n
```

Each displayed minor belongs to the ideal it generates.

[Source](../ToricIdeals/RationalNormalCurve.lean#L96) (line 96).

### ToricIdeals.RationalNormalCurve.hankelIdeal_le_ker

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_le_ker (k : Type u) [CommRing k] (n : ℕ) : hankelIdeal k n ≤ RingHom.ker (rncMap k n)
```

Every Hankel minor vanishes under the rational-normal-curve map, for all
`n` and all commutative coefficient rings.

[Source](../ToricIdeals/RationalNormalCurve.lean#L102) (line 102).

### ToricIdeals.RationalNormalCurve.hankelIdeal_zero

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_zero (k : Type u) [CommRing k] : hankelIdeal k 0 = ⊥
```

At degree zero the Hankel matrix has no ordered pair of columns.

[Source](../ToricIdeals/RationalNormalCurve.lean#L114) (line 114).

### ToricIdeals.RationalNormalCurve.hankelIdeal_one

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_one (k : Type u) [CommRing k] : hankelIdeal k 1 = ⊥
```

At degree one its single column supplies no `2 × 2` minor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L120) (line 120).

### ToricIdeals.RationalNormalCurve.hankelIdeal_zero_lt_ker

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_zero_lt_ker (k : Type u) [CommRing k] [Nontrivial k] : hankelIdeal k 0 < RingHom.ker (rncMap k 0)
```

Degree zero is genuinely exceptional over every nontrivial coefficient
ring: the sole variable maps to `1`, while there are no minors.

[Source](../ToricIdeals/RationalNormalCurve.lean#L127) (line 127).

### ToricIdeals.RationalNormalCurve.rncExponent_one

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_one (d : Fin (1 + 1) →₀ ℕ) : (rncExponent 1) d = d
```

At degree one the exponent map on the two source variables is the identity.

[Source](../ToricIdeals/RationalNormalCurve.lean#L153) (line 153).

### ToricIdeals.RationalNormalCurve.rncMap_one_injective

```lean
theorem ToricIdeals.RationalNormalCurve.rncMap_one_injective (k : Type u) [CommRing k] : Function.Injective ⇑(rncMap k 1)
```

The degree-one monomial parametrization is injective.

[Source](../ToricIdeals/RationalNormalCurve.lean#L159) (line 159).

### ToricIdeals.RationalNormalCurve.hankelIdeal_one_eq_ker

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_one_eq_ker (k : Type u) [CommRing k] : hankelIdeal k 1 = RingHom.ker (rncMap k 1)
```

Degree one is valid but trivial: there are no minors and the
parametrization is injective.

[Source](../ToricIdeals/RationalNormalCurve.lean#L165) (line 165).

### ToricIdeals.RationalNormalCurve.sourceDegree

```lean
abbrev ToricIdeals.RationalNormalCurve.sourceDegree (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ ℕ
```

Total number of source variables in a source monomial.

[Source](../ToricIdeals/RationalNormalCurve.lean#L173) (line 173).

### ToricIdeals.RationalNormalCurve.sourceWeight

```lean
noncomputable def ToricIdeals.RationalNormalCurve.sourceWeight (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ ℕ
```

Weighted index sum `∑ i, i*d_i` of a source monomial.

[Source](../ToricIdeals/RationalNormalCurve.lean#L177) (line 177).

### ToricIdeals.RationalNormalCurve.sourceEnergy

```lean
noncomputable def ToricIdeals.RationalNormalCurve.sourceEnergy (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ ℕ
```

Convex termination measure `∑ i, i²*d_i`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L181) (line 181).

### ToricIdeals.RationalNormalCurve.outerExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.outerExponent (n : ℕ) (p : MinorIndex n) : Fin (n + 1) →₀ ℕ
```

The two separated endpoint variables occurring in a Hankel minor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L185) (line 185).

### ToricIdeals.RationalNormalCurve.innerExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.innerExponent (n : ℕ) (p : MinorIndex n) : Fin (n + 1) →₀ ℕ
```

The two variables one step closer together in the same Hankel minor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L189) (line 189).

### ToricIdeals.RationalNormalCurve.reduceExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.reduceExponent (n : ℕ) (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) : Fin (n + 1) →₀ ℕ
```

Replace one occupied separated pair by the corresponding closer pair.

[Source](../ToricIdeals/RationalNormalCurve.lean#L193) (line 193).

### ToricIdeals.RationalNormalCurve.monomial_add_one

```lean
theorem ToricIdeals.RationalNormalCurve.monomial_add_one (k : Type u) [CommRing k] (n : ℕ) (d e : Fin (n + 1) →₀ ℕ) : (MvPolynomial.monomial (d + e)) 1 = (MvPolynomial.monomial d) 1 * (MvPolynomial.monomial e) 1
```

Multiplication of coefficient-one source monomials adds their exponents.

[Source](../ToricIdeals/RationalNormalCurve.lean#L198) (line 198).

### ToricIdeals.RationalNormalCurve.monomial_outer_sub_inner

```lean
theorem ToricIdeals.RationalNormalCurve.monomial_outer_sub_inner (k : Type u) [CommRing k] (n : ℕ) (p : MinorIndex n) : (MvPolynomial.monomial (outerExponent n p)) 1 - (MvPolynomial.monomial (innerExponent n p)) 1 = hankelMinor k n p
```

The outer-minus-inner monomial relation is the corresponding Hankel minor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L203) (line 203).

### ToricIdeals.RationalNormalCurve.rncExponent_outer_eq_inner

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_outer_eq_inner (n : ℕ) (p : MinorIndex n) : (rncExponent n) (outerExponent n p) = (rncExponent n) (innerExponent n p)
```

A single inward move preserves the target exponent on its replaced pair.

[Source](../ToricIdeals/RationalNormalCurve.lean#L210) (line 210).

### ToricIdeals.RationalNormalCurve.inner_energy_lt_outer_energy

```lean
theorem ToricIdeals.RationalNormalCurve.inner_energy_lt_outer_energy (n : ℕ) (p : MinorIndex n) : (sourceEnergy n) (innerExponent n p) < (sourceEnergy n) (outerExponent n p)
```

The closer pair has strictly smaller squared-index energy.

[Source](../ToricIdeals/RationalNormalCurve.lean#L216) (line 216).

### ToricIdeals.RationalNormalCurve.reduceExponent_preserves_rncExponent

```lean
theorem ToricIdeals.RationalNormalCurve.reduceExponent_preserves_rncExponent (n : ℕ) (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) (h : outerExponent n p ≤ d) : (rncExponent n) (reduceExponent n d p) = (rncExponent n) d
```

An applicable inward move preserves the full monomial's target exponent.

[Source](../ToricIdeals/RationalNormalCurve.lean#L226) (line 226).

### ToricIdeals.RationalNormalCurve.reduceExponent_energy_lt

```lean
theorem ToricIdeals.RationalNormalCurve.reduceExponent_energy_lt (n : ℕ) (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) (h : outerExponent n p ≤ d) : (sourceEnergy n) (reduceExponent n d p) < (sourceEnergy n) d
```

An applicable inward move strictly decreases natural-number energy.

[Source](../ToricIdeals/RationalNormalCurve.lean#L241) (line 241).

### ToricIdeals.RationalNormalCurve.monomial_sub_reduceExponent_mem

```lean
theorem ToricIdeals.RationalNormalCurve.monomial_sub_reduceExponent_mem (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) (h : outerExponent n p ≤ d) : (MvPolynomial.monomial d) 1 - (MvPolynomial.monomial (reduceExponent n d p)) 1 ∈ hankelIdeal k n
```

The monomial change in an applicable inward move is a multiple of a minor,
so its difference belongs to `hankelIdeal`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L256) (line 256).

### ToricIdeals.RationalNormalCurve.Normal

```lean
def ToricIdeals.RationalNormalCurve.Normal (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : Prop
```

A terminal exponent has no occupied pair separated by at least two indices;
equivalently no `outerExponent` fits inside it.

[Source](../ToricIdeals/RationalNormalCurve.lean#L273) (line 273).

### ToricIdeals.RationalNormalCurve.Normal.index_le_add_one

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.index_le_add_one {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (hd : Normal n d) {i j : Fin (n + 1)} (hi : d i ≠ 0) (hj : d j ≠ 0) : ↑i ≤ ↑j + 1
```

Two occupied positions in a terminal exponent differ by at most one.

[Source](../ToricIdeals/RationalNormalCurve.lean#L278) (line 278).

### ToricIdeals.RationalNormalCurve.Normal.mem_support_eq_or_val_eq_add_one

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.mem_support_eq_or_val_eq_add_one {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (hd : Normal n d) {q i : Fin (n + 1)} (hq : d q ≠ 0) (hmin : q ≤ i) (hi : i ∈ d.support) : i = q ∨ ↑i = ↑q + 1
```

Relative to an occupied leftmost position, a terminal exponent is supported
at that position and possibly its successor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L319) (line 319).

### ToricIdeals.RationalNormalCurve.Normal.degree_weight_eq_min_add_succ

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.degree_weight_eq_min_add_succ {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (hd : Normal n d) {q : Fin (n + 1)} (hq : d q ≠ 0) (hmin : ∀ i ∈ d.support, q ≤ i) (hq_lt : ↑q < n) : have q1 := ⟨↑q + 1, ⋯⟩; (sourceDegree n) d = d q + d q1 ∧ (sourceWeight n) d = ↑q * d q + ↑q1 * d q1
```

Degree and weight of a terminal exponent whose leftmost occupied position
has a successor.

[Source](../ToricIdeals/RationalNormalCurve.lean#L338) (line 338).

### ToricIdeals.RationalNormalCurve.Normal.eq_single_add_single_succ

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.eq_single_add_single_succ {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (hd : Normal n d) {q : Fin (n + 1)} (hq : d q ≠ 0) (hmin : ∀ i ∈ d.support, q ≤ i) (hq_lt : ↑q < n) : have q1 := ⟨↑q + 1, ⋯⟩; d = Finsupp.single q (d q) + Finsupp.single q1 (d q1)
```

Explicit two-term expansion of a terminal exponent from its occupied
leftmost position.

[Source](../ToricIdeals/RationalNormalCurve.lean#L368) (line 368).

### ToricIdeals.RationalNormalCurve.Normal.eq_single_of_min_eq_last

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.eq_single_of_min_eq_last {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (_hd : Normal n d) {q : Fin (n + 1)} (_hq : d q ≠ 0) (hmin : ∀ i ∈ d.support, q ≤ i) (hq_last : ↑q = n) : d = Finsupp.single q (d q)
```

A terminal exponent whose leftmost occupied position is the last position
is a single basis exponent.

[Source](../ToricIdeals/RationalNormalCurve.lean#L397) (line 397).

### ToricIdeals.RationalNormalCurve.Normal.min_val_eq_weight_div_degree

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.min_val_eq_weight_div_degree {n : ℕ} {d : Fin (n + 1) →₀ ℕ} (hd : Normal n d) (hdegree : 0 < (sourceDegree n) d) : have hs := ⋯; ↑(d.support.min' hs) = (sourceWeight n) d / (sourceDegree n) d
```

The left endpoint of a nonzero terminal exponent is the quotient of its
weight by its degree.

[Source](../ToricIdeals/RationalNormalCurve.lean#L412) (line 412).

### ToricIdeals.RationalNormalCurve.Normal.eq_of_degree_weight_eq

```lean
theorem ToricIdeals.RationalNormalCurve.Normal.eq_of_degree_weight_eq {n : ℕ} {d e : Fin (n + 1) →₀ ℕ} (hd : Normal n d) (he : Normal n e) (hdegree : (sourceDegree n) d = (sourceDegree n) e) (hweight : (sourceWeight n) d = (sourceWeight n) e) : d = e
```

Terminal exponents are determined by their total degree and weighted index
sum.  This is the adjacent-support uniqueness step behind the toric-kernel
calculation.

[Source](../ToricIdeals/RationalNormalCurve.lean#L459) (line 459).

### ToricIdeals.RationalNormalCurve.exists_normal

```lean
theorem ToricIdeals.RationalNormalCurve.exists_normal (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : ∃ (e : Fin (n + 1) →₀ ℕ), Normal n e ∧ (rncExponent n) e = (rncExponent n) d ∧ (MvPolynomial.monomial d) 1 - (MvPolynomial.monomial e) 1 ∈ hankelIdeal k n
```

Convex-energy reduction terminates at a terminal monomial with the same
target exponent and a coefficient-one monomial congruent modulo the Hankel ideal.
Well-founded induction on `sourceEnergy` uses the strict decrease of each move.

[Source](../ToricIdeals/RationalNormalCurve.lean#L553) (line 553).

### ToricIdeals.RationalNormalCurve.rncExponent_second

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_second (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : ((rncExponent n) d) 1 = (sourceWeight n) d
```

The second target exponent is the source weighted-index sum.

[Source](../ToricIdeals/RationalNormalCurve.lean#L581) (line 581).

### ToricIdeals.RationalNormalCurve.rncExponent_total

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_total (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : ((rncExponent n) d) 0 + ((rncExponent n) d) 1 = n * (sourceDegree n) d
```

The sum of both target exponents is `n` times the source degree.
Recovering the degree from this identity requires positive `n`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L587) (line 587).

### ToricIdeals.RationalNormalCurve.rncExponent_injective_on_normal

```lean
theorem ToricIdeals.RationalNormalCurve.rncExponent_injective_on_normal (n : ℕ) (hn : 1 ≤ n) {d e : Fin (n + 1) →₀ ℕ} (hd : Normal n d) (he : Normal n e) (hexponent : (rncExponent n) d = (rncExponent n) e) : d = e
```

The rational-normal-curve exponent map is injective on terminal exponents
when `1 ≤ n`: the target pair recovers degree and weight, which determine the
terminal exponent. It is not asserted injective on every source exponent.

[Source](../ToricIdeals/RationalNormalCurve.lean#L608) (line 608).

### ToricIdeals.RationalNormalCurve.normalSourceExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.normalSourceExponent (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : Fin (n + 1) →₀ ℕ
```

A classically selected terminal exponent congruent to `d` modulo the
Hankel ideal. The selection depends on `k` and is noncomputable.

[Source](../ToricIdeals/RationalNormalCurve.lean#L624) (line 624).

### ToricIdeals.RationalNormalCurve.normalSourceExponent_normal

```lean
theorem ToricIdeals.RationalNormalCurve.normalSourceExponent_normal (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : Normal n (normalSourceExponent k n d)
```

The chosen source representative is terminal.

[Source](../ToricIdeals/RationalNormalCurve.lean#L630) (line 630).

### ToricIdeals.RationalNormalCurve.normalSourceExponent_rncExponent

```lean
theorem ToricIdeals.RationalNormalCurve.normalSourceExponent_rncExponent (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : (rncExponent n) (normalSourceExponent k n d) = (rncExponent n) d
```

The chosen source representative preserves the target exponent.

[Source](../ToricIdeals/RationalNormalCurve.lean#L635) (line 635).

### ToricIdeals.RationalNormalCurve.monomial_sub_normalSourceExponent_mem

```lean
theorem ToricIdeals.RationalNormalCurve.monomial_sub_normalSourceExponent_mem (k : Type u) [CommRing k] (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : (MvPolynomial.monomial d) 1 - (MvPolynomial.monomial (normalSourceExponent k n d)) 1 ∈ hankelIdeal k n
```

The coefficient-one source monomial and its selected terminal representative
are congruent modulo the Hankel ideal.

[Source](../ToricIdeals/RationalNormalCurve.lean#L641) (line 641).

### ToricIdeals.RationalNormalCurve.normalSourceExponent_eq_of_rncExponent_eq

```lean
theorem ToricIdeals.RationalNormalCurve.normalSourceExponent_eq_of_rncExponent_eq (k : Type u) [CommRing k] (n : ℕ) (hn : 1 ≤ n) {d e : Fin (n + 1) →₀ ℕ} (h : (rncExponent n) d = (rncExponent n) e) : normalSourceExponent k n d = normalSourceExponent k n e
```

Equal target exponents select the same terminal representative for `1 ≤ n`,
using injectivity only among terminal exponents.

[Source](../ToricIdeals/RationalNormalCurve.lean#L649) (line 649).

### ToricIdeals.RationalNormalCurve.fiberNormalExponent

```lean
noncomputable def ToricIdeals.RationalNormalCurve.fiberNormalExponent (k : Type u) [CommRing k] (n : ℕ) (t : Fin 2 →₀ ℕ) : Fin (n + 1) →₀ ℕ
```

A classical, noncomputable terminal representative selected by a target
exponent, also parameterized by the coefficient ring `k`. By definition values
outside the image of `rncExponent` are zero; no additive section is asserted.

[Source](../ToricIdeals/RationalNormalCurve.lean#L658) (line 658).

### ToricIdeals.RationalNormalCurve.fiberNormalExponent_image

```lean
theorem ToricIdeals.RationalNormalCurve.fiberNormalExponent_image (k : Type u) [CommRing k] (n : ℕ) (hn : 1 ≤ n) (d : Fin (n + 1) →₀ ℕ) : fiberNormalExponent k n ((rncExponent n) d) = normalSourceExponent k n d
```

On the image of `rncExponent`, the fiber selection equals the chosen
terminal normal form for the source exponent when `1 ≤ n`.

[Source](../ToricIdeals/RationalNormalCurve.lean#L668) (line 668).

### ToricIdeals.RationalNormalCurve.ker_le_hankelIdeal

```lean
theorem ToricIdeals.RationalNormalCurve.ker_le_hankelIdeal (k : Type u) [CommRing k] (n : ℕ) (hn : 1 ≤ n) : RingHom.ker (rncMap k n) ≤ hankelIdeal k n
```

Reverse inclusion in the kernel calculation, obtained by normalizing each
coefficient along its target-exponent fiber. The coefficient-one congruence is
scaled by `C r` for every `r : k` and passed to the generic fiber theorem.

[Source](../ToricIdeals/RationalNormalCurve.lean#L680) (line 680).

### ToricIdeals.RationalNormalCurve.hankelIdeal_eq_ker

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_eq_ker (k : Type u) [CommRing k] (n : ℕ) (hn : 1 ≤ n) : hankelIdeal k n = RingHom.ker (rncMap k n)
```

For every positive `n`, the `2 × 2` Hankel minors generate exactly the
kernel of the rational-normal-curve monomial parametrization, over an arbitrary
commutative ring.

[Source](../ToricIdeals/RationalNormalCurve.lean#L704) (line 704).

### ToricIdeals.RationalNormalCurve.quotientEquivRange

```lean
noncomputable def ToricIdeals.RationalNormalCurve.quotientEquivRange (k : Type u) [CommRing k] (n : ℕ) (hn : 1 ≤ n) : Source k n ⧸ hankelIdeal k n ≃+* ↥(rncMap k n).range
```

The quotient by the Hankel ideal is the *image subring* of the monomial map,
not necessarily the entire two-variable target. Dependent transport in the
definition does not promise `rfl`/`simp` evaluation on arbitrary quotient
representatives; use ring-homomorphism laws such as `map_one` when appropriate.

[Source](../ToricIdeals/RationalNormalCurve.lean#L711) (line 711).

### ToricIdeals.RationalNormalCurve.hankelIdeal_isPrime

```lean
theorem ToricIdeals.RationalNormalCurve.hankelIdeal_isPrime (k : Type u) [CommRing k] [IsDomain k] (n : ℕ) (hn : 1 ≤ n) : (hankelIdeal k n).IsPrime
```

Over a domain, the Hankel ideal is prime.

[Source](../ToricIdeals/RationalNormalCurve.lean#L720) (line 720).

### ToricIdeals.RationalNormalCurve.quotient_isDomain

```lean
theorem ToricIdeals.RationalNormalCurve.quotient_isDomain (k : Type u) [CommRing k] [IsDomain k] (n : ℕ) (hn : 1 ≤ n) : IsDomain (Source k n ⧸ hankelIdeal k n)
```

Over a domain, the rational-normal-curve coordinate ring is a domain.

[Source](../ToricIdeals/RationalNormalCurve.lean#L726) (line 726).

### ToricIdeals.RationalNormalCurve.spectrum_irreducible

```lean
theorem ToricIdeals.RationalNormalCurve.spectrum_irreducible (k : Type u) [CommRing k] [IsDomain k] (n : ℕ) (hn : 1 ≤ n) : IrreducibleSpace (PrimeSpectrum (Source k n ⧸ hankelIdeal k n))
```

The prime spectrum of the rational-normal-curve coordinate ring is
irreducible over a domain.

[Source](../ToricIdeals/RationalNormalCurve.lean#L732) (line 732).

## Module `ToricIdeals`

> # Toric ideals
>
> Root import for reusable Lean theory of monomial maps, toric ideals, and
> rational normal curves. Import the leaves directly when only one part is needed:
> `ToricIdeals.MonoidAlgebra.FiberNormalization` supplies the independent-universe
> coefficientwise kernel principle, while `ToricIdeals.RationalNormalCurve`
> supplies the Hankel-minor kernel calculation for positive degree, its small-degree
> boundaries, a quotient-to-image equivalence, and domain-dependent consequences.

[Module source](../ToricIdeals.lean)

## Module `ToricIdealsTest.Audit`

> # Audit examples
>
> Named, stored clients of the toric-ideal boundary results and selected axiom prints.

[Module source](../ToricIdealsTest/Audit.lean)

## Module `ToricIdealsTest.RootClient`

> # Root-import clients
>
> Stored private checks of the public monomial-map and rational-normal-curve APIs
> through an ordinary import of `ToricIdeals`.

[Module source](../ToricIdealsTest/RootClient.lean)

## Module `ToricIdealsTest.ReadmeKernel`

> # README example: the positive-degree kernel through a direct leaf import

[Module source](../ToricIdealsTest/ReadmeKernel.lean)
