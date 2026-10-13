# The split quadric

For any commutative ring `A`, including the zero ring, put
`F = A[w,x,y,z]`, `I = (wz - xy)`, `Q = F/I`, and `B = A[W,Y,T]`.
The variable orders are `w,x,y,z` and `W,Y,T`.
`SplitQuadric.theta : F →ₐ[A] B` sends the variables to `W,WT,Y,YT`;
`SplitQuadric.phi : Q →ₐ[A] B` is the induced quotient parametrization.
This is the determinant quadric, not the degree-three rational normal curve.

Import `ToricIdeals.SplitQuadric` for the complete interface, or a leaf below
that module. The coordinate-algebra API uses the namespace `SplitQuadric`;
the exponent API uses `ToricIdeals.SplitQuadric`.

## Kernel and range

`kernel_theta` proves `RingHom.ker (theta A).toRingHom = relationIdeal A`,
and `phi_injective` proves quotient injectivity, over every `CommRing A`.

`rangeEquiv : Q ≃ₐ[A] (theta A).range` constructs the first-isomorphism
equivalence. `rangeEquiv_quotientMap` computes it on polynomial representatives;
`rangeEquiv_coe_apply` identifies its inclusion into `B` with `phi`.

The target is the range subalgebra, not all of `B`. Every image exponent
`(u,v,t)` satisfies `t ≤ u+v`; the exponent of `T` alone is outside that cone.
The exponent map is `(a,b,c,d) ↦ (a+b,c+d,b+d)`.
Reduction replaces `k = min a d` copies of `wz` by `xy`. The resulting exponent
is uniquely reduced in its fiber. The total selector `normal` chooses a preimage
only on the cone and is not asserted additive or a global section.

`monomial_sub_normal_mem_relationIdeal` treats every coefficient, including
nilpotents. Its difference factors as a remainder monomial times
`(wz)^k - (xy)^k`, divisible by `wz - xy`. The coefficient remains in the
remainder monomial, so no cancellation is used. `theta_eq_mapDomainAlgHom`
identifies substitution with Mathlib's monoid-algebra map. The coefficientwise
fiber theorem in `ToricIdeals.MonoidAlgebra.FiberNormalization` then proves
kernel containment without an additive selector or a surjective exponent map.

## Universal morphisms and coefficients

`quotientMap_C`, `quotientMap_X`, `phi_quotientMap`, and `phi_w`, `phi_x`,
`phi_y`, `phi_z` give the coefficient and generator computations.

`lift A values h` constructs a morphism to any commutative `A`-algebra whose
four chosen values satisfy the determinant equation. Its characteristic
lemmas are `lift_quotientMap`, `lift_coordinate`, and `lift_coefficientMap`;
`hom_ext` and `lift_unique` give uniqueness from the four coordinate values.

`Examples.axisPoint A a` evaluates on the `w`-axis. Evaluation at the origin
retracts `coefficientMap`, proving `coefficientMap_injective` independently of
the kernel theorem. Consequently `coordinateRing_isDomain_iff` says that `Q`
is a domain exactly when `A` is; `relationIdeal_isPrime_iff` gives the same
criterion for primality of `I`. `IsDomain` includes nontriviality and
`Ideal.IsPrime` includes properness.

The stored clients in `ToricIdealsTest.SplitQuadricExamples` include integer
domains, rational prime ideals, positive characteristic, nonzero zero divisors
over `ZMod 6`, a nonzero square-zero coefficient over `ZMod 4`, and zero rings.
Over the zero ring `phi` is also surjective, but the quotient is not a domain
and the relation ideal is not prime.

## Localization charts

`chartEquiv` identifies the chart where `w` is invertible with the parameter
chart where `W` is invertible. Its models `LQ : Type s` and `LB : Type t` are
independent, each with its own base-algebra and `A`-algebra structures.
The equivalence requires scalar towers `A → Q → LQ` and `A → B → LB`.
No nonzero, domain, or global-unit premise is needed.

`chartForward` localizes `phi`; `inversePolynomial` sends `W,Y,T` to
`w,y,x * invSelf w` in `LQ`, and `chartBackward` extends it to `LB`.
The backward morphism and `chartBackward_algebraMap` do not require the tower
`A → Q → LQ`. Their chosen `A`-action on `LQ` need not agree with that tower.
Both towers are needed for the inverse identities and the equivalence.

`chartForward_algebraMap`, `chartBackward_algebraMap`, `chartEquiv_generators`,
and `chartEquiv_inverse_generators` express the commuting squares and variable
computations. `canonicalChartEquiv` uses the canonical `Localization.Away`
models. These constructions and proofs do not use the global kernel theorem.

## Scope and references

The missing-plane quotient, scheme-theoretic consequences, and naturality
under arbitrary coefficient changes are not included. Point evaluations are
algebraic examples, not a classification of prime spectra by field-valued tuples.

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry*, §4.4,
motivates the determinant model over a field. The results here allow arbitrary
commutative coefficient rings. Mathlib's contributors provide polynomial,
quotient, localization, first-isomorphism, and domain-transport APIs.
Formal Frontier Agents developed the determinant normal-form proof and the
coefficientwise fiber-normalization theorem, using AI-assisted development.
The code is licensed under Apache-2.0.
