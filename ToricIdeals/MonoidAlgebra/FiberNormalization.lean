/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Fiberwise normalization for additive monoid algebras

If every basis monomial is congruent modulo a left ideal to a source exponent
selected solely from its target index, then every element whose coefficients
sum to zero along the target fibers belongs to that ideal. This coefficientwise
principle needs a ring of coefficients and an additive source monoid, but no
structure on the target index type or additivity of the index function.

For additive exponent homomorphisms, the principle gives containment of the
monomial-map kernel in the ideal. The separate containment of the ideal in the
kernel gives equality and a membership characterization. The normalization
function need not be additive or a right inverse, and the exponent map need
not be surjective. Ideals are left ideals when the source ring is noncommutative.

## References

The coefficient maps and finite-support summation API used here are provided by
Mathlib's `Algebra.MonoidAlgebra.MapDomain` and `Data.Finsupp.Basic` modules.
-/

namespace ToricIdeals

noncomputable section

@[expose] public section

open AddMonoidAlgebra

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

/-- Coefficientwise fiber normalization puts every mapped-zero element in a left ideal.

The coefficient ring and source additive monoid need not be commutative, and the
index map is an arbitrary function to a type with no prescribed algebraic
structure. Every source exponent and every coefficient must satisfy the basis
congruence. The selector `normal` need not select a preimage of its argument.
For commutative coefficient rings and additive commutative exponent monoids,
this specializes to the monomial-map normalization principle.
-/
theorem AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero
    [Ring R] [AddMonoid M]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M → N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      single m r - single (normal (exponentMap m)) r ∈ I)
    {f : AddMonoidAlgebra R M}
    (hf : AddMonoidAlgebra.mapDomain exponentMap f = 0) : f ∈ I := by
  have hdiff :
      f - AddMonoidAlgebra.mapDomain (normal ∘ exponentMap) f ∈ I := by
    rw [show f - AddMonoidAlgebra.mapDomain (normal ∘ exponentMap) f =
        f.coeff.sum (fun m r ↦
          single m r - single (normal (exponentMap m)) r) by
      ext m
      simp only [coeff_sub, coeff_mapDomain, Function.comp_apply, Finsupp.coe_sub,
        Pi.sub_apply, Finsupp.sum_sub, sum_coeff_single, coeff_finsuppSum, coeff_single,
        Finsupp.coe_sum, sub_right_inj, Finsupp.mapDomain_apply]
      calc
        _ = (f.coeff.sum (fun a r ↦
            Finsupp.single (normal (exponentMap a)) r)) m :=
          Finsupp.sum_apply.symm
        _ = _ := congrFun
          (Finsupp.coe_sum f.coeff
            (fun a r ↦ Finsupp.single (normal (exponentMap a)) r)) m]
    rw [Finsupp.sum]
    exact I.sum_mem fun m _ ↦ basis_sub_normal_mem m (f.coeff m)
  have hnormal : AddMonoidAlgebra.mapDomain (normal ∘ exponentMap) f = 0 := by
    rw [show AddMonoidAlgebra.mapDomain (normal ∘ exponentMap) f =
        AddMonoidAlgebra.mapDomain normal
          (AddMonoidAlgebra.mapDomain exponentMap f) by
      change AddMonoidAlgebra.ofCoeff
          (Finsupp.mapDomain (normal ∘ exponentMap) f.coeff) =
        AddMonoidAlgebra.ofCoeff
          (Finsupp.mapDomain normal (Finsupp.mapDomain exponentMap f.coeff))
      rw [Finsupp.mapDomain_comp]]
    rw [hf, AddMonoidAlgebra.mapDomain_zero]
  simpa [hnormal] using hdiff

/-- All-coefficient basis normalization contains the kernel of the induced monomial map.

This is the coefficientwise normalization principle for bundled additive
exponent homomorphisms. Neither coefficients nor exponent monoids need be
commutative; no surjectivity or section hypothesis is required.
-/
theorem AddMonoidAlgebra.ker_mapDomainRingHom_le
    [Ring R] [AddMonoid M] [AddMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      single m r - single (normal (exponentMap m)) r ∈ I) :
    RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R exponentMap) ≤ I := by
  intro f hf
  exact AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero I exponentMap normal
    basis_sub_normal_mem (by
      simpa only [RingHom.mem_ker, AddMonoidAlgebra.mapDomainRingHom_apply] using hf)

/-- A left ideal below the monomial-map kernel is that kernel if every
basis monomial has its coefficientwise normalization modulo the ideal.

Containment of the ideal in the kernel is a separate, necessary hypothesis;
the basis congruences alone give only the opposite containment.
-/
theorem AddMonoidAlgebra.ideal_eq_ker_mapDomainRingHom
    [Ring R] [AddMonoid M] [AddMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      single m r - single (normal (exponentMap m)) r ∈ I)
    (ideal_le_kernel : I ≤
      RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R exponentMap)) :
    I = RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R exponentMap) := by
  exact le_antisymm ideal_le_kernel
    (AddMonoidAlgebra.ker_mapDomainRingHom_le I exponentMap normal basis_sub_normal_mem)

/-- Membership in a normalized left ideal is equivalent to vanishing under the
coefficientwise monomial map, provided the ideal is contained in its kernel. -/
theorem AddMonoidAlgebra.mem_ideal_iff_mapDomain_eq_zero
    [Ring R] [AddMonoid M] [AddMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      single m r - single (normal (exponentMap m)) r ∈ I)
    (ideal_le_kernel : I ≤
      RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R exponentMap))
    {f : AddMonoidAlgebra R M} :
    f ∈ I ↔ AddMonoidAlgebra.mapDomain exponentMap f = 0 := by
  constructor
  · intro hf
    simpa only [RingHom.mem_ker, AddMonoidAlgebra.mapDomainRingHom_apply] using
      ideal_le_kernel hf
  · exact AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero I exponentMap normal
      basis_sub_normal_mem

end

end

end ToricIdeals
