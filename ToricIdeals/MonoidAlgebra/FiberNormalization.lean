/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Fiberwise normalization for additive monoid algebras

This file packages the coefficient-collision step common to elementary proofs
of monomial-map kernels.  If every basis monomial is congruent modulo an ideal
to a representative selected solely from its target exponent, then every
element killed by the induced monomial map belongs to that ideal. The proof
expresses the difference from the normalized sum as a finite sum of assumed
ideal members; `mapDomain` sends the normalized sum to zero when the original
sum maps to zero. This does not need `normal` to be additive or a right inverse.
-/

namespace ToricIdeals

noncomputable section

@[expose] public section

open AddMonoidAlgebra

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

/-- A coefficientwise fiber-normalization principle for monomial maps.

For a commutative coefficient ring `R` and additive commutative exponent monoids
`M`, `N` in independent universes, the function `normal : N → M` need not
preserve addition or select a preimage of every target exponent. The input is
the displayed congruence for every source exponent and *every coefficient*.
The conclusion is kernel membership, not injectivity or finite generation.
-/
theorem AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero
    [CommRing R] [AddCommMonoid M] [AddCommMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
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
      simp [AddMonoidAlgebra.mapDomain, Finsupp.mapDomain_apply]
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

end

end

end ToricIdeals
