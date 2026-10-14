/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import ToricIdeals.RationalNormalCurve.Augmentation
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import ToricIdeals.RationalNormalCurve

/-!
# Coefficient modules of rational-normal-curve coordinate rings

The coefficient action on `Source k n ⧸ hankelIdeal k n` is Mathlib's
quotient-algebra action, induced by `MvPolynomial.C` and `Ideal.Quotient.mkₐ`.
No additional coordinate-ring carrier or scalar-action construction is used.

The proofs below use the standard basis of finitely supported coefficient
functions, restricted to exponents in the monomial map's image, and the
algebraic first isomorphism theorem in positive degree. They concern arbitrary
commutative coefficient rings and every degree, including zero rings and rings
with nilpotent elements or zero divisors. At degree zero the ideal is
bottom and the quotient is the full one-variable polynomial ring: its variable
survives, although the monomial parametrization sends that variable to `1`.
At degree one the quotient is the full two-variable polynomial ring. The
positive-degree quotient-to-image equivalence is not a degree-zero equivalence.

The full quotient is also faithfully flat for this coefficient action in every
degree. For nontrivial coefficients, the existing coefficient augmentation makes
the quotient nontrivial, so Mathlib's faithfully flat free-module result applies.
For subsingleton coefficients, transport from finitely supported functions on a
singleton handles the zero ring without a nontriviality assumption or a claim
that an arbitrary chosen basis has a nonempty index.

Mathlib already supplies the polynomial coefficient algebra, the algebra
homomorphism `AddMonoidAlgebra.mapDomainAlgHom`, and the algebraic first
isomorphism theorem `Ideal.quotientKerEquivRange`. Thus the algebra structure
and coefficient compatibility require no new public definition. The original
parametrization's coefficient law is `rncMap_C` in
`ToricIdeals.RationalNormalCurve`.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
  3.6.F, for the Hankel presentation motivating the coordinate ring.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and its earlier
  coefficient-algebra formalization, for the presentation, small-degree
  boundaries, and the coefficient-module statements followed here.
* Mathlib contributors, `Mathlib.Algebra.MonoidAlgebra.Module`,
  `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, and
  `Mathlib.LinearAlgebra.FreeModule.Basic`, for monomial bases and free modules.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Augmentation`, for
  the coefficient augmentation of the full Hankel quotient.
* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations` and
  `Mathlib.RingTheory.Flat.Basic`, for quotient coefficient actions and the
  implication from freeness to flatness.
* Mathlib contributors, `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.LinearAlgebra.Finsupp.Defs`, for faithful flatness of nontrivial free
  modules and nonempty-index finitely supported functions, transport along
  linear equivalences, and the subsingleton-module equivalence.
-/

namespace ToricIdeals.RationalNormalCurve

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

-- The image is a supported coefficient module, not an arbitrary submodule of a free module.
private theorem rncMap_range_free (n : ℕ) :
    Module.Free k (AddMonoidAlgebra.mapDomainAlgHom k k (rncExponent n)).range := by
  let f : Source k n →ₐ[k] Target k :=
    AddMonoidAlgebra.mapDomainAlgHom k k (rncExponent n)
  let cS : Source k n ≃ₗ[k] ((Fin (n + 1) →₀ ℕ) →₀ k) :=
    AddMonoidAlgebra.coeffLinearEquiv k
  let cT : Target k ≃ₗ[k] ((Fin 2 →₀ ℕ) →₀ k) :=
    AddMonoidAlgebra.coeffLinearEquiv k
  let l : ((Fin (n + 1) →₀ ℕ) →₀ k) →ₗ[k] ((Fin 2 →₀ ℕ) →₀ k) :=
    Finsupp.lmapDomain k k (rncExponent n)
  have h : f.range.toSubmodule.map cT.toLinearMap = LinearMap.range l := by
    ext d
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨cS x, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨f (cS.symm a), ⟨cS.symm a, rfl⟩, rfl⟩
  let e : f.range.toSubmodule ≃ₗ[k] LinearMap.range l :=
    cT.ofSubmodules _ _ h
  have hr : LinearMap.range l =
      Finsupp.supported k k (Set.range (rncExponent n)) := by
    simpa only [Finsupp.supported_univ, ← LinearMap.range_eq_map, Set.image_univ]
      using Finsupp.lmapDomain_supported k k (rncExponent n) Set.univ
  let er : LinearMap.range l ≃ₗ[k] (Set.range (rncExponent n) →₀ k) :=
    (LinearEquiv.ofEq _ _ hr).trans
      (Finsupp.supportedEquivFinsupp (R := k) (M := k) (Set.range (rncExponent n)))
  let : Module.Free k (LinearMap.range l) := Module.Free.of_equiv er.symm
  exact Module.Free.of_equiv e.symm

/-- The quotient by the Hankel ideal is free over its coefficient ring in every degree.
This statement uses the quotient's canonical coefficient-module structure. -/
theorem quotient_free (n : ℕ) :
    Module.Free k (Source k n ⧸ hankelIdeal k n) := by
  by_cases hn : n = 0
  · subst n
    rw [hankelIdeal_zero]
    exact Module.Free.of_equiv (AlgEquiv.quotientBot k (Source k 0)).symm.toLinearEquiv
  · let f : Source k n →ₐ[k] Target k :=
      AddMonoidAlgebra.mapDomainAlgHom k k (rncExponent n)
    let : Module.Free k f.range := rncMap_range_free k n
    have hker : hankelIdeal k n = RingHom.ker f.toRingHom :=
      hankelIdeal_eq_ker k n (Nat.one_le_iff_ne_zero.mpr hn)
    rw [hker]
    exact Module.Free.of_equiv (Ideal.quotientKerEquivRange f).symm.toLinearEquiv

/-- The quotient by the Hankel ideal is flat over its coefficient ring in every degree.
This statement uses the quotient's canonical coefficient-module structure. -/
theorem quotient_flat (n : ℕ) :
    Module.Flat k (Source k n ⧸ hankelIdeal k n) := by
  let : Module.Free k (Source k n ⧸ hankelIdeal k n) := quotient_free k n
  exact Module.Flat.of_free

/-- The full quotient by the Hankel ideal is faithfully flat over its coefficient
ring for the canonical coefficient-module structure, in every degree, including
degree zero and over the zero ring. -/
theorem quotient_faithfullyFlat (n : ℕ) :
    Module.FaithfullyFlat k (Source k n ⧸ hankelIdeal k n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · let : Subsingleton k := hk
    let : Module.FaithfullyFlat k (Unit →₀ k) :=
      Module.FaithfullyFlat.finsupp k Unit
    exact Module.FaithfullyFlat.of_linearEquiv k (Unit →₀ k)
      (Module.subsingletonEquiv k (Source k n ⧸ hankelIdeal k n) Unit)
  · let : Nontrivial k := hk
    let : Module.Free k (Source k n ⧸ hankelIdeal k n) := quotient_free k n
    let : Nontrivial (Source k n ⧸ hankelIdeal k n) :=
      (quotientAugmentation k n).toRingHom.domain_nontrivial
    infer_instance

end
end ToricIdeals.RationalNormalCurve
