/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
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
* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations` and
  `Mathlib.RingTheory.Flat.Basic`, for quotient coefficient actions and the
  implication from freeness to flatness.
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

end
end ToricIdeals.RationalNormalCurve
