/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Internal decompositions under surjective linear maps

A surjective linear map whose kernel is homogeneous carries an internal
submodule decomposition to an internal decomposition by the image submodules.
Only an arbitrary indexed decomposition is needed: neither a grading of the
scalars nor an additive structure on the index type is used.

The additive groups in the source and target allow subtraction in a fiber.
Submodules over a semiring need not themselves be additive groups, so the
proof subtracts in the ambient source, not in its component submodules.

## References

* Mathlib contributors, `Mathlib.Algebra.DirectSum.Decomposition`, for internal
  decompositions and their linear equivalences.
* Mathlib contributors, `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule`,
  for the homogeneous-submodule predicate used here.
-/

@[expose] public section

universe uR uι uM uN

namespace DirectSum

variable {R : Type uR} [Semiring R] {ι : Type uι} [DecidableEq ι]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- A surjective linear map with homogeneous kernel sends a submodule
decomposition to an internal direct sum of the image submodules.
The scalar semiring need not be commutative, and the index type is arbitrary. -/
theorem isInternal_map_of_surjective_of_isHomogeneous_ker
    (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hker : (LinearMap.ker f).IsHomogeneous ℳ) :
    IsInternal (fun i ↦ (ℳ i).map f) := by
  let F := lmap (fun i ↦ f.submoduleMap (ℳ i))
  have hF : Function.Surjective F :=
    (lmap_surjective _).mpr (fun i ↦ f.submoduleMap_surjective (ℳ i))
  have hcomm : coeLinearMap (fun i ↦ (ℳ i).map f) ∘ₗ F =
      f ∘ₗ coeLinearMap ℳ := by
    apply linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, F, lmap_lof, coeLinearMap_lof,
      LinearMap.submoduleMap_coe_apply]
  have hcomm_apply (a : ⨁ i, ℳ i) :
      coeLinearMap (fun i ↦ (ℳ i).map f) (F a) = f (coeLinearMap ℳ a) :=
    DFunLike.congr_fun hcomm a
  have hdecompose (a : ⨁ i, ℳ i) : decompose ℳ (coeLinearMap ℳ a) = a :=
    (decompose ℳ).apply_symm_apply a
  -- Homogeneity controls every component of a difference in the kernel.
  have hcomponents {x y : M} (hxy : f x = f y) (i : ι) :
      f (decompose ℳ x i : M) = f (decompose ℳ y i : M) := by
    let p : M →ₗ[R] M :=
      (ℳ i).subtype ∘ₗ (component R ι (fun i ↦ ℳ i) i) ∘ₗ
        (decomposeLinearEquiv ℳ).toLinearMap
    have hmem : x - y ∈ LinearMap.ker f := by
      change f (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hi := hker i hmem
    change f (p (x - y)) = 0 at hi
    rw [map_sub, map_sub] at hi
    exact sub_eq_zero.mp hi
  change Function.Bijective (coeLinearMap (fun i ↦ (ℳ i).map f))
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hF x
    obtain ⟨b, rfl⟩ := hF y
    have hab : f (coeLinearMap ℳ a) = f (coeLinearMap ℳ b) := by
      rw [← hcomm_apply, ← hcomm_apply]
      exact hxy
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    change f (a i : M) = f (b i : M)
    simpa only [hdecompose] using hcomponents hab i
  · intro y
    obtain ⟨m, rfl⟩ := hf y
    refine ⟨F (decompose ℳ m), ?_⟩
    rw [hcomm_apply]
    change f ((decompose ℳ).symm (decompose ℳ m)) = f m
    rw [(decompose ℳ).symm_apply_apply]

end DirectSum
