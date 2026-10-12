/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum

/-!
# Examples and boundaries for coefficientwise fiber normalization

The examples below concern the basis congruence for every source exponent and
coefficient, and the separate containment of the ideal in a monomial-map kernel.
They use only Mathlib and do not depend on a normalization theorem.

Doubling natural exponents admits normalization by division by two on its image,
but is not surjective, and this normalization is not a section on all target
exponents. Collapsing all exponents to zero gives a nonzero proper collision
ideal over integer coefficients. Over the zero ring, basis congruences and
algebra-map surjectivity do
not imply exponent-map surjectivity. The top ideal satisfies every congruence but
need not be contained in the kernel. Identity maps supply examples with genuinely
noncommutative coefficients and genuinely noncommutative exponent addition.
-/

@[expose] public noncomputable section

namespace AddMonoidAlgebra

universe u v w

private theorem doubling_half (m : ℕ) :
    ((AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) m) / 2 = m := by
  simp only [AddMonoidHom.add_apply, AddMonoidHom.id_apply]
  omega

/-- Doubling natural exponents satisfies the all-coefficient basis congruence
modulo the bottom ideal, over any ring, with normalization `n ↦ n / 2`. -/
theorem doubling_basis_congruence (R : Type u) [Ring R] :
    ∀ (m : ℕ) (r : R),
      single m r - single (((AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) m) / 2) r ∈
        (⊥ : Ideal (AddMonoidAlgebra R ℕ)) := by
  intro m r
  rw [doubling_half]
  simp

/-- The bottom ideal meets the kernel-containment hypothesis for doubling. -/
theorem doubling_bottom_le_kernel (R : Type u) [Ring R] :
    (⊥ : Ideal (AddMonoidAlgebra R ℕ)) ≤
      RingHom.ker (mapDomainRingHom R (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)) :=
  bot_le

/-- Doubling natural exponents omits the target exponent `1`. -/
theorem doubling_not_surjective :
    ¬ Function.Surjective (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) := by
  intro h
  obtain ⟨m, hm⟩ := h 1
  simp only [AddMonoidHom.add_apply, AddMonoidHom.id_apply] at hm
  omega

/-- Division by two is not a right inverse to doubling on all natural exponents. -/
theorem half_not_rightInverse_doubling :
    ¬ Function.RightInverse (fun n : ℕ ↦ n / 2)
      (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) := by
  intro h
  have h₁ := h 1
  norm_num at h₁

/-- Division by two does not preserve addition of natural exponents. -/
theorem half_not_additive :
    ¬ ∀ (m n : ℕ), (m + n) / 2 = m / 2 + n / 2 := by
  intro h
  have h₁ := h 1 1
  norm_num at h₁

/-- In a zero coefficient ring, any exponent function and any normalization
satisfy the basis congruence for every coefficient and every ideal. -/
theorem subsingleton_basis_congruence
    {R : Type u} {M : Type v} {N : Type w} [Ring R] [Subsingleton R] [AddMonoid M]
    (I : Ideal (AddMonoidAlgebra R M)) (φ : M → N) (normal : N → M) :
    ∀ (m : M) (r : R), single m r - single (normal (φ m)) r ∈ I := by
  intro m r
  rw [Subsingleton.elim (single m r - single (normal (φ m)) r) 0]
  exact I.zero_mem

/-- Every monomial map with zero coefficients has the whole source as its kernel. -/
theorem subsingleton_mapDomain_kernel
    {R : Type u} {M : Type v} {N : Type w}
    [Ring R] [Subsingleton R] [AddMonoid M] [AddMonoid N] (φ : M →+ N) :
    RingHom.ker (mapDomainRingHom R φ) = ⊤ :=
  RingHom.ker_eq_top_of_subsingleton _

/-- Over `ZMod 1`, even a nonsurjective doubling exponent map induces a surjective
algebra map, since its target algebra is a subsingleton. -/
theorem zmod_one_doubling_surjective :
    Function.Surjective
        (mapDomainAlgHom (ZMod 1) (ZMod 1) (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)) ∧
      ¬ Function.Surjective (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) := by
  refine ⟨?_, doubling_not_surjective⟩
  intro f
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The zero-ring basis congruence requires no coherence at all of the chosen
exponent representative: even the constant-zero normalization is allowed. -/
theorem zmod_one_constant_normalization :
    (∀ (m : ℕ) (r : ZMod 1), single m r - single 0 r ∈
      (⊥ : Ideal (AddMonoidAlgebra (ZMod 1) ℕ))) ∧
    RingHom.ker (mapDomainRingHom (ZMod 1)
      (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)) = ⊤ := by
  exact ⟨subsingleton_basis_congruence ⊥
    (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ) (fun _ ↦ 0),
    subsingleton_mapDomain_kernel _⟩

/-- The top ideal satisfies the all-coefficient congruence for identity
normalization, but is not contained in the identity-map kernel over `ℤ[ℕ]`. -/
theorem top_identity_not_le_kernel :
    (∀ (m : ℕ) (r : ℤ), single m r - single ((AddMonoidHom.id ℕ) m) r ∈
      (⊤ : Ideal (AddMonoidAlgebra ℤ ℕ))) ∧
    ¬ (⊤ : Ideal (AddMonoidAlgebra ℤ ℕ)) ≤
      RingHom.ker (mapDomainRingHom ℤ (AddMonoidHom.id ℕ)) := by
  refine ⟨fun _ _ ↦ by simp, ?_⟩
  intro h
  exact RingHom.one_notMem_ker (mapDomainRingHom ℤ (AddMonoidHom.id ℕ)) (h (by simp))

/-- Collapsing every natural exponent to zero has the all-coefficient basis
congruence modulo the ideal generated by `single 1 1 - single 0 1`. -/
theorem collapse_basis_congruence (R : Type u) [Ring R] :
    ∀ (n : ℕ) (r : R), single n r - single 0 r ∈
      Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra R ℕ)) := by
  intro n r
  induction n with
  | zero => simp
  | succ n ih =>
    have hgen : single 1 1 - single 0 1 ∈
        Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra R ℕ)) :=
      Ideal.mem_span_singleton_self _
    have hstep := (Ideal.span ({single 1 1 - single 0 1} :
      Set (AddMonoidAlgebra R ℕ))).add_mem
        ((Ideal.span _).mul_mem_left (single n r) hgen) ih
    simpa [mul_sub, single_mul_single, sub_add_sub_cancel] using hstep

/-- The collision ideal identifying all powers with exponent zero admits
normalization along any index function, without a target monoid structure. -/
theorem collapse_function_basis_congruence
    (R : Type u) [Ring R] {N : Type w} (φ : ℕ → N) (normal : N → ℕ) :
    ∀ (n : ℕ) (r : R), single n r - single (normal (φ n)) r ∈
      Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra R ℕ)) := by
  intro n r
  have h := (Ideal.span ({single 1 1 - single 0 1} :
    Set (AddMonoidAlgebra R ℕ))).sub_mem
      (collapse_basis_congruence R n r)
      (collapse_basis_congruence R (normal (φ n)) r)
  simpa only [sub_sub_sub_cancel_right] using h

/-- The relation identifying exponent one with exponent zero maps to zero
under the constant-zero exponent homomorphism. -/
theorem collapse_relation_le_kernel (R : Type u) [Ring R] :
    Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra R ℕ)) ≤
      RingHom.ker (mapDomainRingHom R (0 : ℕ →+ ℕ)) := by
  apply Ideal.span_le.mpr
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  apply RingHom.mem_ker.mpr
  rw [map_sub]
  simp [mapDomainRingHom]

/-- Over integer coefficients, the exponent-collision relation generates a
nonzero proper ideal, so its basis congruences are not bottom-ideal examples. -/
theorem collapse_relation_nonzero_proper :
    Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra ℤ ℕ)) ≠ ⊥ ∧
    Ideal.span ({single 1 1 - single 0 1} : Set (AddMonoidAlgebra ℤ ℕ)) ≠ ⊤ := by
  constructor
  · intro hI
    have hgen := Ideal.mem_span_singleton_self
      (single 1 (1 : ℤ) - single (0 : ℕ) 1)
    have heq : single 1 (1 : ℤ) - single (0 : ℕ) 1 = 0 := by
      simpa [hI] using hgen
    have hcoeff := congrArg (fun f : AddMonoidAlgebra ℤ ℕ ↦ f.coeff 1) heq
    norm_num at hcoeff
  · intro hI
    have hone : (1 : AddMonoidAlgebra ℤ ℕ) ∈
        RingHom.ker (mapDomainRingHom ℤ (0 : ℕ →+ ℕ)) :=
      collapse_relation_le_kernel ℤ (by simp [hI])
    exact RingHom.one_notMem_ker (mapDomainRingHom ℤ (0 : ℕ →+ ℕ)) hone

/-- Identity exponent maps and identity normalization satisfy both hypotheses
modulo the bottom ideal without commutativity of coefficients or exponents. -/
theorem identity_bottom_compatible
    (R : Type u) (M : Type v) [Ring R] [AddMonoid M] :
    (∀ (m : M) (r : R), single m r - single ((AddMonoidHom.id M) m) r ∈
      (⊥ : Ideal (AddMonoidAlgebra R M))) ∧
    (⊥ : Ideal (AddMonoidAlgebra R M)) ≤
      RingHom.ker (mapDomainRingHom R (AddMonoidHom.id M)) := by
  exact ⟨fun m r ↦ by simp, bot_le⟩

private theorem matrix_units_not_commute :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℚ) * Matrix.single 1 0 1 ≠
      Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  have h₀₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ ↦ A 0 0) h
  simp only [Matrix.single_mul_single_same, mul_one] at h₀₀
  norm_num [Matrix.single] at h₀₀

/-- Constant monomials with rational matrix coefficients need not commute. -/
theorem matrix_coefficient_monomials_not_commute :
    ∃ f g : AddMonoidAlgebra (Matrix (Fin 2) (Fin 2) ℚ) ℕ, f * g ≠ g * f := by
  refine ⟨single 0 (Matrix.single 0 1 1), single 0 (Matrix.single 1 0 1), ?_⟩
  intro h
  apply matrix_units_not_commute
  have hcoeff := congrArg
    (fun f : AddMonoidAlgebra (Matrix (Fin 2) (Fin 2) ℚ) ℕ ↦ f.coeff 0) h
  simpa using hcoeff

private theorem free_addition_not_commute :
    FreeAddMonoid.of false + FreeAddMonoid.of true ≠
      FreeAddMonoid.of true + FreeAddMonoid.of false := by
  intro h
  have hlist := congrArg FreeAddMonoid.toList h
  simp at hlist

/-- Monomials in a free additive monoid on two generators need not commute,
even with commutative integer coefficients. -/
theorem free_exponent_monomials_not_commute :
    ∃ f g : AddMonoidAlgebra ℤ (FreeAddMonoid Bool), f * g ≠ g * f := by
  refine ⟨single (FreeAddMonoid.of false) 1, single (FreeAddMonoid.of true) 1, ?_⟩
  intro h
  apply free_addition_not_commute
  exact (single_left_inj (one_ne_zero : (1 : ℤ) ≠ 0)).mp (by simpa using h)

private theorem matrix_identity_compatible :
    (∀ (m : ℕ) (r : Matrix (Fin 2) (Fin 2) ℚ),
      single m r - single ((AddMonoidHom.id ℕ) m) r ∈
        (⊥ : Ideal (AddMonoidAlgebra (Matrix (Fin 2) (Fin 2) ℚ) ℕ))) ∧
    (⊥ : Ideal (AddMonoidAlgebra (Matrix (Fin 2) (Fin 2) ℚ) ℕ)) ≤
      RingHom.ker (mapDomainRingHom (Matrix (Fin 2) (Fin 2) ℚ) (AddMonoidHom.id ℕ)) :=
  identity_bottom_compatible (Matrix (Fin 2) (Fin 2) ℚ) ℕ

private theorem free_identity_compatible :
    (∀ (m : FreeAddMonoid Bool) (r : ℤ),
      single m r - single ((AddMonoidHom.id (FreeAddMonoid Bool)) m) r ∈
        (⊥ : Ideal (AddMonoidAlgebra ℤ (FreeAddMonoid Bool)))) ∧
    (⊥ : Ideal (AddMonoidAlgebra ℤ (FreeAddMonoid Bool))) ≤
      RingHom.ker (mapDomainRingHom ℤ (AddMonoidHom.id (FreeAddMonoid Bool))) :=
  identity_bottom_compatible ℤ (FreeAddMonoid Bool)

end AddMonoidAlgebra
