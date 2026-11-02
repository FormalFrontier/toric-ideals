/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Regular.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Regular single terms in monoid algebras

Regularity of a single term separates regularity of its coefficient from cancellation
at its index. Subsingleton coefficient semirings require no cancellation of the index.
No associativity or identity is required of the index multiplication.
-/

public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} {M : Type v} [Semiring R] [Mul M]

-- Multiplication by a single term acts on coefficients, then transports indices.
private theorem coeff_single_mul_eq_mapDomain (m : M) (r : R) (x : MonoidAlgebra R M) :
    (single m r * x).coeff =
      Finsupp.mapDomain (m * ·) (Finsupp.mapRange (r * ·) (mul_zero r) x.coeff) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, coeff_add, hx, hy,
      Finsupp.mapRange_add (mul_add r), Finsupp.mapDomain_add]
  | single n s =>
    simp only [single_mul_single, coeff_single,
      Finsupp.mapRange_single, Finsupp.mapDomain_single]

private theorem coeff_mul_single_eq_mapDomain (m : M) (r : R) (x : MonoidAlgebra R M) :
    (x * single m r).coeff =
      Finsupp.mapDomain (· * m) (Finsupp.mapRange (· * r) (zero_mul r) x.coeff) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [add_mul, coeff_add, hx, hy,
      Finsupp.mapRange_add (f := fun a : R => a * r) (fun a b => add_mul a b r),
      Finsupp.mapDomain_add]
  | single n s =>
    simp only [single_mul_single, coeff_single,
      Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- A single term is left-regular precisely when its coefficient is left-regular and
its index is left-regular, unless the coefficient semiring is subsingleton. -/
theorem isLeftRegular_single_iff (m : M) (r : R) :
    IsLeftRegular (single m r : MonoidAlgebra R M) ↔
      IsLeftRegular r ∧ (Subsingleton R ∨ IsLeftRegular m) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Finsupp.single_injective m
      have hs : (single m a : MonoidAlgebra R M) = single m b :=
        h (by simp only [single_mul_single, hab])
      simpa only [coeff_single] using congrArg coeff hs
    · rcases subsingleton_or_nontrivial R with hR | hR
      · exact Or.inl hR
      · let _ := hR
        right
        intro a b hab
        apply Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
        have hs : (single a 1 : MonoidAlgebra R M) = single b 1 :=
          h (by simp only [single_mul_single, mul_one, hab])
        simpa only [coeff_single] using congrArg coeff hs
  · rintro ⟨hr, hR | hm⟩
    · let _ := hR
      intro x y _
      apply MonoidAlgebra.ext
      ext n
      exact Subsingleton.elim _ _
    · intro x y hxy
      apply MonoidAlgebra.ext
      apply Finsupp.mapRange_injective (r * ·) (mul_zero r) hr
      apply Finsupp.mapDomain_injective hm
      simpa only [coeff_single_mul_eq_mapDomain] using congrArg coeff hxy

/-- A single term is right-regular precisely when its coefficient is right-regular and
its index is right-regular, unless the coefficient semiring is subsingleton. -/
theorem isRightRegular_single_iff (m : M) (r : R) :
    IsRightRegular (single m r : MonoidAlgebra R M) ↔
      IsRightRegular r ∧ (Subsingleton R ∨ IsRightRegular m) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Finsupp.single_injective m
      have hs : (single m a : MonoidAlgebra R M) = single m b :=
        h (by simp only [single_mul_single, hab])
      simpa only [coeff_single] using congrArg coeff hs
    · rcases subsingleton_or_nontrivial R with hR | hR
      · exact Or.inl hR
      · let _ := hR
        right
        intro a b hab
        apply Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
        have hs : (single a 1 : MonoidAlgebra R M) = single b 1 :=
          h (by simp only [single_mul_single, one_mul, hab])
        simpa only [coeff_single] using congrArg coeff hs
  · rintro ⟨hr, hR | hm⟩
    · let _ := hR
      intro x y _
      apply MonoidAlgebra.ext
      ext n
      exact Subsingleton.elim _ _
    · intro x y hxy
      apply MonoidAlgebra.ext
      apply Finsupp.mapRange_injective (· * r) (zero_mul r) hr
      apply Finsupp.mapDomain_injective hm
      simpa only [coeff_mul_single_eq_mapDomain] using congrArg coeff hxy

/-- A single term is regular precisely when its coefficient is regular and its index
is regular, unless the coefficient semiring is subsingleton. -/
theorem isRegular_single_iff (m : M) (r : R) :
    IsRegular (single m r : MonoidAlgebra R M) ↔
      IsRegular r ∧ (Subsingleton R ∨ IsRegular m) := by
  rw [isRegular_iff, isLeftRegular_single_iff, isRightRegular_single_iff]
  constructor
  · rintro ⟨⟨hl, hml⟩, ⟨hr, hmr⟩⟩
    refine ⟨⟨hl, hr⟩, ?_⟩
    rcases hml with hR | hml
    · exact Or.inl hR
    · rcases hmr with hR | hmr
      · exact Or.inl hR
      · exact Or.inr ⟨hml, hmr⟩
  · rintro ⟨hr, hR | hm⟩
    · exact ⟨⟨hr.left, Or.inl hR⟩, ⟨hr.right, Or.inl hR⟩⟩
    · exact ⟨⟨hr.left, Or.inr hm.left⟩, ⟨hr.right, Or.inr hm.right⟩⟩

end MonoidAlgebra
