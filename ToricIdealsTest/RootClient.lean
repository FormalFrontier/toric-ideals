/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis

/-!
# Root-import clients

Stored private checks of the public monomial-map and rational-normal-curve APIs
through an ordinary import of `ToricIdeals`.
-/

open ToricIdeals.RationalNormalCurve

universe u v w

private theorem generic_fiber_normalization
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommMonoid M] [AddCommMonoid N]
    (I : Ideal (AddMonoidAlgebra R M)) (exponentMap : M →+ N)
    (normal : N → M)
    (basis_sub_normal_mem : ∀ (m : M) (r : R),
      AddMonoidAlgebra.single m r -
        AddMonoidAlgebra.single (normal (exponentMap m)) r ∈ I)
    {f : AddMonoidAlgebra R M}
    (hf : AddMonoidAlgebra.mapDomain exponentMap f = 0) : f ∈ I :=
  ToricIdeals.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero
    I exponentMap normal basis_sub_normal_mem hf

variable (k : Type u) [CommRing k]

private theorem degree_zero_strict [Nontrivial k] :
    hankelIdeal k 0 < RingHom.ker (rncMap k 0) :=
  hankelIdeal_zero_lt_ker k

private theorem degree_zero_subsingleton [Subsingleton k] :
    hankelIdeal k 0 = RingHom.ker (rncMap k 0) :=
  Subsingleton.elim _ _

private theorem degree_one_kernel :
    hankelIdeal k 1 = RingHom.ker (rncMap k 1) :=
  hankelIdeal_one_eq_ker k

private theorem degree_two_kernel :
    hankelIdeal k 2 = RingHom.ker (rncMap k 2) :=
  hankelIdeal_eq_ker k 2 (by decide)

private theorem exposed_coordinate (index : Fin 2) :
    coordinateExponent 1 index =
      Finsupp.single (0 : Fin 2) (1 - index.val) +
        Finsupp.single (1 : Fin 2) index.val :=
  rfl

private theorem exposed_monomial_map (n : ℕ) :
    rncMap k n = AddMonoidAlgebra.mapDomainRingHom k (rncExponent n) :=
  rfl

private theorem coefficient_embedding_injective (n : ℕ) :
    Function.Injective (fun r : k ↦ rncMap k n (MvPolynomial.C r)) := by
  intro r s h
  apply MvPolynomial.C_injective (Fin 2) k
  simpa only [rncMap_C] using h

private theorem quotient_range_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (quotientEquivRange k n hn) :=
  (quotientEquivRange k n hn).surjective

private theorem quotient_range_evaluation (n : ℕ) (hn : 1 ≤ n) :
    quotientEquivRange k n hn (1 : Source k n ⧸ hankelIdeal k n) = 1 :=
  map_one (quotientEquivRange k n hn)

private theorem degree_two_prime [IsDomain k] :
    (hankelIdeal k 2).IsPrime :=
  hankelIdeal_isPrime k 2 (by decide)

private theorem degree_two_domain [IsDomain k] :
    IsDomain (Source k 2 ⧸ hankelIdeal k 2) :=
  quotient_isDomain k 2 (by decide)

private theorem degree_two_spectrum [IsDomain k] :
    IrreducibleSpace (PrimeSpectrum (Source k 2 ⧸ hankelIdeal k 2)) :=
  spectrum_irreducible k 2 (by decide)

/-! Closed coefficient-change clients use the existing quotient map directly,
without introducing a coordinate-ring alias or a specialized public map. -/

private theorem residue_four_not_injective :
    ¬ Function.Injective (Int.castRingHom (ZMod 4)) := by
  intro hinj
  exact (by decide : (4 : ℤ) ≠ 0) (hinj (by decide))

private theorem coefficient_minor_mod_four :
    MvPolynomial.map (Int.castRingHom (ZMod 4))
        (hankelMinor ℤ 2 ⟨(0, 1), by decide⟩) =
      MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) -
        MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (1 : Fin 3) := by
  rw [map_hankelMinor]
  rfl

private theorem coefficient_quotient_mod_four_relation :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 2).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 2)
          (hankelMinor ℤ 2 ⟨(0, 1), by decide⟩)) = 0 := by
  rw [Ideal.quotientMap_mk, map_hankelMinor]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (minor_mem (ZMod 4) 2 ⟨(0, 1), by decide⟩)

private theorem coefficient_quotient_mod_four_constant :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 2).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 2) (MvPolynomial.C (4 : ℤ))) = 0 := by
  have hfour : (Int.castRingHom (ZMod 4)) (4 : ℤ) = 0 := by decide
  rw [Ideal.quotientMap_mk, MvPolynomial.map_C, hfour]
  simp

private theorem coefficient_ideal_mod_four_degree_zero :
    Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (hankelIdeal ℤ 0) = ⊥ := by
  rw [map_hankelIdeal, hankelIdeal_zero]

private theorem coefficient_quotient_mod_four_degree_zero_variable :
    Ideal.quotientMap (hankelIdeal (ZMod 4) 0)
        (MvPolynomial.map (Int.castRingHom (ZMod 4)))
        (Ideal.le_comap_of_map_le
          (map_hankelIdeal (Int.castRingHom (ZMod 4)) 0).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1))) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (MvPolynomial.X (0 : Fin 1)) := by
  simp

private theorem integer_degree_zero_kernel_boundary :
    hankelIdeal ℤ 0 < RingHom.ker (rncMap ℤ 0) :=
  hankelIdeal_zero_lt_ker ℤ

private theorem integer_degree_zero_constants_distinct :
    rncMap ℤ 0 (MvPolynomial.C (4 : ℤ)) ≠
      rncMap ℤ 0 (MvPolynomial.C (0 : ℤ)) := by
  intro h
  exact (by decide : (4 : ℤ) ≠ 0) (coefficient_embedding_injective ℤ 0 h)

private theorem integer_degree_two_constant :
    rncMap ℤ 2 (MvPolynomial.C (-3 : ℤ)) = MvPolynomial.C (-3 : ℤ) :=
  rncMap_C ℤ 2 (-3)

private theorem product_degree_two_constant :
    rncMap (ℤ × ℤ) 2 (MvPolynomial.C ((1, 0) : ℤ × ℤ)) =
      MvPolynomial.C ((1, 0) : ℤ × ℤ) :=
  rncMap_C (ℤ × ℤ) 2 (1, 0)

section

open scoped TensorProduct

/-- In degree one, base change to `ℤ/4ℤ` sends `2 ⊗ [X₀ + X₁]` to the
nonzero class `[2(X₀ + X₁)]`, detected by evaluation at `(1, 0)`. -/
private theorem mod_four_degree_one_base_change :
    quotientBaseChangeAlgEquiv ℤ (ZMod 4) 1
        ((2 : ZMod 4) ⊗ₜ[ℤ] Ideal.Quotient.mk (hankelIdeal ℤ 1)
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1)
        (MvPolynomial.C (2 : ZMod 4) *
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))) ∧
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1)
        (MvPolynomial.C (2 : ZMod 4) *
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))) ≠ 0 := by
  constructor
  · have hmap :
        MvPolynomial.map (algebraMap ℤ (ZMod 4))
            (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) =
          MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :=
      ((MvPolynomial.map (algebraMap ℤ (ZMod 4))).map_add
        (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))).trans
          (congrArg₂ (fun p q : Source (ZMod 4) 1 ↦ p + q)
            (MvPolynomial.map_X (algebraMap ℤ (ZMod 4)) (0 : Fin 2))
            (MvPolynomial.map_X (algebraMap ℤ (ZMod 4)) (1 : Fin 2)))
    calc
      _ = Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1)
          ((2 : ZMod 4) • MvPolynomial.map (algebraMap ℤ (ZMod 4))
            (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))) :=
        quotientBaseChangeAlgEquiv_tmul_mk ℤ (ZMod 4) 1 2
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
      _ = _ := congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 4) 1))
        ((congrArg (fun p : Source (ZMod 4) 1 ↦ (2 : ZMod 4) • p) hmap).trans
          (MvPolynomial.smul_eq_C_mul
            (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) (2 : ZMod 4)))
  · rw [hankelIdeal_one]
    intro hzero
    have heval := congrArg
      ((MvPolynomial.eval
          (fun i : Fin 2 ↦ if i = 0 then (1 : ZMod 4) else 0)).comp
        (RingEquiv.quotientBot (Source (ZMod 4) 1)).toRingHom) hzero
    have htwo : (2 : ZMod 4) = 0 := by
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.quotientBot_mk, map_zero, map_mul,
        map_add, MvPolynomial.eval_C, MvPolynomial.eval_X,
        ite_eq_left (rfl : (0 : Fin 2) = 0),
        ite_eq_right (by decide : (1 : Fin 2) ≠ 0), ite_true, add_zero, mul_one] using heval
    exact (by decide : (2 : ZMod 4) ≠ 0) htwo

end

private theorem integer_degree_zero_augmentation :
    quotientAugmentation ℤ 0
        (Ideal.Quotient.mk (hankelIdeal ℤ 0)
          (MvPolynomial.C (3 : ℤ) + MvPolynomial.X (0 : Fin 1))) = 3 := by
  simp only [quotientAugmentation_mk, map_add, MvPolynomial.constantCoeff_C,
    MvPolynomial.constantCoeff_X, add_zero]

/-! Coordinate-axis clients retain the indeterminate in degree zero, kill a
nonzero degree-one coordinate, and preserve a nilpotent coefficient. Polynomial
evaluation also gives maps to a noncommutative matrix algebra. -/

private theorem integer_degree_zero_axis_polynomial :
    axisProjection ℤ 0
        (Ideal.Quotient.mk (hankelIdeal ℤ 0)
          (MvPolynomial.C (3 : ℤ) + MvPolynomial.X (0 : Fin 1))) =
      Polynomial.C (3 : ℤ) + Polynomial.X ∧
    axisSection ℤ 0 (Polynomial.C (3 : ℤ) + Polynomial.X) =
      Ideal.Quotient.mk (hankelIdeal ℤ 0)
        (MvPolynomial.C (3 : ℤ) + MvPolynomial.X (0 : Fin 1)) := by
  constructor
  · rw [map_add, map_add, axisProjection_C, axisProjection_X_zero]
  · rw [map_add, axisSection_C, axisSection_X, map_add]

private theorem integer_degree_one_axis_kernel :
    Ideal.Quotient.mk (hankelIdeal ℤ 1) (MvPolynomial.X (1 : Fin 2)) ≠ 0 ∧
    axisProjection ℤ 1
      (Ideal.Quotient.mk (hankelIdeal ℤ 1) (MvPolynomial.X (1 : Fin 2))) = 0 := by
  constructor
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_one, Submodule.mem_bot] at hmem
    exact MvPolynomial.X_ne_zero (1 : Fin 2) hmem
  · exact axisProjection_X_of_ne_zero ℤ 1 (1 : Fin 2) (by decide)

private theorem mod_four_degree_two_axis_nilpotent :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (MvPolynomial.C (2 : ZMod 4)) ≠ 0 ∧
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (MvPolynomial.C (2 : ZMod 4)) ^ 2 = 0 ∧
    axisProjection (ZMod 4) 2
        (Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (MvPolynomial.C (2 : ZMod 4))) =
      Polynomial.C (2 : ZMod 4) := by
  have htwo : (2 : ZMod 4) ^ 2 = 0 := by decide
  refine ⟨?_, ?_, axisProjection_C (ZMod 4) 2 2⟩
  · intro hzero
    have hconstant : Polynomial.C (2 : ZMod 4) = 0 := by
      rw [← axisProjection_C (ZMod 4) 2 2, hzero, map_zero]
    exact (by decide : (2 : ZMod 4) ≠ 0) (Polynomial.C_eq_zero.mp hconstant)
  · rw [← map_pow, ← MvPolynomial.C_pow, htwo]
    simp

private theorem matrix_degree_two_axis_evaluation :
    ∃! f : (Source (ZMod 2) 2 ⧸ hankelIdeal (ZMod 2) 2) →ₐ[ZMod 2]
        Matrix (Fin 2) (Fin 2) (ZMod 2),
      f (Ideal.Quotient.mk (hankelIdeal (ZMod 2) 2)
          (MvPolynomial.X (0 : Fin 3))) = Matrix.single 0 1 1 ∧
      (∀ i : Fin 3, i ≠ 0 →
        f (Ideal.Quotient.mk (hankelIdeal (ZMod 2) 2) (MvPolynomial.X i)) = 0) ∧
      f (Ideal.Quotient.mk (hankelIdeal (ZMod 2) 2)
          (MvPolynomial.X (0 : Fin 3) ^ 2 + MvPolynomial.C (1 : ZMod 2))) = 1 := by
  have hnil : (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ^ 2 = 0 := by
    rw [pow_two]
    exact Matrix.single_mul_single_of_ne 1 0 1 0 (by decide) 1
  obtain ⟨f, ⟨hzero, hpos⟩, huniq⟩ :=
    existsUnique_axisHom (ZMod 2) 2
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
  refine ⟨f, ⟨hzero, hpos, ?_⟩, ?_⟩
  · rw [eq_aeval_comp_axisProjection (ZMod 2) 2 f hpos, hzero]
    simp only [AlgHom.comp_apply, map_add, map_pow, axisProjection_X_zero,
      Polynomial.aeval_X, map_one, hnil, zero_add]
  · intro g hg
    exact huniq g ⟨hg.1, hg.2.1⟩

private theorem natural_conic_no_left_inverse :
    ¬ ∃ recover : Target ℕ → Source ℕ 2, Function.LeftInverse recover (rncMap ℕ 2) := by
  rintro ⟨recover, hrecover⟩
  rcases (rncMap_injective_iff ℕ 2).mp hrecover.injective with hdegree | hcoeff
  · exact (by decide : (2 : ℕ) ≠ 1) hdegree
  · exact Nat.zero_ne_one (@Subsingleton.elim ℕ hcoeff 0 1)
