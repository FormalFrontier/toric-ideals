/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.Cotangent

/-!
# Quotienting the variable classes recovers the coefficient algebra

These clients instantiate Mathlib's first isomorphism theorem for the coefficient
augmentation and transport its domain to the quotient by the span of all variable
classes. The equivalence evaluates representatives at zero and fixes coefficients.
The integer degree-zero variable is nonzero before this second quotient; integer
coefficients survive in degree one. The nonzero square-zero coefficient `2` in
`ZMod 4` survives the second quotient in every degree, while zero coefficients
make the variable span the unit ideal.

The vertex cotangent basis gives a nonzero integer conic class with raw linear
coordinate `37`, represented by `37 • X₀`. Its scalar multiple interpretation
uses the inherited coefficient action. The degree-zero basis retains the class
of `X₀`; zero coefficients allow vanishing indexed basis vectors, while the
nonzero nilpotent coefficient `2` in `ZMod 4` does not annihilate a basis vector.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Augmentation`, for the
  augmentation kernel and its variable-span description, and
  `ToricIdeals.RationalNormalCurve.Cotangent`, for the prescribed-variable basis
  and raw linear-coordinate formula.
* Mathlib contributors, `Mathlib.RingTheory.Ideal.Quotient.Operations`, for
  `quotientEquivAlgOfEq` and `quotientKerAlgEquivOfSurjective`.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve.AugmentationKernelModels

noncomputable section

universe u

/-- Mathlib's first isomorphism equivalence on the quotient by the variable span. -/
private def coefficientEquiv (R : Type u) [CommRing R] (n : ℕ) :
    ((Source R n ⧸ hankelIdeal R n) ⧸
      Ideal.span (Set.range (fun i : Fin (n + 1) =>
        Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i)))) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (ker_quotientAugmentation R n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (quotientAugmentation_surjective R n))

/-- The transported first isomorphism evaluates any polynomial representative. -/
private theorem coefficientEquiv_mk (R : Type u) [CommRing R] (n : ℕ)
    (f : Source R n) :
    coefficientEquiv R n (Ideal.Quotient.mk _
      (Ideal.Quotient.mkₐ R (hankelIdeal R n) f)) = constantCoeff f := by
  calc
    coefficientEquiv R n (Ideal.Quotient.mk _
        (Ideal.Quotient.mkₐ R (hankelIdeal R n) f)) =
        Ideal.quotientKerAlgEquivOfSurjective
          (f := quotientAugmentation R n) (quotientAugmentation_surjective R n)
          (Ideal.quotientEquivAlgOfEq R (ker_quotientAugmentation R n).symm
            (Ideal.Quotient.mk _ (Ideal.Quotient.mkₐ R (hankelIdeal R n) f))) := rfl
    _ = Ideal.quotientKerAlgEquivOfSurjective
        (f := quotientAugmentation R n) (quotientAugmentation_surjective R n)
        (Ideal.Quotient.mk _ (Ideal.Quotient.mkₐ R (hankelIdeal R n) f)) :=
      congrArg (fun q => Ideal.quotientKerAlgEquivOfSurjective
        (f := quotientAugmentation R n) (quotientAugmentation_surjective R n) q)
        (Ideal.quotientEquivAlgOfEq_mk R (ker_quotientAugmentation R n).symm
          (Ideal.Quotient.mkₐ R (hankelIdeal R n) f))
    _ = quotientAugmentation R n (Ideal.Quotient.mkₐ R (hankelIdeal R n) f) :=
      Ideal.quotientKerAlgEquivOfSurjective_mk
        (f := quotientAugmentation R n) (quotientAugmentation_surjective R n)
        (Ideal.Quotient.mkₐ R (hankelIdeal R n) f)
    _ = constantCoeff f := quotientAugmentation_mk R n f

/-- Coefficients and the inverse equivalence agree with the canonical algebra map. -/
private theorem coefficient_roundtrip (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    coefficientEquiv R n (@algebraMap R
      ((Source R n ⧸ hankelIdeal R n) ⧸
        Ideal.span (Set.range (fun i : Fin (n + 1) =>
          Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i))))
      inferInstance
      (Ideal.Quotient.semiring (Ideal.span (Set.range (fun i : Fin (n + 1) =>
        Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i)))))
      (Ideal.Quotient.algebra R (I := Ideal.span (Set.range (fun i : Fin (n + 1) =>
        Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i))))) r) = r ∧
      (coefficientEquiv R n).symm r = @algebraMap R
        ((Source R n ⧸ hankelIdeal R n) ⧸
          Ideal.span (Set.range (fun i : Fin (n + 1) =>
            Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i))))
        inferInstance
        (Ideal.Quotient.semiring (Ideal.span (Set.range (fun i : Fin (n + 1) =>
          Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i)))))
        (Ideal.Quotient.algebra R (I := Ideal.span (Set.range (fun i : Fin (n + 1) =>
          Ideal.Quotient.mkₐ R (hankelIdeal R n) (X i))))) r := by
  have h := ((coefficientEquiv R n).commutes r).trans (Algebra.algebraMap_self_apply r)
  refine ⟨h, ?_⟩
  apply (coefficientEquiv R n).injective
  exact ((coefficientEquiv R n).apply_symm_apply r).trans h.symm

/-- The degree-zero integer variable is nonzero in the full Hankel quotient,
but is killed by the variable-span quotient, which retains the constant term. -/
private theorem integer_degree_zero :
    Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (X (0 : Fin 1)) ∈
        Ideal.span (Set.range (fun i : Fin 1 =>
          Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (X i))) ∧
      coefficientEquiv ℤ 0 (Ideal.Quotient.mk _
        (Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0)
          (X (0 : Fin 1) + C (37 : ℤ)))) = 37 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have h := congrArg (fun q => (RingEquiv.quotientBot (Source ℤ 0))
      ((Ideal.quotEquivOfEq (hankelIdeal_zero ℤ)) q)) hzero
    apply MvPolynomial.X_ne_zero (R := ℤ) (0 : Fin 1)
    simpa only [Ideal.Quotient.mkₐ_eq_mk, Ideal.quotEquivOfEq_mk,
      RingEquiv.quotientBot_mk, map_zero] using h
  · apply (mem_span_quotient_X_iff ℤ 0 _).mpr
    simp only [Ideal.Quotient.mkₐ_eq_mk, quotientAugmentation_mk, constantCoeff_X]
  · simp only [coefficientEquiv_mk, map_add, constantCoeff_X, constantCoeff_C, zero_add]

/-- Both degree-one variables belong to the kernel, while the coefficient `37`
survives the second quotient and a mixed representative still evaluates to `37`. -/
private theorem integer_degree_one :
    (∀ i : Fin 2, Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 1) (X i) ∈
      Ideal.span (Set.range (fun j : Fin 2 =>
        Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 1) (X j)))) ∧
      Ideal.Quotient.mk _ (Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 1) (C (37 : ℤ))) ≠
        (0 : (Source ℤ 1 ⧸ hankelIdeal ℤ 1) ⧸
          Ideal.span (Set.range (fun i : Fin 2 =>
            Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 1) (X i)))) ∧
      coefficientEquiv ℤ 1 (Ideal.Quotient.mk _
        (Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 1)
          (X (0 : Fin 2) * X (1 : Fin 2) + X (1 : Fin 2) + C (37 : ℤ)))) = 37 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply (mem_span_quotient_X_iff ℤ 1 _).mpr
    simp only [Ideal.Quotient.mkₐ_eq_mk, quotientAugmentation_mk, constantCoeff_X]
  · intro hzero
    have h := congrArg (coefficientEquiv ℤ 1) hzero
    have : (37 : ℤ) = 0 := by
      simpa only [coefficientEquiv_mk, constantCoeff_C, map_zero] using h
    exact (by decide : (37 : ℤ) ≠ 0) this
  · simp only [coefficientEquiv_mk, map_add, map_mul, constantCoeff_X, constantCoeff_C,
      zero_mul, zero_add]

/-- A nonzero square-zero coefficient remains nonzero with square zero after
quotienting by the variable span, in every degree over `ZMod 4`. -/
private theorem mod_four_all_degrees (n : ℕ) :
    let c := @algebraMap (ZMod 4)
      ((Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ⧸
        Ideal.span (Set.range (fun i : Fin (n + 1) =>
          Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) n) (X i))))
      inferInstance
      (Ideal.Quotient.semiring (Ideal.span (Set.range (fun i : Fin (n + 1) =>
        Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) n) (X i)))))
      (Ideal.Quotient.algebra (ZMod 4)
        (I := Ideal.span (Set.range (fun i : Fin (n + 1) =>
          Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) n) (X i))))) (2 : ZMod 4)
    c ≠ 0 ∧ c ^ 2 = 0 ∧ coefficientEquiv (ZMod 4) n c = 2 := by
  dsimp only
  have hvalue := (coefficient_roundtrip (ZMod 4) n (2 : ZMod 4)).1
  refine ⟨?_, ?_, hvalue⟩
  · intro hzero
    have h := congrArg (coefficientEquiv (ZMod 4) n) hzero
    rw [hvalue, map_zero] at h
    exact (by decide : (2 : ZMod 4) ≠ 0) h
  · apply (coefficientEquiv (ZMod 4) n).injective
    rw [map_pow, hvalue, map_zero]
    decide

/-- With zero coefficients the variable span is the unit ideal, and every
variable class vanishes in its quotient, for arbitrary degree. -/
private theorem zero_coefficients_all_degrees (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin (n + 1) =>
      Ideal.Quotient.mkₐ (ZMod 1) (hankelIdeal (ZMod 1) n) (X i))) = ⊤ ∧
      ∀ i : Fin (n + 1), Ideal.Quotient.mk
        (Ideal.span (Set.range (fun j : Fin (n + 1) =>
          Ideal.Quotient.mkₐ (ZMod 1) (hankelIdeal (ZMod 1) n) (X j))))
        (Ideal.Quotient.mkₐ (ZMod 1) (hankelIdeal (ZMod 1) n) (X i)) = 0 := by
  constructor
  · apply (Ideal.eq_top_iff_one _).mpr
    rw [mem_span_quotient_X_iff]
    exact Subsingleton.elim _ _
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_range_self i)

/-- The conic parametrization has the prescribed constant coefficient on every
class of the full integer Hankel quotient. -/
private theorem integer_conic_constantCoeff (q : Source ℤ 2 ⧸ hankelIdeal ℤ 2) :
    constantCoeff (quotientMap ℤ 2 q) = quotientAugmentation ℤ 2 q := by
  exact RingHom.congr_fun (constantCoeff_comp_quotientMap ℤ 2 (by decide)) q

/-- The retained degree-zero integer variable distinguishes the parametrization
constant coefficient from the coefficient augmentation. -/
private theorem integer_degree_zero_incompatible :
    Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      (constantCoeff : Target ℤ →+* ℤ).comp (quotientMap ℤ 0).toRingHom ≠
        (quotientAugmentation ℤ 0).toRingHom := by
  refine ⟨integer_degree_zero.1, ?_⟩
  intro h
  have hx := RingHom.congr_fun h
    (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)))
  change constantCoeff (quotientMap ℤ 0
    (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)))) =
      quotientAugmentation ℤ 0
        (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1))) at hx
  have hone : (1 : ℤ) = 0 := by
    simpa [quotientMap_mk, rncMap_X, coordinateExponent] using hx
  exact one_ne_zero hone

/-- A concrete integer conic class has nonzero raw coordinate `37` and is
`37` times the prescribed variable vector for the canonical coefficient action. -/
private theorem integer_conic_cotangent_witness :
    ∃ z : (RingHom.ker (quotientAugmentation ℤ 2).toRingHom).Cotangent,
      z = (37 : ℤ) • quotientAugmentationCotangentBasis ℤ 2 (0 : Fin 3) ∧
      (quotientAugmentationCotangentBasis ℤ 2).repr z (0 : Fin 3) = 37 ∧ z ≠ 0 := by
  let p : Source ℤ 2 := (37 : ℤ) • X (0 : Fin 3)
  have hp : constantCoeff p = 0 := by simp [p]
  let z := (RingHom.ker (quotientAugmentation ℤ 2).toRingHom).toCotangent
    ⟨Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 2) p, by
      apply RingHom.mem_ker.mpr
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Ideal.Quotient.mkₐ_eq_mk, quotientAugmentation_mk] using hp⟩
  have hcoord : (quotientAugmentationCotangentBasis ℤ 2).repr z (0 : Fin 3) = 37 := by
    simpa only [z, p, coeff_smul, coeff_X_same, smul_eq_mul, mul_one] using
      quotientAugmentationCotangentBasis_repr_mk ℤ 2 p hp (0 : Fin 3)
  refine ⟨z, ?_, hcoord, ?_⟩
  · rw [quotientAugmentationCotangentBasis_apply]
    change ((RingHom.ker (quotientAugmentation ℤ 2).toRingHom).toCotangent.restrictScalars ℤ)
      _ = (37 : ℤ) •
        ((RingHom.ker (quotientAugmentation ℤ 2).toRingHom).toCotangent.restrictScalars ℤ) _
    rw [← map_smul]
    congr 1
  · intro hzero
    have hbad : (37 : ℤ) = 0 := by
      simpa only [hzero, map_zero, Finsupp.zero_apply] using hcoord.symm
    exact (by decide : (37 : ℤ) ≠ 0) hbad

/-- At degree zero the full polynomial quotient has the nonzero cotangent
vector `[X₀]`, as detected by its raw coefficient `1`. -/
private theorem integer_degree_zero_cotangent :
    hankelIdeal ℤ 0 = ⊥ ∧ quotientAugmentationCotangentBasis ℤ 0 (0 : Fin 1) ≠ 0 := by
  refine ⟨hankelIdeal_zero ℤ, ?_⟩
  have hcoord : (quotientAugmentationCotangentBasis ℤ 0).repr
      (quotientAugmentationCotangentBasis ℤ 0 (0 : Fin 1)) (0 : Fin 1) = 1 := by
    rw [quotientAugmentationCotangentBasis_apply]
    simpa only [coeff_X_same] using
      quotientAugmentationCotangentBasis_repr_mk ℤ 0 (X (0 : Fin 1))
        (by simp only [constantCoeff_X]) (0 : Fin 1)
  intro hzero
  have hbad : (0 : ℤ) = 1 := by
    simpa only [hzero, map_zero, Finsupp.zero_apply] using hcoord
  exact (by decide : (0 : ℤ) ≠ 1) hbad

/-- A zero coefficient ring permits a basis indexed by all variables even
though each vector vanishes; no numerical rank is asserted. -/
private theorem zero_coefficients_cotangent_vectors (n : ℕ) (i : Fin (n + 1)) :
    quotientAugmentationCotangentBasis (ZMod 1) n i = 0 := by
  apply (quotientAugmentationCotangentBasis (ZMod 1) n).repr.injective
  ext j
  exact Subsingleton.elim _ _

/-- A nonzero square-zero coefficient does not annihilate the conic's first
cotangent basis vector under the canonical coefficient action. -/
private theorem mod_four_cotangent_scalar :
    (2 : ZMod 4) ^ 2 = 0 ∧
      (2 : ZMod 4) • quotientAugmentationCotangentBasis (ZMod 4) 2 (0 : Fin 3) ≠ 0 := by
  refine ⟨by decide, ?_⟩
  intro hzero
  have hcoord := congrArg
    (fun z => (quotientAugmentationCotangentBasis (ZMod 4) 2).repr z (0 : Fin 3)) hzero
  have hbad : (2 : ZMod 4) = 0 := by
    simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero, Finsupp.zero_apply] using hcoord
  exact (by decide : (2 : ZMod 4) ≠ 0) hbad

end

end ToricIdeals.RationalNormalCurve.AugmentationKernelModels
