/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals
import ToricIdeals.RationalNormalCurve.GradedAlgebra
import Mathlib.Algebra.Algebra.Operations

/-!
# Clients of homogeneous Hankel-quotient coordinates

These examples use the public basis and coordinate API. They reconstruct a
bivariate polynomial, check a conic relation by its five coordinates, and
retain a nonzero square-zero coefficient in a positive-degree component.
The one-variable and zero-coefficient boundaries use the full quotient.

The integer conic also uses the standard grading through its degree-zero ring
homomorphism and coefficient-augmentation compatibility. The parameter-zero
variable has homogeneous degree one, and degree zero retains nilpotent
coefficients. These operations also apply over the zero coefficient ring.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve.HomogeneousBasisExamples

noncomputable section

universe u

private theorem oneVariable_power_coordinate (R : Type u) [CommRing R] (d : ℕ) (r : R) :
    (quotientHomogeneousBasis R 0 d).repr
      (quotientHomogeneousRepresentative R 0 d (C r * X 0 ^ d)
        (isHomogeneous_C_mul_X_pow r 0 d)) 0 = r := by
  rw [quotientHomogeneousBasis_repr_representative_zero]
  simp [X_pow_eq_monomial]

private theorem oneVariable_power_reconstruction (d : ℕ) (r : ℤ) :
    (quotientHomogeneousRepresentative ℤ 0 d (C r * X 0 ^ d)
      (isHomogeneous_C_mul_X_pow r 0 d) : Source ℤ 0 ⧸ hankelIdeal ℤ 0) =
        r • Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (X 0 ^ d) := by
  rw [quotientHomogeneousRepresentative_coe, map_mul,
    eq_intCast (C : ℤ →+* Source ℤ 0) r, map_intCast, zsmul_eq_mul]

-- Finite coordinates also reflect coefficients in the constant component.
private theorem constant_coefficient_injective (R : Type u) [CommRing R] (n : ℕ)
    (r s : R)
    (h : Ideal.Quotient.mkₐ R (hankelIdeal R n) (C r) =
      Ideal.Quotient.mkₐ R (hankelIdeal R n) (C s)) : r = s := by
  have hx : quotientHomogeneousRepresentative R n 0 (C r)
      (isHomogeneous_C (Fin (n + 1)) r) =
      quotientHomogeneousRepresentative R n 0 (C s)
        (isHomogeneous_C (Fin (n + 1)) s) := Subtype.ext h
  have hc := congrArg (fun x => (quotientHomogeneousBasis R n 0).repr x 0) hx
  simpa only [quotientHomogeneousBasis_repr_C] using hc

private def quadratic : Source ℤ 1 := C 3 * X 0 ^ 2 + X 0 * X 1 + C (-2) * X 1 ^ 2

private theorem quadratic_homogeneous : quadratic.IsHomogeneous 2 :=
  ((isHomogeneous_C_mul_X_pow 3 0 2).add
    ((isHomogeneous_X ℤ 0).mul (isHomogeneous_X ℤ 1))).add
      (isHomogeneous_C_mul_X_pow (-2) 1 2)

private theorem quadratic_coordinates :
    quotientHomogeneousCoordinates ℤ 1 2
      (quotientHomogeneousRepresentative ℤ 1 2 quadratic quadratic_homogeneous) =
        ![3, 1, -2] := by
  ext i
  rw [quotientHomogeneousCoordinates_apply,
    quotientHomogeneousBasis_repr_representative_of_pos ℤ 1 2 (by decide)]
  simp only [quadratic, rncMap_one, RingHom.id_apply, C_mul_X_pow_eq_monomial]
  simp only [X, monomial_mul_monomial, mul_one]
  fin_cases i <;> simp [Finsupp.ext_iff, Fin.forall_fin_two]

private theorem quadratic_reconstruction :
    quotientHomogeneousRepresentative ℤ 1 2 quadratic quadratic_homogeneous =
      3 • quotientHomogeneousBasis ℤ 1 2 0 + quotientHomogeneousBasis ℤ 1 2 1 -
        2 • quotientHomogeneousBasis ℤ 1 2 2 := by
  apply (quotientHomogeneousBasis ℤ 1 2).repr.injective
  ext i
  have hc := congrFun quadratic_coordinates i
  rw [quotientHomogeneousCoordinates_apply] at hc
  rw [hc]
  fin_cases i <;> simp

private def conicLeft : quotientHomogeneousSubmodule (ZMod 4) 2 2 :=
  quotientHomogeneousRepresentative (ZMod 4) 2 2 (X 0 * X 2)
    ((isHomogeneous_X (ZMod 4) 0).mul (isHomogeneous_X (ZMod 4) 2))

private def conicRight : quotientHomogeneousSubmodule (ZMod 4) 2 2 :=
  quotientHomogeneousRepresentative (ZMod 4) 2 2 (X 1 ^ 2)
    (isHomogeneous_X_pow 1 2)

-- This equality is checked through the finite coordinate equivalence, not by
-- unfolding the Hankel ideal or inserting a relation as a hypothesis.
private theorem conic_relation_from_coordinates : conicLeft = conicRight := by
  apply quotientHomogeneousCoordinates_ext (ZMod 4) 2 2
  intro i
  simp only [quotientHomogeneousCoordinates_apply, conicLeft, conicRight,
    quotientHomogeneousBasis_repr_representative_of_pos (ZMod 4) 2 2 (by decide)]
  fin_cases i <;>
    simp [map_mul, map_pow, rncMap_X, coordinateExponent, monomial_mul_monomial,
      monomial_pow, Finsupp.ext_iff, Fin.forall_fin_two]

private def conicNilpotent : quotientHomogeneousSubmodule (ZMod 4) 2 2 :=
  quotientHomogeneousRepresentative (ZMod 4) 2 2 (C 2 * X 0 ^ 2)
    (isHomogeneous_C_mul_X_pow 2 0 2)

private theorem conic_nilpotent_coordinates :
    quotientHomogeneousCoordinates (ZMod 4) 2 2 conicNilpotent = ![2, 0, 0, 0, 0] := by
  ext i
  rw [quotientHomogeneousCoordinates_apply]
  simp only [conicNilpotent,
    quotientHomogeneousBasis_repr_representative_of_pos (ZMod 4) 2 2 (by decide)]
  fin_cases i <;>
    simp [map_mul, map_pow, rncMap_C, rncMap_X, coordinateExponent, monomial_pow,
      C_mul_monomial, Finsupp.ext_iff, Fin.forall_fin_two]

private theorem conic_nilpotent_reconstruction :
    conicNilpotent = (2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) 2 2 0 := by
  have h := (quotientHomogeneousCoordinates (ZMod 4) 2 2).symm_apply_apply conicNilpotent
  rw [conic_nilpotent_coordinates, quotientHomogeneousCoordinates_symm_apply] at h
  simpa [Fin.sum_univ_succ] using h.symm

private theorem conic_nilpotent_nonzero_and_square_zero :
    conicNilpotent ≠ 0 ∧
      (conicNilpotent : Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) ^ 2 = 0 := by
  constructor
  · intro hzero
    have hc := congrFun conic_nilpotent_coordinates 0
    rw [hzero, map_zero] at hc
    exact (by decide : (2 : ZMod 4) ≠ 0) (by simpa using hc.symm)
  · have hb :
        (quotientHomogeneousBasis (ZMod 4) 2 2 0 :
          Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) ^ 2 =
        (quotientHomogeneousBasis (ZMod 4) 2 4 0 :
          Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) := by
      simpa [pow_two] using quotientHomogeneousBasis_mul (ZMod 4) 2 2 2 0 0
    have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
    rw [conic_nilpotent_reconstruction, Submodule.coe_smul,
      Algebra.smul_def (2 : ZMod 4)
        (quotientHomogeneousBasis (ZMod 4) 2 2 0 :
          Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2),
      mul_pow, hb, ← map_pow, hsq, map_zero, zero_mul]

-- This reconstruction uses internality; the nonzero nilpotent example above
-- uses only the basis and product API, independently of this decomposition.
private theorem conic_finite_homogeneous_reconstruction
    (q : Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) :
    ∃ (degrees : Finset ℕ)
      (components : DirectSum ℕ (fun d => ↥(quotientHomogeneousSubmodule (ZMod 4) 2 d))),
      (∑ d ∈ degrees,
        (components d : Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2)) = q := by
  classical
  let _ : DirectSum.Decomposition (quotientHomogeneousSubmodule (ZMod 4) 2) :=
    (quotientHomogeneousSubmodule_isInternal (ZMod 4) 2).chooseDecomposition
  let components := DirectSum.decompose (quotientHomogeneousSubmodule (ZMod 4) 2) q
  exact ⟨components.support, components,
    DirectSum.sum_support_decompose (quotientHomogeneousSubmodule (ZMod 4) 2) q⟩

private theorem zeroCoefficient_vectors_coincide :
    quotientHomogeneousBasis (ZMod 1) 2 2 0 = quotientHomogeneousBasis (ZMod 1) 2 2 1 :=
  Subsingleton.elim _ _

private theorem zeroCoefficient_inverse_coordinates (n d : ℕ) :
    (quotientHomogeneousCoordinates (ZMod 1) n d).symm (fun _ => 0) = 0 :=
  (quotientHomogeneousCoordinates (ZMod 1) n d).symm.map_zero

private theorem integer_conic_zero_piece :
    quotientHomogeneousSubmodule ℤ 2 0 =
      (1 : Submodule ℤ (Source ℤ 2 ⧸ hankelIdeal ℤ 2)) := by
  simpa only [quotientHomogeneousSubmodule, MvPolynomial.homogeneousSubmodule_zero] using
    (Submodule.map_one (Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 2)))

private theorem integer_conic_zero_projection_augmentation
    (q : Source ℤ 2 ⧸ hankelIdeal ℤ 2) :
    GradedRing.projZeroRingHom (quotientHomogeneousSubmodule ℤ 2) q =
      algebraMap ℤ (Source ℤ 2 ⧸ hankelIdeal ℤ 2) (quotientAugmentation ℤ 2 q) :=
  RingHom.congr_fun (quotientHomogeneous_projZeroRingHom ℤ 2) q

private theorem integer_zero_parameter :
    Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1)) ∈
        quotientHomogeneousSubmodule ℤ 0 1 ∧
      GradedRing.projZeroRingHom (quotientHomogeneousSubmodule ℤ 0)
        (Ideal.Quotient.mkₐ ℤ (hankelIdeal ℤ 0) (MvPolynomial.X (0 : Fin 1))) = 0 ∧
      GradedRing.projZeroRingHom (quotientHomogeneousSubmodule ℤ 0) 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hankelIdeal_zero] at hmem
    exact MvPolynomial.X_ne_zero (R := ℤ) (0 : Fin 1) (Ideal.mem_bot.mp hmem)
  · exact (mem_quotientHomogeneousSubmodule_iff ℤ 0 1 _).mpr
      ⟨MvPolynomial.X 0, isHomogeneous_X ℤ 0, rfl⟩
  · rw [quotientHomogeneous_projZeroRingHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Ideal.Quotient.mkₐ_eq_mk,
      quotientAugmentation_mk, MvPolynomial.constantCoeff_X, map_zero]
  · exact map_one _

private theorem mod_four_nilpotent_coefficient :
    algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2 ≠ 0 ∧
      algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2 *
        algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2 = 0 ∧
      GradedRing.projZeroRingHom (quotientHomogeneousSubmodule (ZMod 4) 2)
        (algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2) =
          algebraMap (ZMod 4) (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have htwo : (2 : ZMod 4) = 0 := by
      simpa only [AlgHom.commutes, Algebra.algebraMap_self_apply, map_zero] using
        congrArg (quotientAugmentation (ZMod 4) 2) hzero
    exact (by decide : (2 : ZMod 4) ≠ 0) htwo
  · have hsq : (2 : ZMod 4) * (2 : ZMod 4) = 0 := by decide
    rw [← map_mul, hsq, map_zero]
  · rw [quotientHomogeneous_projZeroRingHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
      Algebra.algebraMap_self_apply]

private theorem zero_coefficients :
    GradedRing.projZeroRingHom (quotientHomogeneousSubmodule (ZMod 1) 0)
      (Ideal.Quotient.mkₐ (ZMod 1) (hankelIdeal (ZMod 1) 0)
        (MvPolynomial.X (0 : Fin 1))) = 0 := by
  exact Subsingleton.elim _ _

end

end ToricIdeals.RationalNormalCurve.HomogeneousBasisExamples
