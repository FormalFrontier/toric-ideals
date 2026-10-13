/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import ToricIdeals.RationalNormalCurve

/-!
# Polynomial and tensor-quotient examples over `ZMod 4`

These examples compute the polynomial tensor equivalence on a two-variable
linear form and the tensor-quotient equivalence on a degree-two coordinate.
They also transport the degree-two Hankel ideal through the right inclusion
and the polynomial tensor equivalence. All actions are the canonical ones.

The computations reuse Mathlib's polynomial tensor formalization by Antoine
Chambert-Loir, its tensor-quotient formalization by Christian Merten, Yi Song
and Sihan Su, and the coefficient-transport lemmas of the rational-normal-curve
formalization by Formal Frontier Agents.

## Implementation notes

The examples concern the polynomial and tensor-quotient equivalences separately;
they do not construct an equivalence of the two Hankel quotients.
-/

open TensorProduct

namespace ToricIdeals.RationalNormalCurve.BaseChangeTensorModels

/-- The polynomial tensor equivalence computes a scalar multiple of a linear form. -/
private theorem mod_four_polynomial_tensor_linear_form :
    MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) ℤ (ZMod 4)
        ((2 : ZMod 4) ⊗ₜ[ℤ]
          (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) : Source ℤ 1)) =
      MvPolynomial.C (2 : ZMod 4) *
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) := by
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_add,
    MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.smul_eq_C_mul]

/-- The tensor-quotient equivalence computes a scalar times the right inclusion. -/
private theorem mod_four_tensor_quotient_coordinate :
    Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ) (ZMod 4) (Source ℤ 2)
        (ZMod 4) (hankelIdeal ℤ 2)
        ((2 : ZMod 4) ⊗ₜ[ℤ]
          Ideal.Quotient.mk (hankelIdeal ℤ 2) (MvPolynomial.X (0 : Fin 3))) =
      Ideal.Quotient.mk
        ((hankelIdeal ℤ 2).map
          (Algebra.TensorProduct.includeRight (A := ZMod 4) (B := Source ℤ 2)
            (R := ℤ)).toRingHom)
        (algebraMap (ZMod 4) ((ZMod 4) ⊗[ℤ] Source ℤ 2) (2 : ZMod 4) *
          Algebra.TensorProduct.includeRight (A := ZMod 4) (B := Source ℤ 2)
            (R := ℤ) (MvPolynomial.X (0 : Fin 3))) := by
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  congr 1
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- Extending the conic ideal through the tensor inclusion gives the conic ideal
modulo four. -/
private theorem mod_four_conic_tensor_ideal_transport :
    ((hankelIdeal ℤ 2).map
        (Algebra.TensorProduct.includeRight (A := ZMod 4) (B := Source ℤ 2)
          (R := ℤ)).toRingHom).map
        (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 3) ℤ (ZMod 4)).toRingHom =
      hankelIdeal (ZMod 4) 2 := by
  have h :
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 3) ℤ (ZMod 4)).toRingHom.comp
          (Algebra.TensorProduct.includeRight (A := ZMod 4) (B := Source ℤ 2)
            (R := ℤ)).toRingHom =
        MvPolynomial.map (algebraMap ℤ (ZMod 4)) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv (σ := Fin 3) ℤ (ZMod 4)
        (Algebra.TensorProduct.includeRight (A := ZMod 4) (B := Source ℤ 2)
          (R := ℤ) p) = MvPolynomial.map (algebraMap ℤ (ZMod 4)) p
    rw [Algebra.TensorProduct.includeRight_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rw [Ideal.map_map, h]
  exact map_hankelIdeal (algebraMap ℤ (ZMod 4)) 2

end ToricIdeals.RationalNormalCurve.BaseChangeTensorModels
