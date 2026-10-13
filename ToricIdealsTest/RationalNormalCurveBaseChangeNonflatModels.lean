/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.BaseChange

/-!
# Nonflat coefficient specialization of the conic Hankel quotient

Reduction from `ℤ` to `ZMod 4` is neither injective nor flat. On the degree-two
Hankel quotient, the canonical coefficient quotient map kills the nonzero
constant class `[C 4]`. It sends `[C 2]` to a nonzero square-zero class.
Constant-coefficient evaluation detects these classes without identifying the
quotient with the parametrization image. Along `ℤ → ZMod 4 → ZMod 2`, the
two-step and direct tensor base-change equivalences give the same nonzero
class `[1 + X₀]` in every degree. The nonzero square-zero constant `[C 2]`
over `ZMod 4` becomes zero after the second base change.

The proofs reuse Mathlib's regular-scalar criterion for flat modules and its
constant-coefficient and quotient-map APIs. The coefficient-map applications
follow the rational-normal-curve root clients, and the constant-class arguments
follow the Artinian models, by Formal Frontier Agents.

The tower computations use the public base-change coherence theorem and its
pure-tensor formula, together with Mathlib's `cancelBaseChange`. Nonzero
constants are detected through the public quotient-augmentation API.

Implementation notes: all fixtures are private. The first coefficient-map
fixtures concern `ℤ → ZMod 4` and degree two; the tensor-tower fixtures include
every degree and a zero target ring. All coefficient and module actions are
canonical, with the residue algebra structures supplied by `ZMod.castHom`.
-/

open MvPolynomial
open ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve

noncomputable section

private theorem mod_four_reduction_noninjective_nonflat :
    ¬ Function.Injective (algebraMap ℤ (ZMod 4)) ∧ ¬ Module.Flat ℤ (ZMod 4) := by
  constructor
  · intro hinj
    have hfour : algebraMap ℤ (ZMod 4) (4 : ℤ) =
        algebraMap ℤ (ZMod 4) (0 : ℤ) := by decide
    exact (by decide : (4 : ℤ) ≠ 0) (hinj hfour)
  · intro hflat
    let : Module.Flat ℤ (ZMod 4) := hflat
    have hregular : IsRegular (4 : ℤ) := IsRegular.of_ne_zero (by decide)
    have hinj : IsSMulRegular (ZMod 4) (4 : ℤ) :=
      Module.Flat.isSMulRegular_of_isRegular hregular
    have hfour : (4 : ℤ) • (1 : ZMod 4) = (4 : ℤ) • (0 : ZMod 4) := by decide
    exact (by decide : (1 : ZMod 4) ≠ 0) (hinj hfour)

private theorem integer_conic_constant_four_ne_zero :
    Ideal.Quotient.mk (hankelIdeal ℤ 2) (C (4 : ℤ)) ≠ 0 := by
  have hI : hankelIdeal ℤ 2 ≤
      RingHom.ker (MvPolynomial.constantCoeff : Source ℤ 2 →+* ℤ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero, sub_self]
  intro hzero
  have hfour : (4 : ℤ) = 0 := by
    simpa only [RingHom.mem_ker, MvPolynomial.constantCoeff_C] using
      hI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  exact (by decide : (4 : ℤ) ≠ 0) hfour

private theorem mod_four_conic_constant_two_nonzero_square_zero :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0 := by
  constructor
  · have hI : hankelIdeal (ZMod 4) 2 ≤
        RingHom.ker (MvPolynomial.constantCoeff : Source (ZMod 4) 2 →+* ZMod 4) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨p, rfl⟩
      apply RingHom.mem_ker.mpr
      simp only [hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
        mul_zero, sub_self]
    intro hzero
    have htwo : (2 : ZMod 4) = 0 := by
      simpa only [RingHom.mem_ker, MvPolynomial.constantCoeff_C] using
        hI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    exact (by decide : (2 : ZMod 4) ≠ 0) htwo
  · have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
    calc
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 =
          Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C ((2 : ZMod 4) ^ 2)) := by
        simp only [map_pow]
      _ = 0 := by rw [hsq, map_zero, map_zero]

private theorem mod_four_conic_quotient_specialization :
    let f := Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
      (MvPolynomial.map (algebraMap ℤ (ZMod 4)))
      (Ideal.le_comap_of_map_le (map_hankelIdeal (algebraMap ℤ (ZMod 4)) 2).le)
    (Ideal.Quotient.mk (hankelIdeal ℤ 2) (C (4 : ℤ)) ≠ 0 ∧
      f (Ideal.Quotient.mk (hankelIdeal ℤ 2) (C (4 : ℤ))) = 0) ∧
    (f (Ideal.Quotient.mk (hankelIdeal ℤ 2) (C (2 : ℤ))) =
        Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0) ∧
    ¬ Function.Injective f := by
  dsimp only
  have hfour : algebraMap ℤ (ZMod 4) (4 : ℤ) = 0 := by decide
  have hkill :
      Ideal.quotientMap (hankelIdeal (ZMod 4) 2)
        (MvPolynomial.map (algebraMap ℤ (ZMod 4)))
        (Ideal.le_comap_of_map_le (map_hankelIdeal (algebraMap ℤ (ZMod 4)) 2).le)
        (Ideal.Quotient.mk (hankelIdeal ℤ 2) (C (4 : ℤ))) = 0 := by
    rw [Ideal.quotientMap_mk, MvPolynomial.map_C, hfour, map_zero, map_zero]
  refine ⟨⟨integer_conic_constant_four_ne_zero, hkill⟩,
    ⟨?_, mod_four_conic_constant_two_nonzero_square_zero⟩, ?_⟩
  · have htwo : algebraMap ℤ (ZMod 4) (2 : ℤ) = (2 : ZMod 4) := by decide
    rw [Ideal.quotientMap_mk, MvPolynomial.map_C, htwo]
  · intro hinj
    apply integer_conic_constant_four_ne_zero
    apply hinj
    simpa only [map_zero] using hkill

section ResidueTower

open scoped TensorProduct

local instance : Algebra (ZMod 4) (ZMod 2) :=
  (ZMod.castHom (show 2 ∣ 4 from by decide) (ZMod 2)).toAlgebra

/-- Both routes along a nonflat coefficient tower give a nonzero class;
in degree zero this is still a class in the full polynomial quotient. -/
private theorem mod_four_to_two_coherent_class (n : ℕ) :
    (Algebra.TensorProduct.cancelBaseChange ℤ (ZMod 4) (ZMod 2) (ZMod 2)
        (Source ℤ n ⧸ hankelIdeal ℤ n)).trans
        (quotientBaseChangeAlgEquiv ℤ (ZMod 2) n)
        ((1 : ZMod 2) ⊗ₜ[ZMod 4]
          ((3 : ZMod 4) ⊗ₜ[ℤ] Ideal.Quotient.mk (hankelIdeal ℤ n)
            (C (1 : ℤ) + X (0 : Fin (n + 1))))) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 2) n)
        (C (1 : ZMod 2) + X (0 : Fin (n + 1))) ∧
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod 2 ≃ₐ[ZMod 2] ZMod 2)
        (quotientBaseChangeAlgEquiv ℤ (ZMod 4) n)).trans
        (quotientBaseChangeAlgEquiv (ZMod 4) (ZMod 2) n)
        ((1 : ZMod 2) ⊗ₜ[ZMod 4]
          ((3 : ZMod 4) ⊗ₜ[ℤ] Ideal.Quotient.mk (hankelIdeal ℤ n)
            (C (1 : ℤ) + X (0 : Fin (n + 1))))) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 2) n)
        (C (1 : ZMod 2) + X (0 : Fin (n + 1))) ∧
    Ideal.Quotient.mk (hankelIdeal (ZMod 2) n)
        (C (1 : ZMod 2) + X (0 : Fin (n + 1))) ≠ 0 ∧
    ¬ Module.Flat ℤ (ZMod 4) := by
  have hthree : algebraMap (ZMod 4) (ZMod 2) (3 : ZMod 4) = 1 := by decide
  have hdirect :
      (Algebra.TensorProduct.cancelBaseChange ℤ (ZMod 4) (ZMod 2) (ZMod 2)
          (Source ℤ n ⧸ hankelIdeal ℤ n)).trans
          (quotientBaseChangeAlgEquiv ℤ (ZMod 2) n)
          ((1 : ZMod 2) ⊗ₜ[ZMod 4]
            ((3 : ZMod 4) ⊗ₜ[ℤ] Ideal.Quotient.mk (hankelIdeal ℤ n)
              (C (1 : ℤ) + X (0 : Fin (n + 1))))) =
        Ideal.Quotient.mk (hankelIdeal (ZMod 2) n)
          (C (1 : ZMod 2) + X (0 : Fin (n + 1))) := by
    rw [AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.smul_def, hthree, mul_one, quotientBaseChangeAlgEquiv_tmul_mk]
    simp only [one_smul, map_add, MvPolynomial.map_X, map_one]
  refine ⟨hdirect, ?_, ?_, mod_four_reduction_noninjective_nonflat.2⟩
  · rw [← quotientBaseChangeAlgEquiv_tower ℤ (ZMod 4) (ZMod 2) n]
    exact hdirect
  · intro hzero
    have hone : (1 : ZMod 2) = 0 := by
      simpa only [quotientAugmentation_mk, map_add, MvPolynomial.constantCoeff_C,
        MvPolynomial.constantCoeff_X, add_zero, map_zero] using
          congrArg (quotientAugmentation (ZMod 2) n) hzero
    exact one_ne_zero hone

/-- Further tensor base change kills a nonzero square-zero class, rather than
merely comparing two maps on a zero source quotient. -/
private theorem mod_four_to_two_conic_nilpotent_boundary :
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ≠ 0 ∧
    Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4)) ^ 2 = 0 ∧
    quotientBaseChangeAlgEquiv (ZMod 4) (ZMod 2) 2
        ((1 : ZMod 2) ⊗ₜ[ZMod 4]
          Ideal.Quotient.mk (hankelIdeal (ZMod 4) 2) (C (2 : ZMod 4))) = 0 := by
  have htwo : algebraMap (ZMod 4) (ZMod 2) (2 : ZMod 4) = 0 := by decide
  refine ⟨mod_four_conic_constant_two_nonzero_square_zero.1,
    mod_four_conic_constant_two_nonzero_square_zero.2, ?_⟩
  rw [quotientBaseChangeAlgEquiv_tmul_mk, one_smul, MvPolynomial.map_C,
    htwo, map_zero, map_zero]

end ResidueTower

section ZeroTarget

open scoped TensorProduct

local instance : Algebra (ZMod 4) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 4 from by decide) (ZMod 1)).toAlgebra

/-- The scalar-tower square also applies to a zero target ring. The integer
constant being specialized is nonzero before either scalar extension. -/
private theorem mod_four_to_zero_coherent_constant :
    Ideal.Quotient.mk (hankelIdeal ℤ 0) (C (1 : ℤ)) ≠ 0 ∧
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod 1 ≃ₐ[ZMod 1] ZMod 1)
        (quotientBaseChangeAlgEquiv ℤ (ZMod 4) 0)).trans
        (quotientBaseChangeAlgEquiv (ZMod 4) (ZMod 1) 0)
        ((1 : ZMod 1) ⊗ₜ[ZMod 4]
          ((1 : ZMod 4) ⊗ₜ[ℤ] Ideal.Quotient.mk (hankelIdeal ℤ 0) (C (1 : ℤ)))) = 0 := by
  constructor
  · intro hzero
    have hone : (1 : ℤ) = 0 := by
      simpa only [quotientAugmentation_mk, MvPolynomial.constantCoeff_C, map_zero] using
        congrArg (quotientAugmentation ℤ 0) hzero
    exact one_ne_zero hone
  · rw [← quotientBaseChangeAlgEquiv_tower ℤ (ZMod 4) (ZMod 1) 0]
    exact Subsingleton.elim _ _

end ZeroTarget

end

end ToricIdeals.RationalNormalCurve
