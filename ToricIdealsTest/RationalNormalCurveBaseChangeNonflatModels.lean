/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import ToricIdeals.RationalNormalCurve

/-!
# Nonflat coefficient specialization of the conic Hankel quotient

Reduction from `ℤ` to `ZMod 4` is neither injective nor flat. On the degree-two
Hankel quotient, the canonical coefficient quotient map kills the nonzero
constant class `[C 4]`. It sends `[C 2]` to a nonzero square-zero class.
Constant-coefficient evaluation detects these classes without identifying the
quotient with the parametrization image.

The proofs reuse Mathlib's regular-scalar criterion for flat modules and its
constant-coefficient and quotient-map APIs. The coefficient-map applications
follow the rational-normal-curve root clients, and the constant-class arguments
follow the Artinian models, by Formal Frontier Agents.

Implementation notes: all fixtures are private and concern the fixed map
`ℤ → ZMod 4` and the degree-two quotient. No tensor equivalence is constructed,
and all coefficient and module actions are the canonical ones.
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

end

end ToricIdeals.RationalNormalCurve
