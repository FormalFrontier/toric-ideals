/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.RingTheory.Artinian.Module
import ToricIdeals.RationalNormalCurve
import ToricIdealsTest.RationalNormalCurveDomainModels

/-!
# Integer-product Artinian models for rational normal curves

The complementary idempotents `(1, 0)` and `(0, 1)` of `ℤ × ℤ` survive as
nonzero constant classes in every Hankel quotient, and their product is zero.
These quotients are not Artinian: constant coefficient followed by the first
projection induces a surjection onto `ℤ`, where `2` is regular but not a unit.

The quotient is the full polynomial presentation modulo the Hankel ideal,
including in degrees zero and one. No reducedness or domain assumption is
needed for the orthogonal constant classes.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  polynomial presentation and Hankel minors.
* Formal Frontier Agents, `ToricIdealsTest.RationalNormalCurveDomainModels`,
  supplies the complementary integer-product coefficient idempotents.
* Mathlib contributors, `Mathlib.RingTheory.Artinian.Module`, supplies
  surjective transfer of Artinian rings and the regular-unit criterion.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve.ArtinianModels

/-- The regular nonunit `2` prevents the integers from being Artinian. -/
private theorem integer_coefficients_not_artinian : ¬ IsArtinianRing ℤ := by
  intro hZ
  let : IsArtinianRing ℤ := hZ
  have hregular : IsRegular (2 : ℤ) := IsRegular.of_ne_zero (by decide)
  have hnonunit : ¬ IsUnit (2 : ℤ) := by
    rw [Int.isUnit_iff]
    decide
  exact hnonunit (IsArtinianRing.isUnit_iff_isRegular.mpr hregular)

/-- Every integer-product Hankel quotient has nonzero orthogonal constant
classes and is not Artinian. -/
private theorem integer_product_quotients_not_artinian (n : ℕ) :
    ((1, 0) : ℤ × ℤ) ≠ 0 ∧
      ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
        (MvPolynomial.C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
        (MvPolynomial.C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((1, 0) : ℤ × ℤ)) *
        Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
          (MvPolynomial.C ((0, 1) : ℤ × ℤ)) = 0 ∧
      ¬ IsArtinianRing (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := by
  let e : Source (ℤ × ℤ) n →+* (ℤ × ℤ) := MvPolynomial.constantCoeff
  have hI : hankelIdeal (ℤ × ℤ) n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [e, hankelMinor, map_sub, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero, sub_self]
  let g : (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) →+* (ℤ × ℤ) :=
    Ideal.Quotient.lift (hankelIdeal (ℤ × ℤ) n) e
      (fun _ hf => RingHom.mem_ker.mp (hI hf))
  have hg : Function.Surjective g := by
    intro c
    refine ⟨Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n) (MvPolynomial.C c), ?_⟩
    simp only [g, Ideal.Quotient.lift_mk, e, MvPolynomial.constantCoeff_C]
  have hcoeff := DomainModels.product_coefficients.2
  refine ⟨hcoeff.1, hcoeff.2.1, hcoeff.2.2, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hcoeff.1
    have he := RingHom.mem_ker.mp (hI (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    simpa only [e, MvPolynomial.constantCoeff_C] using he
  · intro hzero
    apply hcoeff.2.1
    have he := RingHom.mem_ker.mp (hI (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    simpa only [e, MvPolynomial.constantCoeff_C] using he
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ ↦ Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) n)
        (MvPolynomial.C c)) hcoeff.2.2
  · intro hQ
    let : IsArtinianRing (Source (ℤ × ℤ) n ⧸ hankelIdeal (ℤ × ℤ) n) := hQ
    have hfst : Function.Surjective (RingHom.fst ℤ ℤ) := by
      intro z
      exact ⟨(z, 0), rfl⟩
    have hsurj : Function.Surjective ((RingHom.fst ℤ ℤ).comp g) := hfst.comp hg
    exact integer_coefficients_not_artinian hsurj.isArtinianRing

#print axioms ToricIdeals.RationalNormalCurve.ArtinianModels.integer_product_quotients_not_artinian

end ToricIdeals.RationalNormalCurve.ArtinianModels
