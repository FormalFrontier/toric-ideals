/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.FinCases
import ToricIdeals.RationalNormalCurve

/-!
# Flatness models for the rational-normal-curve parametrization

These models concern the whole two-variable target as a module over the
whole source through `rncMap`, not its coefficient module or its image.

The degree-one map is the identity. The zero coefficient ring gives flat
maps at degrees zero and two. Over the integers, the degree-zero relation
`X₀ - 1` and the degree-two and degree-three relations `X₁² - X₀ X₂`
obstruct flatness. Selecting a polynomial variable makes these relations
monic, so the same degree-two obstruction works over `ZMod 4` and `ℤ × ℤ`
without a domain assumption. The former has the nonzero square-zero element
`2`; the latter is reduced but has nonzero orthogonal elements. A lifted
integer ring supplies a degree-one model in an independent universe.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the source,
  target, exponent map, and coefficient and variable formulas.
* Mathlib contributors, `Mathlib.RingTheory.RingHom.Flat` and
  `Mathlib.RingTheory.Flat.TorsionFree`, for flat maps, the canonical module
  bridge, and regular scalars acting injectively on flat modules.
* Mathlib contributors, `Mathlib.Algebra.Polynomial.Monic`,
  `Mathlib.Algebra.MvPolynomial.Equiv`, and
  `Mathlib.Algebra.Regular.SMul`, for monic regularity, polynomial-variable
  equivalences, and transport of injective scalar actions.
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.FlatnessModels

noncomputable section

universe u

/-- At degree one, the exponent identity gives the identity on polynomial rings. -/
private theorem degree_one_map_eq_id (R : Type u) [CommRing R] :
    rncMap R 1 = RingHom.id (Target R) := by
  have hexponent : rncExponent 1 = AddMonoidHom.id (Fin 2 →₀ ℕ) := by
    apply AddMonoidHom.ext
    exact rncExponent_one
  rw [rncMap, hexponent, AddMonoidAlgebra.mapDomainRingHom_id]

/-- The zero coefficient ring has flat parametrizations in every degree. -/
private theorem zero_coefficients_flat (n : ℕ) : (rncMap (ZMod 1) n).Flat := by
  let : Algebra (Source (ZMod 1) n) (Target (ZMod 1)) :=
    (rncMap (ZMod 1) n).toAlgebra
  have hflat : (algebraMap (Source (ZMod 1) n) (Target (ZMod 1))).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  simpa only [RingHom.algebraMap_toAlgebra] using hflat

private theorem zero_coefficients_degree_zero :
    Subsingleton (Source (ZMod 1) 0) ∧ Subsingleton (Target (ZMod 1)) ∧
      (rncMap (ZMod 1) 0).Flat :=
  ⟨inferInstance, inferInstance, zero_coefficients_flat 0⟩

private theorem zero_coefficients_degree_two :
    Subsingleton (Source (ZMod 1) 2) ∧ Subsingleton (Target (ZMod 1)) ∧
      (rncMap (ZMod 1) 2).Flat :=
  ⟨inferInstance, inferInstance, zero_coefficients_flat 2⟩

private theorem integer_degree_one :
    rncMap ℤ 1 = RingHom.id (Target ℤ) ∧ (rncMap ℤ 1).Flat := by
  refine ⟨degree_one_map_eq_id ℤ, ?_⟩
  rw [degree_one_map_eq_id]
  exact RingHom.Flat.id (Target ℤ)

private theorem mod_four_degree_one : (rncMap (ZMod 4) 1).Flat := by
  rw [degree_one_map_eq_id]
  exact RingHom.Flat.id (Target (ZMod 4))

private theorem lifted_integer_degree_one : (rncMap (ULift.{u + 1} ℤ) 1).Flat := by
  rw [degree_one_map_eq_id]
  exact RingHom.Flat.id (Target (ULift.{u + 1} ℤ))

/-- The degree-zero relation is monic in its sole variable and has zero image. -/
private theorem integer_degree_zero_relation :
    IsRegular (X (0 : Fin 1) - C 1 : Source ℤ 0) ∧
      rncMap ℤ 0 (X (0 : Fin 1) - C 1) = 0 := by
  constructor
  · let p : Source ℤ 0 := X 0 - C 1
    let e := MvPolynomial.finSuccEquiv ℤ 0
    have hregular : IsRegular (e p) := by
      simpa [p, e, MvPolynomial.finSuccEquiv_X_zero] using
        (Polynomial.monic_X_sub_C (1 : MvPolynomial (Fin 0) ℤ)).isRegular
    have hleft : IsLeftRegular p :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv) (r := p) (s := e p)
        (fun q => e.map_mul p q)).mpr hregular.left
    exact ⟨hleft, hleft.right_of_commute (fun q => mul_comm p q)⟩
  · simp [rncMap_X, coordinateExponent]

/-- Swapping the first two variables exhibits the conic relation as monic,
without imposing any condition on the coefficient ring. -/
private theorem degree_two_relation (R : Type u) [CommRing R] :
    IsRegular (X (1 : Fin 3) ^ 2 - X 0 * X 2 : Source R 2) ∧
      rncMap R 2 (X (1 : Fin 3) ^ 2 - X 0 * X 2) = 0 := by
  constructor
  · let p : Source R 2 := X 1 ^ 2 - X 0 * X 2
    let e := (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 3) 1)).trans
      (MvPolynomial.finSuccEquiv R 2)
    have hx0 : e (X (0 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_left, Fin.succ_zero_eq_one'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := R) (j := (0 : Fin 2)))
    have hx1 : e (X (1 : Fin 3)) = Polynomial.X := by
      simp only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero]
    have hswap : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    have hx2 : e (X (2 : Fin 3)) = Polynomial.C (X (1 : Fin 2)) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, hswap, Fin.succ_one_eq_two'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := R) (j := (1 : Fin 2)))
    have he : e p = Polynomial.X ^ 2 -
        Polynomial.C (X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) R) := by
      simp only [p, map_sub, map_pow, map_mul, hx0, hx1, hx2]
    have hregular : IsRegular (e p) := by
      rw [he]
      exact (Polynomial.monic_X_pow_sub_C _ (by decide : (2 : ℕ) ≠ 0)).isRegular
    have hleft : IsLeftRegular p :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv) (r := p) (s := e p)
        (fun q => e.map_mul p q)).mpr hregular.left
    exact ⟨hleft, hleft.right_of_commute (fun q => mul_comm p q)⟩
  · have hexponent : coordinateExponent 2 (1 : Fin 3) + coordinateExponent 2 1 =
        coordinateExponent 2 0 + coordinateExponent 2 2 := by
      ext i
      fin_cases i <;> simp [coordinateExponent]
    simp only [pow_two, map_sub, map_mul, rncMap_X,
      MvPolynomial.monomial_mul_monomial, one_mul]
    rw [hexponent, sub_self]

/-- The next integer degree has the same monic relation with its degree-three images. -/
private theorem integer_degree_three_relation :
    IsRegular (X (1 : Fin 4) ^ 2 - X 0 * X 2 : Source ℤ 3) ∧
      rncMap ℤ 3 (X (1 : Fin 4) ^ 2 - X 0 * X 2) = 0 := by
  constructor
  · let p : Source ℤ 3 := X 1 ^ 2 - X 0 * X 2
    let e := (MvPolynomial.renameEquiv ℤ (Equiv.swap (0 : Fin 4) 1)).trans
      (MvPolynomial.finSuccEquiv ℤ 3)
    have hx0 : e (X (0 : Fin 4)) = Polynomial.C (X (0 : Fin 3)) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_left, Fin.succ_zero_eq_one'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := ℤ) (j := (0 : Fin 3)))
    have hx1 : e (X (1 : Fin 4)) = Polynomial.X := by
      simp only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero]
    have hswap : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
    have hx2 : e (X (2 : Fin 4)) = Polynomial.C (X (1 : Fin 3)) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, hswap, Fin.succ_one_eq_two'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := ℤ) (j := (1 : Fin 3)))
    have he : e p = Polynomial.X ^ 2 -
        Polynomial.C (X (0 : Fin 3) * X 1 : MvPolynomial (Fin 3) ℤ) := by
      simp only [p, map_sub, map_pow, map_mul, hx0, hx1, hx2]
    have hregular : IsRegular (e p) := by
      rw [he]
      exact (Polynomial.monic_X_pow_sub_C _ (by decide : (2 : ℕ) ≠ 0)).isRegular
    have hleft : IsLeftRegular p :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv) (r := p) (s := e p)
        (fun q => e.map_mul p q)).mpr hregular.left
    exact ⟨hleft, hleft.right_of_commute (fun q => mul_comm p q)⟩
  · have hexponent : coordinateExponent 3 (1 : Fin 4) + coordinateExponent 3 1 =
        coordinateExponent 3 0 + coordinateExponent 3 2 := by
      ext i
      fin_cases i <;> simp [coordinateExponent]
    simp only [pow_two, map_sub, map_mul, rncMap_X,
      MvPolynomial.monomial_mul_monomial, one_mul]
    rw [hexponent, sub_self]

private theorem integer_degree_zero_not_flat : ¬ (rncMap ℤ 0).Flat := by
  intro hflat
  let : Algebra (Source ℤ 0) (Target ℤ) := (rncMap ℤ 0).toAlgebra
  let : Module.Flat (Source ℤ 0) (Target ℤ) :=
    RingHom.flat_algebraMap_iff.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
  let p : Source ℤ 0 := X 0 - C 1
  have hscalar : IsSMulRegular (Target ℤ) p :=
    Module.Flat.isSMulRegular_of_isRegular integer_degree_zero_relation.1
  have hkill : p • (1 : Target ℤ) = 0 := by
    rw [RingHom.smul_toAlgebra (rncMap ℤ 0),
      show rncMap ℤ 0 p = 0 from integer_degree_zero_relation.2, zero_mul]
  exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)

private theorem integer_degree_two_not_flat : ¬ (rncMap ℤ 2).Flat := by
  intro hflat
  let : Algebra (Source ℤ 2) (Target ℤ) := (rncMap ℤ 2).toAlgebra
  let : Module.Flat (Source ℤ 2) (Target ℤ) :=
    RingHom.flat_algebraMap_iff.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
  let p : Source ℤ 2 := X 1 ^ 2 - X 0 * X 2
  have hscalar : IsSMulRegular (Target ℤ) p :=
    Module.Flat.isSMulRegular_of_isRegular (degree_two_relation ℤ).1
  have hkill : p • (1 : Target ℤ) = 0 := by
    rw [RingHom.smul_toAlgebra (rncMap ℤ 2),
      show rncMap ℤ 2 p = 0 from (degree_two_relation ℤ).2, zero_mul]
  exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)

private theorem integer_degree_three_not_flat : ¬ (rncMap ℤ 3).Flat := by
  intro hflat
  let : Algebra (Source ℤ 3) (Target ℤ) := (rncMap ℤ 3).toAlgebra
  let : Module.Flat (Source ℤ 3) (Target ℤ) :=
    RingHom.flat_algebraMap_iff.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
  let p : Source ℤ 3 := X 1 ^ 2 - X 0 * X 2
  have hscalar : IsSMulRegular (Target ℤ) p :=
    Module.Flat.isSMulRegular_of_isRegular integer_degree_three_relation.1
  have hkill : p • (1 : Target ℤ) = 0 := by
    rw [RingHom.smul_toAlgebra (rncMap ℤ 3),
      show rncMap ℤ 3 p = 0 from integer_degree_three_relation.2, zero_mul]
  exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)

private theorem mod_four_nonzero_square_zero : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  constructor <;> decide

private theorem mod_four_target_nonzero_square_zero :
    (C (2 : ZMod 4) : Target (ZMod 4)) ≠ 0 ∧
      (C (2 : ZMod 4) : Target (ZMod 4)) ^ 2 = 0 := by
  constructor
  · intro hzero
    exact mod_four_nonzero_square_zero.1 (MvPolynomial.C_eq_zero.mp hzero)
  · rw [← map_pow, mod_four_nonzero_square_zero.2, map_zero]

private theorem mod_four_degree_two_not_flat : ¬ (rncMap (ZMod 4) 2).Flat := by
  let : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  intro hflat
  let : Algebra (Source (ZMod 4) 2) (Target (ZMod 4)) := (rncMap (ZMod 4) 2).toAlgebra
  let : Module.Flat (Source (ZMod 4) 2) (Target (ZMod 4)) :=
    RingHom.flat_algebraMap_iff.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
  let p : Source (ZMod 4) 2 := X 1 ^ 2 - X 0 * X 2
  have hscalar : IsSMulRegular (Target (ZMod 4)) p :=
    Module.Flat.isSMulRegular_of_isRegular (degree_two_relation (ZMod 4)).1
  have hkill : p • (1 : Target (ZMod 4)) = 0 := by
    rw [RingHom.smul_toAlgebra (rncMap (ZMod 4) 2),
      show rncMap (ZMod 4) 2 p = 0 from (degree_two_relation (ZMod 4)).2, zero_mul]
  exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)

private theorem integer_product_reduced_with_zero_divisors :
    IsReduced (ℤ × ℤ) ∧ ((1, 0) : ℤ × ℤ) ≠ 0 ∧ ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro hzero
    exact one_ne_zero (congrArg Prod.snd hzero)
  · ext <;> simp

private theorem integer_product_degree_two_not_flat : ¬ (rncMap (ℤ × ℤ) 2).Flat := by
  intro hflat
  let : Algebra (Source (ℤ × ℤ) 2) (Target (ℤ × ℤ)) := (rncMap (ℤ × ℤ) 2).toAlgebra
  let : Module.Flat (Source (ℤ × ℤ) 2) (Target (ℤ × ℤ)) :=
    RingHom.flat_algebraMap_iff.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
  let p : Source (ℤ × ℤ) 2 := X 1 ^ 2 - X 0 * X 2
  have hscalar : IsSMulRegular (Target (ℤ × ℤ)) p :=
    Module.Flat.isSMulRegular_of_isRegular (degree_two_relation (ℤ × ℤ)).1
  have hkill : p • (1 : Target (ℤ × ℤ)) = 0 := by
    rw [RingHom.smul_toAlgebra (rncMap (ℤ × ℤ) 2),
      show rncMap (ℤ × ℤ) 2 p = 0 from (degree_two_relation (ℤ × ℤ)).2, zero_mul]
  exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)

end

end ToricIdeals.RationalNormalCurve.FlatnessModels
