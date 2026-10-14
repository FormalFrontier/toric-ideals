/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import ToricIdeals
import ToricIdeals.RationalNormalCurve.Homogeneous

/-!
# Homogeneous components of full Hankel quotients: independent models

The component used here is the image of the standard homogeneous polynomial
submodule under the coefficient-linear quotient map. It is a submodule of the
full quotient, not the image of the parametrization. All local constructions
use the existing coefficient action.

The one-variable and bivariate bottom-ideal models use the stock supported
monomial basis. The constant component is computed by the existing coefficient
augmentation. A separate conic model over `ZMod 4` uses target coefficients of
homogeneous quartics, retaining the nonzero square-zero coefficient `2` in a
positive-degree component. Zero coefficients and independently lifted integer
coefficients are also included. All model declarations are private.

The dependent `#check` records a prospective basis-data signature; it does not
define a basis for arbitrary `n` and `d`. A public component API would expose
homogeneous representatives and quotient membership, and a public basis would
need vector, coordinate and reconstruction formulas, not just freeness.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the full
  quotient, small-degree bottom ideals and the original exponent map.
* Mathlib contributors, supported monomial bases, standard homogeneous
  polynomials, submodule images and finite antidiagonal equivalences.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve.HomogeneousQuotientModels

noncomputable section

universe u v

-- This is a dependent function TYPE, with no basis-existence premise.
#check ((R : Type u) → [CommRing R] → (n d : ℕ) →
  Module.Basis (Fin (n * d + 1)) R
    ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
      (Ideal.Quotient.mkₐ R (hankelIdeal R n)).toLinearMap))

-- A private abbreviation of the stock object, not another grading or action.
private abbrev component (R : Type u) [CommRing R] (n d : ℕ) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
    (Ideal.Quotient.mkₐ R (hankelIdeal R n)).toLinearMap

private theorem component_mem_iff (R : Type u) [CommRing R] (n d : ℕ)
    (x : Source R n ⧸ hankelIdeal R n) :
    x ∈ component R n d ↔ ∃ p : Source R n,
      p.IsHomogeneous d ∧ Ideal.Quotient.mkₐ R (hankelIdeal R n) p = x :=
  Submodule.mem_map

private def representative (R : Type u) [CommRing R] (n d : ℕ)
    (p : Source R n) (hp : p.IsHomogeneous d) : component R n d :=
  ⟨Ideal.Quotient.mkₐ R (hankelIdeal R n) p, Submodule.mem_map_of_mem hp⟩

private theorem representative_coe (R : Type u) [CommRing R] (n d : ℕ)
    (p : Source R n) (hp : p.IsHomogeneous d) :
    (representative R n d p hp : Source R n ⧸ hankelIdeal R n) =
      Ideal.Quotient.mk (hankelIdeal R n) p := rfl

private theorem component_ext (R : Type u) [CommRing R] (n d : ℕ)
    (x y : component R n d)
    (h : (x : Source R n ⧸ hankelIdeal R n) = y) : x = y :=
  Subtype.ext h

/-! ## One variable: source degree is not lost at `n = 0` -/

private def oneExponentIndex (d : ℕ) :
    {e : Fin 1 →₀ ℕ // e.degree = d} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨Finsupp.single 0 d, by simp⟩
  left_inv e := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hd : e.1 0 = d := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_one] using e.2
    simpa using hd.symm
  right_inv i := Subsingleton.elim _ _

private theorem zero_mk_injective (R : Type u) [CommRing R] :
    Function.Injective (Ideal.Quotient.mkₐ R (hankelIdeal R 0)).toLinearMap := by
  intro p q h
  apply sub_eq_zero.mp
  apply Ideal.mem_bot.mp
  rw [← hankelIdeal_zero R]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mkₐ R (hankelIdeal R 0) (p - q) = 0
  change Ideal.Quotient.mkₐ R (hankelIdeal R 0) p =
    Ideal.Quotient.mkₐ R (hankelIdeal R 0) q at h
  rw [map_sub, h, sub_self]

private def oneVariableBasis (R : Type u) [CommRing R] (d : ℕ) :
    Module.Basis (Fin 1) R (component R 0 d) :=
  (((MvPolynomial.basisRestrictSupport R {e : Fin 1 →₀ ℕ | e.degree = d}).map
      (LinearEquiv.ofEq _ _
        (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 1) R d).symm)).reindex
      (oneExponentIndex d)).map
    (Submodule.equivMapOfInjective
      (Ideal.Quotient.mkₐ R (hankelIdeal R 0)).toLinearMap (zero_mk_injective R) _)

private theorem oneVariableBasis_apply (R : Type u) [CommRing R] (d : ℕ) (i : Fin 1) :
    (oneVariableBasis R d i : Source R 0 ⧸ hankelIdeal R 0) =
      Ideal.Quotient.mkₐ R (hankelIdeal R 0) (X 0 ^ d) := by
  simp only [oneVariableBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Submodule.coe_equivMapOfInjective_apply]
  apply congrArg (Ideal.Quotient.mkₐ R (hankelIdeal R 0))
  rw [MvPolynomial.X_pow_eq_monomial]
  apply MvPolynomial.ext
  intro e
  change ((Finsupp.supportedEquivFinsupp (R := R) (M := R)
      {e : Fin 1 →₀ ℕ | e.degree = d}).symm
      (Finsupp.single ((oneExponentIndex d).symm i) (1 : R)) :
        (Fin 1 →₀ ℕ) →₀ R) e = (monomial (Finsupp.single 0 d) (1 : R)).coeff e
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

private theorem oneVariable_reconstruction (R : Type u) [CommRing R] (d : ℕ)
    (x : component R 0 d) :
    (oneVariableBasis R d).repr x 0 • oneVariableBasis R d 0 = x := by
  simpa only [Fin.sum_univ_one] using (oneVariableBasis R d).sum_repr x

private theorem oneVariable_power_survives (R : Type u) [CommRing R] [Nontrivial R]
    (d : ℕ) :
    Ideal.Quotient.mkₐ R (hankelIdeal R 0) (X 0 ^ d) ≠ 0 := by
  intro h
  have hp : (X (0 : Fin 1) ^ d : Source R 0) = 0 :=
    zero_mk_injective R (by simpa only [AlgHom.toLinearMap_apply, map_zero] using h)
  have hc := congrArg (fun p : Source R 0 => p.coeff (Finsupp.single 0 d)) hp
  rw [MvPolynomial.X_pow_eq_monomial] at hc
  exact one_ne_zero (by
    simpa only [coeff_monomial, ite_true, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using hc)

private theorem zero_parameter_is_not_the_component (R : Type u) [CommRing R] :
    rncMap R 0 (X 0) = 1 ∧
      quotientAugmentation R 0 (Ideal.Quotient.mkₐ R (hankelIdeal R 0) (X 0)) = 0 := by
  constructor
  · simp [rncMap_X, coordinateExponent]
  · change quotientAugmentation R 0 (Ideal.Quotient.mk (hankelIdeal R 0) (X 0)) = 0
    rw [quotientAugmentation_mk]
    exact MvPolynomial.constantCoeff_X R (0 : Fin 1)

/-! ## Degree zero: the actual coefficient component -/

private def constantEquiv (R : Type u) [CommRing R] (n : ℕ) :
    component R n 0 ≃ₗ[R] R where
  toFun x := quotientAugmentation R n x.1
  invFun r := representative R n 0 (C r) (isHomogeneous_C (Fin (n + 1)) r)
  left_inv x := by
    rcases x with ⟨x, p, hp, rfl⟩
    apply Subtype.ext
    change Ideal.Quotient.mkₐ R (hankelIdeal R n)
        (C (quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) p))) = _
    rw [quotientAugmentation_mk]
    have hconst : C (p.coeff 0) = p := by
      simpa only [homogeneousComponent_zero] using homogeneousComponent_eq_self hp
    exact congrArg (Ideal.Quotient.mkₐ R (hankelIdeal R n)) hconst
  right_inv r := by
    change quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) (C r)) = r
    rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_C]
  map_add' x y := (quotientAugmentation R n).map_add x.1 y.1
  map_smul' r x := (quotientAugmentation R n).toLinearMap.map_smul r x.1

private def constantBasis (R : Type u) [CommRing R] (n : ℕ) :
    Module.Basis (Fin 1) R (component R n 0) :=
  (Module.Basis.singleton (Fin 1) R).map (constantEquiv R n).symm

private theorem constantBasis_apply (R : Type u) [CommRing R] (n : ℕ) (i : Fin 1) :
    (constantBasis R n i : Source R n ⧸ hankelIdeal R n) = 1 := by
  simp only [constantBasis, Module.Basis.map_apply, Module.Basis.singleton_apply]
  change Ideal.Quotient.mkₐ R (hankelIdeal R n) (C 1) = 1
  rw [map_one, map_one]

private theorem constant_scalar_action (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    (r • constantBasis R n 0 : Source R n ⧸ hankelIdeal R n) =
      algebraMap R (Source R n ⧸ hankelIdeal R n) r := by
  rw [constantBasis_apply, Algebra.smul_def r (1 : Source R n ⧸ hankelIdeal R n), mul_one]

private theorem constant_scalar_coordinate (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    (constantEquiv R n)
      (representative R n 0 (C r) (isHomogeneous_C (Fin (n + 1)) r)) = r :=
  (constantEquiv R n).apply_symm_apply r

private theorem constant_reconstruction (R : Type u) [CommRing R] (n : ℕ)
    (x : component R n 0) :
    (constantBasis R n).repr x 0 • constantBasis R n 0 = x := by
  simpa only [Fin.sum_univ_one] using (constantBasis R n).sum_repr x

/-! ## Two variables: stock degree fibers and the finite antidiagonal -/

private def twoExponentAntidiagonal (d : ℕ) :
    {e : Fin 2 →₀ ℕ // e.degree = d} ≃ (Finset.antidiagonal d) where
  toFun e := ⟨(e.1 1, e.1 0), Finset.mem_antidiagonal.mpr (by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two, Nat.add_comm] using e.2)⟩
  invFun p := ⟨Finsupp.single 0 p.1.2 + Finsupp.single 1 p.1.1, by
    have hp := Finset.mem_antidiagonal.mp p.2
    simpa only [map_add, Finsupp.degree_single, Nat.add_comm] using hp⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp

private def twoExponentIndex (d : ℕ) :
    {e : Fin 2 →₀ ℕ // e.degree = d} ≃ Fin (d + 1) :=
  (twoExponentAntidiagonal d).trans (Finset.Nat.antidiagonalEquivFin d)

private theorem twoExponentIndex_symm (d : ℕ) (i : Fin (d + 1)) :
    ((twoExponentIndex d).symm i).1 =
      Finsupp.single 0 (d - i.val) + Finsupp.single 1 i.val := rfl

private theorem one_mk_injective (R : Type u) [CommRing R] :
    Function.Injective (Ideal.Quotient.mkₐ R (hankelIdeal R 1)).toLinearMap := by
  intro p q h
  apply sub_eq_zero.mp
  apply Ideal.mem_bot.mp
  rw [← hankelIdeal_one R]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mkₐ R (hankelIdeal R 1) (p - q) = 0
  change Ideal.Quotient.mkₐ R (hankelIdeal R 1) p =
    Ideal.Quotient.mkₐ R (hankelIdeal R 1) q at h
  rw [map_sub, h, sub_self]

private def twoVariableBasis (R : Type u) [CommRing R] (d : ℕ) :
    Module.Basis (Fin (d + 1)) R (component R 1 d) :=
  (((MvPolynomial.basisRestrictSupport R {e : Fin 2 →₀ ℕ | e.degree = d}).map
      (LinearEquiv.ofEq _ _
        (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) R d).symm)).reindex
      (twoExponentIndex d)).map
    (Submodule.equivMapOfInjective
      (Ideal.Quotient.mkₐ R (hankelIdeal R 1)).toLinearMap (one_mk_injective R) _)

private theorem twoVariableBasis_apply (R : Type u) [CommRing R] (d : ℕ)
    (i : Fin (d + 1)) :
    (twoVariableBasis R d i : Source R 1 ⧸ hankelIdeal R 1) =
      Ideal.Quotient.mkₐ R (hankelIdeal R 1)
        (monomial (Finsupp.single 0 (d - i.val) + Finsupp.single 1 i.val) 1) := by
  simp only [twoVariableBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Submodule.coe_equivMapOfInjective_apply]
  apply congrArg (Ideal.Quotient.mkₐ R (hankelIdeal R 1))
  apply MvPolynomial.ext
  intro e
  change ((Finsupp.supportedEquivFinsupp (R := R) (M := R)
      {e : Fin 2 →₀ ℕ | e.degree = d}).symm
      (Finsupp.single ((twoExponentIndex d).symm i) (1 : R)) :
        (Fin 2 →₀ ℕ) →₀ R) e =
    (monomial (Finsupp.single 0 (d - i.val) + Finsupp.single 1 i.val) (1 : R)).coeff e
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

private theorem twoVariable_reconstruction (R : Type u) [CommRing R] (d : ℕ)
    (x : component R 1 d) :
    ∑ i, (twoVariableBasis R d).repr x i • twoVariableBasis R d i = x :=
  (twoVariableBasis R d).sum_repr x

/-! ## A conic over nonreduced coefficients -/

private def conicPolynomial : Fin 5 → Source (ZMod 4) 2 :=
  ![X 0 ^ 2, X 0 * X 1, X 1 ^ 2, X 1 * X 2, X 2 ^ 2]

private theorem conicPolynomial_homogeneous (i : Fin 5) :
    (conicPolynomial i).IsHomogeneous 2 := by
  fin_cases i
  · exact isHomogeneous_X_pow (R := ZMod 4) (0 : Fin 3) 2
  · exact (isHomogeneous_X (ZMod 4) 0).mul (isHomogeneous_X (ZMod 4) 1)
  · exact isHomogeneous_X_pow (R := ZMod 4) (1 : Fin 3) 2
  · exact (isHomogeneous_X (ZMod 4) 1).mul (isHomogeneous_X (ZMod 4) 2)
  · exact isHomogeneous_X_pow (R := ZMod 4) (2 : Fin 3) 2

private def conicVector (i : Fin 5) : component (ZMod 4) 2 2 :=
  representative (ZMod 4) 2 2 (conicPolynomial i) (conicPolynomial_homogeneous i)

private theorem conic_relation :
    Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) (X 0 * X 2) =
      Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) (X 1 ^ 2) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hminor : hankelMinor (ZMod 4) 2 ⟨(0, 1), by decide⟩ =
      (X 0 * X 2 - X 1 * X 1 : Source (ZMod 4) 2) := rfl
  simpa only [hminor, pow_two] using
    minor_mem (ZMod 4) 2 ⟨(0, 1), by decide⟩

private def conicDescend :
    (Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) →ₐ[ZMod 4] Target (ZMod 4) :=
  Ideal.Quotient.liftₐ (hankelIdeal (ZMod 4) 2)
    (AddMonoidAlgebra.mapDomainAlgHom (ZMod 4) (ZMod 4) (rncExponent 2))
    (fun _p hp => hankelIdeal_le_ker (ZMod 4) 2 hp)

private theorem conicDescend_mk (p : Source (ZMod 4) 2) :
    conicDescend (Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) p) =
      rncMap (ZMod 4) 2 p := rfl

private theorem conicDescend_injective : Function.Injective conicDescend := by
  intro x y h
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective (ZMod 4) (hankelIdeal (ZMod 4) 2) x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mkₐ_surjective (ZMod 4) (hankelIdeal (ZMod 4) 2) y
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [hankelIdeal_eq_ker (ZMod 4) 2 (by decide)]
  change rncMap (ZMod 4) 2 (p - q) = 0
  rw [conicDescend_mk, conicDescend_mk] at h
  rw [map_sub, h, sub_self]

private def conicCoordinates : component (ZMod 4) 2 2 →ₗ[ZMod 4] (Fin 5 → ZMod 4) where
  toFun x i := (conicDescend x.1).coeff ((twoExponentIndex 4).symm i).1
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

private theorem conicCoordinates_vector (i : Fin 5) :
    conicCoordinates (conicVector i) = Pi.single i 1 := by
  ext j
  change (conicDescend
      (Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) (conicPolynomial i))).coeff
      ((twoExponentIndex 4).symm j).1 = (Pi.single i (1 : ZMod 4) : Fin 5 → ZMod 4) j
  rw [conicDescend_mk, twoExponentIndex_symm]
  fin_cases i <;> fin_cases j <;>
    simp [conicPolynomial, map_mul, map_pow, rncMap_X, coordinateExponent,
      monomial_mul_monomial, monomial_pow, Finsupp.ext_iff, Fin.forall_fin_two]

private theorem conic_image_homogeneous (p : Source (ZMod 4) 2)
    (hp : p.IsHomogeneous 2) : (rncMap (ZMod 4) 2 p).IsHomogeneous 4 := by
  rw [p.as_sum, map_sum]
  apply (homogeneousSubmodule (Fin 2) (ZMod 4) 4).sum_mem
  intro e he
  rw [rncMap_monomial]
  apply isHomogeneous_monomial
  have hedegree : e.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp he)
  have htotal := rncExponent_total 2 e
  change rncExponent 2 e 0 + rncExponent 2 e 1 = 2 * e.degree at htotal
  rw [hedegree] at htotal
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using htotal

private theorem conicCoordinates_injective : Function.Injective conicCoordinates := by
  intro x y h
  apply Subtype.ext
  apply conicDescend_injective
  obtain ⟨p, hp, hpx⟩ := (component_mem_iff (ZMod 4) 2 2 x.1).mp x.2
  obtain ⟨q, hq, hqy⟩ := (component_mem_iff (ZMod 4) 2 2 y.1).mp y.2
  have hph : (conicDescend x.1).IsHomogeneous 4 := by
    rw [← hpx, conicDescend_mk]
    exact conic_image_homogeneous p hp
  have hqh : (conicDescend y.1).IsHomogeneous 4 := by
    rw [← hqy, conicDescend_mk]
    exact conic_image_homogeneous q hq
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = 4
  · let i := twoExponentIndex 4 ⟨e, he⟩
    have hi := congrFun h i
    have hindex : ((twoExponentIndex 4).symm i).1 = e :=
      congrArg Subtype.val ((twoExponentIndex 4).symm_apply_apply ⟨e, he⟩)
    change (conicDescend x.1).coeff ((twoExponentIndex 4).symm i).1 =
      (conicDescend y.1).coeff ((twoExponentIndex 4).symm i).1 at hi
    simpa only [hindex] using hi
  · rw [hph.coeff_eq_zero he, hqh.coeff_eq_zero he]

private theorem conicCoordinates_surjective : Function.Surjective conicCoordinates := by
  intro c
  refine ⟨∑ i, c i • conicVector i, ?_⟩
  ext j
  simp [map_sum, map_smul, conicCoordinates_vector, Pi.single_apply]

private def conicEquiv : component (ZMod 4) 2 2 ≃ₗ[ZMod 4] (Fin 5 → ZMod 4) :=
  LinearEquiv.ofBijective conicCoordinates
    ⟨conicCoordinates_injective, conicCoordinates_surjective⟩

private def conicBasis : Module.Basis (Fin 5) (ZMod 4) (component (ZMod 4) 2 2) :=
  Module.Basis.ofEquivFun conicEquiv

private theorem conicBasis_apply (i : Fin 5) : conicBasis i = conicVector i := by
  apply conicEquiv.injective
  have hb : conicBasis i = conicEquiv.symm (Pi.single i 1) :=
    congrFun (Module.Basis.coe_ofEquivFun conicEquiv) i
  rw [hb, LinearEquiv.apply_symm_apply]
  exact (conicCoordinates_vector i).symm

private theorem conicBasis_repr (x : component (ZMod 4) 2 2) (i : Fin 5) :
    conicBasis.repr x i = (conicDescend x.1).coeff ((twoExponentIndex 4).symm i).1 :=
  Module.Basis.ofEquivFun_repr_apply conicEquiv x i

private theorem conic_reconstruction (x : component (ZMod 4) 2 2) :
    ∑ i, (conicDescend x.1).coeff ((twoExponentIndex 4).symm i).1 • conicVector i = x := by
  simpa only [conicBasis_repr, conicBasis_apply] using conicBasis.sum_repr x

private theorem conic_nilpotent_positive_coordinate :
    conicCoordinates ((2 : ZMod 4) • conicVector 0) 0 = 2 ∧
      (2 : ZMod 4) • conicVector 0 ≠ 0 ∧
      ((2 : ZMod 4) • (conicVector 0 : Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2)) ^ 2 = 0 := by
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  have hcoord : conicCoordinates ((2 : ZMod 4) • conicVector 0) 0 = 2 := by
    simp [map_smul, conicCoordinates_vector]
  refine ⟨hcoord, ?_, ?_⟩
  · intro hzero
    rw [hzero, map_zero, Pi.zero_apply] at hcoord
    exact htwo hcoord.symm
  · change ((2 : ZMod 4) •
      (Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) (X 0 ^ 2))) ^ 2 = 0
    rw [Algebra.smul_def (2 : ZMod 4)
      (Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 2) (X 0 ^ 2)),
      mul_pow, ← map_pow, hsq, map_zero, zero_mul]

/-! ## Zero coefficients and an independent coefficient universe -/

private def zeroCoefficientBasis (n d : ℕ) :
    Module.Basis (Fin (n * d + 1)) (ZMod 1) (component (ZMod 1) n d) :=
  Module.Basis.ofRepr
    (Module.subsingletonEquiv (ZMod 1) (component (ZMod 1) n d) (Fin (n * d + 1)))

private theorem zeroCoefficient_coordinates (n d : ℕ) (x : component (ZMod 1) n d)
    (i : Fin (n * d + 1)) :
    (zeroCoefficientBasis n d).repr x i = 0 :=
  Subsingleton.elim _ _

private theorem zeroCoefficient_vectors_coincide (n d : ℕ) (i j : Fin (n * d + 1)) :
    zeroCoefficientBasis n d i = zeroCoefficientBasis n d j :=
  Subsingleton.elim _ _

private def liftedIntegerBasis (d : ℕ) :
    Module.Basis (Fin 1) (ULift.{v} ℤ) (component (ULift.{v} ℤ) 0 d) :=
  oneVariableBasis (ULift.{v} ℤ) d

private theorem liftedInteger_power_survives (d : ℕ) :
    Ideal.Quotient.mkₐ (ULift.{v} ℤ) (hankelIdeal (ULift.{v} ℤ) 0) (X 0 ^ d) ≠ 0 :=
  oneVariable_power_survives (ULift.{v} ℤ) d

end

end ToricIdeals.RationalNormalCurve.HomogeneousQuotientModels
