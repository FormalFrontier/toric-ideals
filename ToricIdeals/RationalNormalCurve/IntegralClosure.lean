/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
public import ToricIdeals.RationalNormalCurve

import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.ExponentImage

/-!
# Integral closedness of rational-normal-curve coordinate rings

This module states the integral-closedness criterion for the full quotient of
`Source R n` by `hankelIdeal R n`, over a commutative domain `R`, in every degree.
It uses Mathlib's `IsIntegrallyClosed`, whose definition itself requires only a
commutative ring; the domain hypothesis is part of the criterion's context.

At degree zero the Hankel ideal is `⊥` and the full quotient is a one-variable
polynomial ring. It is not replaced by the image of the parametrization.

## References

* Mathlib contributors, `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  for the integral-closedness predicate.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u v

/-- Integral closedness descends along an algebra's unital linear splitting. -/
private theorem isIntegrallyClosed_of_linearMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain B] [IsIntegrallyClosed B] (p : B →ₗ[A] A) (hp1 : p 1 = 1) :
    IsIntegrallyClosed A := by
  have hp_map (a : A) : p (algebraMap A B a) = a := by
    calc
      p (algebraMap A B a) = p (a • (1 : B)) := by
        rw [Algebra.smul_def, mul_one]
      _ = a • p 1 := p.map_smul a 1
      _ = a := by rw [hp1, smul_eq_mul, mul_one]
  have hinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    simpa only [hp_map] using congrArg p hab
  let : IsDomain A := Function.Injective.isDomain (algebraMap A B) hinj
  let g : A →+* FractionRing B :=
    (algebraMap B (FractionRing B)).comp (algebraMap A B)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B (FractionRing B)).comp hinj
  let f : FractionRing A →+* FractionRing B := IsFractionRing.lift hg
  have hf (a : A) : f (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) :=
    IsFractionRing.lift_algebraMap hg a
  apply (isIntegrallyClosed_iff (FractionRing A)).mpr
  intro x hx
  have hfx : IsIntegral B (f x) :=
    IsIntegral.map_of_comp_eq (algebraMap A B) f (by
      ext a
      exact (hf a).symm) hx
  obtain ⟨y, hy⟩ :=
    (isIntegrallyClosed_iff (FractionRing B)).mp (inferInstance : IsIntegrallyClosed B) hfx
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
  have hbA : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul : algebraMap A (FractionRing A) b * x =
      algebraMap A (FractionRing A) a := by
    calc
      algebraMap A (FractionRing A) b * x = x * algebraMap A (FractionRing A) b :=
        mul_comm _ _
      _ = algebraMap A (FractionRing A) a := ((div_eq_iff hbA).mp hab).symm
  have hclear : algebraMap A B b * y = algebraMap A B a := by
    apply IsFractionRing.injective B (FractionRing B)
    calc
      algebraMap B (FractionRing B) (algebraMap A B b * y) =
          f (algebraMap A (FractionRing A) b * x) := by
        simp only [map_mul, hf, hy]
      _ = f (algebraMap A (FractionRing A) a) := congrArg f hmul
      _ = algebraMap B (FractionRing B) (algebraMap A B a) := hf a
  have hpy : b * p y = a := by
    calc
      b * p y = p (algebraMap A B b * y) := by
        simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using
          (p.map_smul b y).symm
      _ = p (algebraMap A B a) := congrArg p hclear
      _ = a := hp_map a
  refine ⟨p y, ?_⟩
  apply mul_left_cancel₀ hbA
  calc
    algebraMap A (FractionRing A) b * algebraMap A (FractionRing A) (p y) =
        algebraMap A (FractionRing A) a := by rw [← map_mul, hpy]
    _ = algebraMap A (FractionRing A) b * x := hmul.symm

private theorem quotient_zero_isIntegrallyClosed (R : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed (Source R 0 ⧸ hankelIdeal R 0) := by
  rw [hankelIdeal_zero]
  exact IsIntegrallyClosed.of_equiv
    ((MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingEquiv.trans
      (RingEquiv.quotientBot (Source R 0)).symm)

private def degreeMod (n : ℕ) : (Fin 2 →₀ ℕ) →+ ZMod n where
  toFun d := ((d 0 + d 1 : ℕ) : ZMod n)
  map_zero' := by simp
  map_add' d e := by
    simp only [Finsupp.add_apply, Nat.cast_add]
    abel

private theorem rncMap_range_eq_gradeZero (R : Type u) [CommRing R] (n : ℕ) :
    (rncMap R n).range =
      SetLike.GradeZero.subring (AddMonoidAlgebra.gradeBy R (degreeMod n)) := by
  classical
  let cS : Source R n ≃ₗ[R] ((Fin (n + 1) →₀ ℕ) →₀ R) :=
    AddMonoidAlgebra.coeffLinearEquiv R
  let cT : Target R ≃ₗ[R] ((Fin 2 →₀ ℕ) →₀ R) :=
    AddMonoidAlgebra.coeffLinearEquiv R
  let l : ((Fin (n + 1) →₀ ℕ) →₀ R) →ₗ[R] ((Fin 2 →₀ ℕ) →₀ R) :=
    Finsupp.lmapDomain R R (rncExponent n)
  have hs : LinearMap.range l =
      Finsupp.supported R R (Set.range (rncExponent n)) := by
    simpa only [Finsupp.supported_univ, ← LinearMap.range_eq_map, Set.image_univ]
      using Finsupp.lmapDomain_supported R R (rncExponent n) Set.univ
  have hr (f : Target R) :
      f ∈ (rncMap R n).range ↔ cT f ∈ LinearMap.range l := by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨cS a, rfl⟩
    · rintro ⟨a, ha⟩
      refine ⟨cS.symm a, ?_⟩
      apply cT.injective
      change l (cS (cS.symm a)) = cT f
      simpa only [LinearEquiv.apply_symm_apply] using ha
  ext f
  rw [hr, hs, Finsupp.mem_supported]
  change (↑f.coeff.support ⊆ Set.range (rncExponent n)) ↔
    ∀ d, d ∈ f.coeff.support → degreeMod n d = 0
  constructor
  · intro h d hd
    apply (ZMod.natCast_eq_zero_iff (d 0 + d 1) n).mpr
    exact (mem_mrange_rncExponent_iff n d).mp (AddMonoidHom.mem_mrange.mpr (h hd))
  · intro h d hd
    apply AddMonoidHom.mem_mrange.mp
    apply (mem_mrange_rncExponent_iff n d).mpr
    exact (ZMod.natCast_eq_zero_iff (d 0 + d 1) n).mp (h d hd)

-- The scalar ring here is the whole image, acting by its inclusion in the target.
-- For the cyclic grading the projection need not preserve multiplication.
private theorem exists_range_linearProjection (R : Type u) [CommRing R] (n : ℕ) :
    ∃ p : Target R →ₗ[(rncMap R n).range] (rncMap R n).range, p 1 = 1 := by
  classical
  let G := AddMonoidAlgebra.gradeBy R (degreeMod n)
  have hG : (rncMap R n).range = SetLike.GradeZero.subring G :=
    rncMap_range_eq_gradeZero R n
  have hmem (f : Target R) : f ∈ (rncMap R n).range ↔ f ∈ G 0 := by
    rw [hG]
    rfl
  let p : Target R →ₗ[(rncMap R n).range] (rncMap R n).range :=
    { toFun f := ⟨GradedAlgebra.proj G 0 f,
        (hmem _).mpr (DirectSum.decompose G f 0).property⟩
      map_add' f g := by
        apply Subtype.ext
        exact (GradedAlgebra.proj G 0).map_add f g
      map_smul' a f := by
        apply Subtype.ext
        change (DirectSum.decompose G ((a : Target R) * f) 0 : Target R) =
          (a : Target R) * (DirectSum.decompose G f 0 : Target R)
        exact DirectSum.coe_decompose_mul_of_left_mem_zero G ((hmem _).mp a.property) }
  refine ⟨p, ?_⟩
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same G (SetLike.one_mem_graded G)

/-- In every degree, the full Hankel quotient over a commutative domain is
integrally closed exactly when its coefficient ring is integrally closed. -/
theorem quotient_isIntegrallyClosed_iff (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) :
    IsIntegrallyClosed (Source R n ⧸ hankelIdeal R n) ↔ IsIntegrallyClosed R := by
  classical
  let : IsDomain (Source R n ⧸ hankelIdeal R n) :=
    (quotient_isDomain_iff R n).2 inferInstance
  constructor
  · intro hQ
    let : IsIntegrallyClosed (Source R n ⧸ hankelIdeal R n) := hQ
    exact isIntegrallyClosed_of_linearMap R (Source R n ⧸ hankelIdeal R n)
      (quotientAugmentation R n).toLinearMap (map_one (quotientAugmentation R n))
  · intro hR
    let : IsIntegrallyClosed R := hR
    by_cases hn : n = 0
    · subst n
      exact quotient_zero_isIntegrallyClosed R
    · let : IsIntegrallyClosed (MvPolynomial (Fin 1) R) :=
        IsIntegrallyClosed.of_equiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingEquiv
      let : IsIntegrallyClosed (Target R) :=
        IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R 1).symm.toRingEquiv
      obtain ⟨p, hp1⟩ := exists_range_linearProjection R n
      let : IsIntegrallyClosed (rncMap R n).range :=
        isIntegrallyClosed_of_linearMap (rncMap R n).range (Target R) p hp1
      exact IsIntegrallyClosed.of_equiv
        (quotientEquivRange R n (Nat.one_le_iff_ne_zero.mpr hn)).symm

end ToricIdeals.RationalNormalCurve
