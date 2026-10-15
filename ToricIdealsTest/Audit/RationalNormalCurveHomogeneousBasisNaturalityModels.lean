/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.HomogeneousBasis

/-!
# Coefficient change of homogeneous Hankel-quotient vectors

The examples use the standard homogeneous submodule of the full Hankel
quotient and its coefficient-ring action. Reduction from `ZMod 4` to
`ZMod 2` kills a nonzero square-zero basis multiple in every component.
Identity maps include both nilpotent and zero coefficient rings.

One-variable powers, constant components, bivariate monomials and the five
quadratic conic vectors give explicit coefficient-change computations.
Integer homomorphisms and independently lifted coefficient rings provide
examples with different coefficient universes. All declarations are private.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.HomogeneousBasis`
  and its homogeneous-basis examples, for representative and coordinate laws,
  the five conic monomials and the square-zero coefficient example.
* Mathlib contributors, quotient ring homomorphisms, basis representations,
  modular coefficient reduction and lifted commutative rings.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve.Audit.CoefficientChangeExamples

noncomputable section

universe u v w z

-- Reduction of coefficients modulo two.
private def reduction : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)

private theorem reduction_two : reduction (2 : ZMod 4) = 0 := by
  have h := map_natCast reduction 2
  exact h.trans (by decide : (2 : ZMod 2) = 0)

private theorem reduction_not_injective : ¬ Function.Injective reduction := by
  intro hinj
  have h : (2 : ZMod 4) = 0 := hinj (reduction_two.trans (map_zero reduction).symm)
  exact (by decide : (2 : ZMod 4) ≠ 0) h

private theorem coefficient_two_nonzero_square_zero :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  constructor <;> decide

-- The coefficient is detected in every homogeneous component, including
-- components over a nonreduced coefficient ring.
private theorem nilpotent_basis_coordinates (n d : ℕ) (i j : Fin (n * d + 1)) :
    (quotientHomogeneousBasis (ZMod 4) n d).repr
      ((2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i) j =
      if i = j then 2 else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

private theorem nilpotent_basis_coordinate (n d : ℕ) (i : Fin (n * d + 1)) :
    (quotientHomogeneousBasis (ZMod 4) n d).repr
      ((2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i) i = 2 ∧
    (2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i ≠ 0 := by
  have hc : (quotientHomogeneousBasis (ZMod 4) n d).repr
      ((2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i) i = 2 := by
    simp
  refine ⟨hc, ?_⟩
  intro hz
  rw [hz, map_zero, Finsupp.zero_apply] at hc
  exact (by decide : (2 : ZMod 4) ≠ 0) hc.symm

private theorem nilpotent_basis_class_nonzero
    (n d : ℕ) (i : Fin (n * d + 1)) :
    (2 : ZMod 4) •
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ≠ 0 := by
  intro hz
  have hsub : (2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i = 0 :=
    Subtype.ext hz
  exact (nilpotent_basis_coordinate n d i).2 hsub

private theorem nilpotent_basis_class_square_zero
    (n d : ℕ) (i : Fin (n * d + 1)) :
    ((2 : ZMod 4) •
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)) ^ 2 = 0 := by
  rw [Algebra.smul_def (R := ZMod 4)
    (A := Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) (2 : ZMod 4)
    (quotientHomogeneousBasis (ZMod 4) n d i :
      Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n),
    mul_pow, ← map_pow, coefficient_two_nonzero_square_zero.2, map_zero, zero_mul]

-- Coefficient reduction kills this nonzero square-zero class in every
-- component, without an injectivity assertion for the quotient map.
private theorem reduction_kills_nilpotent_basis_class
    (n d : ℕ) (i : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) n) (MvPolynomial.map reduction)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal reduction n).le)
      ((2 : ZMod 4) •
        (quotientHomogeneousBasis (ZMod 4) n d i :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)) = 0 := by
  rw [Algebra.smul_def (R := ZMod 4)
    (A := Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) (2 : ZMod 4)
    (quotientHomogeneousBasis (ZMod 4) n d i :
      Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n),
    map_mul, Ideal.quotientMap_algebraMap]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
    reduction_two, map_zero, zero_mul]

-- Identity coefficient change acts on every indexed vector.
private theorem nilpotent_identity (n d : ℕ) (i : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 4) n)
      (MvPolynomial.map (RingHom.id (ZMod 4)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (RingHom.id (ZMod 4)) n).le)
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) =
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (quotientHomogeneousBasis (ZMod 4) n d i :
      Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)
  rw [← hp, Ideal.quotientMap_mk, MvPolynomial.map_id]

private theorem zero_identity (n d : ℕ) (i : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 1) n)
      (MvPolynomial.map (RingHom.id (ZMod 1)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (RingHom.id (ZMod 1)) n).le)
      (quotientHomogeneousBasis (ZMod 1) n d i :
        Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) =
      (quotientHomogeneousBasis (ZMod 1) n d i :
        Source (ZMod 1) n ⧸ hankelIdeal (ZMod 1) n) :=
  Subsingleton.elim _ _

private theorem zero_basis_coordinates (n d : ℕ)
    (i j : Fin (n * d + 1)) :
    quotientHomogeneousBasis (ZMod 1) n d i =
      quotientHomogeneousBasis (ZMod 1) n d j ∧
    (quotientHomogeneousBasis (ZMod 1) n d).repr
      (quotientHomogeneousBasis (ZMod 1) n d i) j = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

-- The full one-variable quotient retains the degree of X_0^d.
private theorem reduction_one_variable (d : ℕ) (i : Fin (0 * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) 0) (MvPolynomial.map reduction)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal reduction 0).le)
      (quotientHomogeneousBasis (ZMod 4) 0 d i :
        Source (ZMod 4) 0 ⧸ hankelIdeal (ZMod 4) 0) =
      Ideal.Quotient.mkₐ (ZMod 2) (hankelIdeal (ZMod 2) 0) (X 0 ^ d) := by
  rw [quotientHomogeneousBasis_zero_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.quotientMap_mk, map_pow, MvPolynomial.map_X]
  rfl

private theorem one_variable_power_nonzero (d : ℕ) :
    Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 0) (X 0 ^ d) ≠ 0 := by
  intro hz
  have hsub : quotientHomogeneousRepresentative (ZMod 4) 0 d (X 0 ^ d)
      (isHomogeneous_X_pow 0 d) = 0 := Subtype.ext hz
  have hc := congrArg (fun x => (quotientHomogeneousBasis (ZMod 4) 0 d).repr x 0) hsub
  rw [quotientHomogeneousBasis_repr_representative_zero] at hc
  have hone : (1 : ZMod 4) = 0 := by
    simpa [X_pow_eq_monomial] using hc
  exact (by decide : (1 : ZMod 4) ≠ 0) hone

private theorem one_variable_power_not_one (d : ℕ) (hd : 0 < d) :
    Ideal.Quotient.mkₐ (ZMod 4) (hankelIdeal (ZMod 4) 0) (X 0 ^ d) ≠ 1 := by
  intro h
  have h' : Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) (X 0 ^ d) =
      Ideal.Quotient.mk (hankelIdeal (ZMod 4) 0) 1 := by simpa using h
  have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X 0 ^ d) 1).mp h'
  rw [hankelIdeal_zero] at hm
  have hp : (X (0 : Fin 1) ^ d - 1 : Source (ZMod 4) 0) = 0 := Ideal.mem_bot.mp hm
  have hc := congrArg (fun p : Source (ZMod 4) 0 =>
    p.coeff (Finsupp.single 0 d)) hp
  have hs : (Finsupp.single (0 : Fin 1) d : Fin 1 →₀ ℕ) ≠ 0 := by
    simpa using (Nat.ne_of_gt hd)
  have hone : (1 : ZMod 4) = 0 := by
    simpa [X_pow_eq_monomial, coeff_one, Ne.symm hs] using hc
  exact (by decide : (1 : ZMod 4) ≠ 0) hone

-- All n: the degree-zero basis vector is the coefficient unit.
private theorem degree_zero_unit (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n * 0 + 1)) :
    (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n) = 1 := by
  have h : quotientHomogeneousBasis R n 0 i =
      quotientHomogeneousRepresentative R n 0 (C 1)
        (isHomogeneous_C (Fin (n + 1)) (1 : R)) := by
    apply (quotientHomogeneousBasis R n 0).repr.injective
    ext j
    have hij : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      simp only [Nat.mul_zero, Nat.zero_add] at hi hj
      omega
    subst j
    rw [Module.Basis.repr_self]
    simpa only [Finsupp.single_eq_same] using
      (quotientHomogeneousBasis_repr_C R n (1 : R) i).symm
  rw [h, quotientHomogeneousRepresentative_coe, map_one, map_one]

private theorem degree_zero_coefficient_action (R : Type u) [CommRing R] (n : ℕ)
    (r : R) (i : Fin (n * 0 + 1)) :
    r • (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n) =
      algebraMap R (Source R n ⧸ hankelIdeal R n) r := by
  rw [degree_zero_unit]
  exact (Algebra.algebraMap_eq_smul_one (R := R)
    (A := Source R n ⧸ hankelIdeal R n) r).symm

private theorem reduction_degree_zero (n : ℕ) (i : Fin (n * 0 + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) n) (MvPolynomial.map reduction)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal reduction n).le)
      (quotientHomogeneousBasis (ZMod 4) n 0 i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) =
      (quotientHomogeneousBasis (ZMod 2) n 0 i :
        Source (ZMod 2) n ⧸ hankelIdeal (ZMod 2) n) := by
  simp only [degree_zero_unit, map_one]

-- Bivariate monomials retain their given index under reduction.
private theorem reduction_two_variable (d : ℕ) (i : Fin (1 * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) 1) (MvPolynomial.map reduction)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal reduction 1).le)
      (quotientHomogeneousBasis (ZMod 4) 1 d i :
        Source (ZMod 4) 1 ⧸ hankelIdeal (ZMod 4) 1) =
      (quotientHomogeneousBasis (ZMod 2) 1 d i :
        Source (ZMod 2) 1 ⧸ hankelIdeal (ZMod 2) 1) := by
  simp only [quotientHomogeneousBasis_one_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.quotientMap_mk, MvPolynomial.map_monomial, map_one]

-- The five quadratic conic monomials, in increasing target weight.
private def conicPolynomial (R : Type u) [CommRing R] : Fin 5 → Source R 2 :=
  ![X 0 ^ 2, X 0 * X 1, X 1 ^ 2, X 1 * X 2, X 2 ^ 2]

private theorem conicPolynomial_homogeneous (R : Type u) [CommRing R] (i : Fin 5) :
    (conicPolynomial R i).IsHomogeneous 2 := by
  fin_cases i
  · exact isHomogeneous_X_pow (R := R) (0 : Fin 3) 2
  · exact (isHomogeneous_X R 0).mul (isHomogeneous_X R 1)
  · exact isHomogeneous_X_pow (R := R) (1 : Fin 3) 2
  · exact (isHomogeneous_X R 1).mul (isHomogeneous_X R 2)
  · exact isHomogeneous_X_pow (R := R) (2 : Fin 3) 2

private theorem conic_representative_is_basis (R : Type u) [CommRing R] (i : Fin 5) :
    quotientHomogeneousRepresentative R 2 2 (conicPolynomial R i)
      (conicPolynomial_homogeneous R i) = quotientHomogeneousBasis R 2 2 i := by
  apply (quotientHomogeneousBasis R 2 2).repr.injective
  ext j
  rw [quotientHomogeneousBasis_repr_representative_of_pos R 2 2 (by decide)]
  fin_cases i <;> fin_cases j <;>
    simp [conicPolynomial, map_mul, map_pow, rncMap_X, coordinateExponent,
      monomial_mul_monomial, monomial_pow, Finsupp.ext_iff, Fin.forall_fin_two]

private theorem reduction_conic_vector (i : Fin 5) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) 2) (MvPolynomial.map reduction)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal reduction 2).le)
      (quotientHomogeneousBasis (ZMod 4) 2 2 i :
        Source (ZMod 4) 2 ⧸ hankelIdeal (ZMod 4) 2) =
      (quotientHomogeneousBasis (ZMod 2) 2 2 i :
        Source (ZMod 2) 2 ⧸ hankelIdeal (ZMod 2) 2) := by
  rw [← conic_representative_is_basis (ZMod 4) i,
    ← conic_representative_is_basis (ZMod 2) i,
    quotientHomogeneousRepresentative_coe, quotientHomogeneousRepresentative_coe,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientMap_mk]
  apply congrArg (Ideal.Quotient.mk (hankelIdeal (ZMod 2) 2))
  fin_cases i <;> simp [conicPolynomial]

private theorem conic_distinct_coordinates (i j : Fin 5) (hij : i ≠ j) :
    quotientHomogeneousBasis (ZMod 4) 2 2 i ≠
      quotientHomogeneousBasis (ZMod 4) 2 2 j ∧
    quotientHomogeneousBasis (ZMod 2) 2 2 i ≠
      quotientHomogeneousBasis (ZMod 2) 2 2 j := by
  let _ : Nontrivial (ZMod 4) :=
    ⟨⟨2, 0, coefficient_two_nonzero_square_zero.1⟩⟩
  let _ : Nontrivial (ZMod 2) := ⟨⟨1, 0, by decide⟩⟩
  exact ⟨fun h => hij ((quotientHomogeneousBasis (ZMod 4) 2 2).injective h),
    fun h => hij ((quotientHomogeneousBasis (ZMod 2) 2 2).injective h)⟩

-- The canonical integer homomorphism into a lifted nonreduced ring.
private theorem integer_to_lifted_nilpotent (d : ℕ) :
    Ideal.quotientMap (hankelIdeal (ULift.{v} (ZMod 4)) 0)
      (MvPolynomial.map (Int.castRingHom (ULift.{v} (ZMod 4))))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (Int.castRingHom (ULift.{v} (ZMod 4))) 0).le)
      (Ideal.Quotient.mk (hankelIdeal ℤ 0) (C 2 * X 0 ^ d)) =
      Ideal.Quotient.mk (hankelIdeal (ULift.{v} (ZMod 4)) 0)
        (C (2 : ULift.{v} (ZMod 4)) * X 0 ^ d) := by
  rw [Ideal.quotientMap_mk]
  apply congrArg (Ideal.Quotient.mk (hankelIdeal (ULift.{v} (ZMod 4)) 0))
  simp only [map_mul, _root_.map_ofNat, map_pow,
    MvPolynomial.map_X]

private theorem lifted_nilpotent_nonzero :
    (2 : ULift.{v} (ZMod 4)) ≠ 0 ∧ (2 : ULift.{v} (ZMod 4)) ^ 2 = 0 := by
  constructor
  · intro h
    exact (by decide : (2 : ZMod 4) ≠ 0) (congrArg ULift.down h)
  · apply ULift.down_injective
    change (2 : ZMod 4) ^ 2 = 0
    decide

private theorem lifted_nilpotent_power_class_nonzero (d : ℕ) :
    Ideal.Quotient.mkₐ (ULift.{v} (ZMod 4))
      (hankelIdeal (ULift.{v} (ZMod 4)) 0)
      (C 2 * X 0 ^ d) ≠ 0 := by
  intro hz
  have hsub : quotientHomogeneousRepresentative (ULift.{v} (ZMod 4)) 0 d
      (C 2 * X 0 ^ d) (isHomogeneous_C_mul_X_pow 2 0 d) = 0 :=
    Subtype.ext hz
  have hc := congrArg (fun x =>
    (quotientHomogeneousBasis (ULift.{v} (ZMod 4)) 0 d).repr x 0) hsub
  rw [quotientHomogeneousBasis_repr_representative_zero] at hc
  have htwo : (2 : ULift.{v} (ZMod 4)) = 0 := by
    simpa [X_pow_eq_monomial] using hc
  exact lifted_nilpotent_nonzero.1 htwo

private theorem lifted_nilpotent_power_class_square_zero (d : ℕ) :
    (Ideal.Quotient.mkₐ (ULift.{v} (ZMod 4))
      (hankelIdeal (ULift.{v} (ZMod 4)) 0) (C 2 * X 0 ^ d)) ^ 2 = 0 := by
  rw [← map_pow, mul_pow, ← map_pow, lifted_nilpotent_nonzero.2,
    map_zero, zero_mul, map_zero]

private theorem integer_to_lifted_zero (n d : ℕ) (i : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ULift.{v} (ZMod 1)) n)
      (MvPolynomial.map (Int.castRingHom (ULift.{v} (ZMod 1))))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (Int.castRingHom (ULift.{v} (ZMod 1))) n).le)
      (quotientHomogeneousBasis ℤ n d i : Source ℤ n ⧸ hankelIdeal ℤ n) =
      (quotientHomogeneousBasis (ULift.{v} (ZMod 1)) n d i :
        Source (ULift.{v} (ZMod 1)) n ⧸ hankelIdeal (ULift.{v} (ZMod 1)) n) :=
  Subsingleton.elim _ _

-- Independent lifts of the modular reduction homomorphism.
private theorem independently_lifted_reduction (d : ℕ) :
    Ideal.quotientMap (hankelIdeal (ULift.{v} (ZMod 2)) 0)
      (MvPolynomial.map (reduction.ulift :
        ULift.{u} (ZMod 4) →+* ULift.{v} (ZMod 2)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (reduction.ulift :
          ULift.{u} (ZMod 4) →+* ULift.{v} (ZMod 2)) 0).le)
      (Ideal.Quotient.mk (hankelIdeal (ULift.{u} (ZMod 4)) 0) (X 0 ^ d)) =
      Ideal.Quotient.mk (hankelIdeal (ULift.{v} (ZMod 2)) 0) (X 0 ^ d) := by
  rw [Ideal.quotientMap_mk]
  simp

-- Arbitrary coefficient homomorphisms also act on these one-variable
-- representatives between independently lifted coefficient universes.
private theorem independently_lifted_coefficients
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) (d : ℕ) :
    Ideal.quotientMap (hankelIdeal (ULift.{z} S) 0)
      (MvPolynomial.map (φ.ulift : ULift.{w} R →+* ULift.{z} S))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (φ.ulift : ULift.{w} R →+* ULift.{z} S) 0).le)
      (Ideal.Quotient.mk (hankelIdeal (ULift.{w} R) 0)
        (C (ULift.up r) * X 0 ^ d)) =
      Ideal.Quotient.mk (hankelIdeal (ULift.{z} S) 0)
        (C (ULift.up (φ r)) * X 0 ^ d) := by
  rw [Ideal.quotientMap_mk]
  simp [RingHom.ulift_apply]

end
end ToricIdeals.RationalNormalCurve.Audit.CoefficientChangeExamples
