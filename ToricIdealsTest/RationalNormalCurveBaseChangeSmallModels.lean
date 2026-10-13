/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ToricIdeals.RationalNormalCurve

/-!
# Small-degree and coefficient-map boundary models for Hankel quotients

The degree-zero and degree-one Hankel quotients over the integers are the
full polynomial rings: their quotient maps are bijective, and evaluation
assigns arbitrary values to the one or two coordinates. In degree zero the
surviving coordinate is neither zero nor one, although its raw monomial
parametrization is one. In degree one both coordinates are nonzero and distinct.

For the diagonal coefficient map `ℤ → ℤ × ℤ`, extending the quadratic Hankel
ideal permits multiplication by arbitrary product coefficients. The constant
classes `(1, 0)` and `(0, 1)` are nonzero orthogonal idempotents, and neither
coefficient is diagonal. The unital coefficient map `ℤ → ZMod 1` induces a
quotient map that kills every class and is not injective. There is no unital
ring homomorphism `ZMod 1 → ℤ`.

These are finite polynomial, ideal and quotient computations. They neither
construct nor use a scalar-base-change equivalence for Hankel quotients.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, supplies the
  small-degree bottom-ideal facts, coefficient transport and ideal-kernel
  inclusion. The bottom-quotient injectivity and constant-detection arguments
  follow the existing coordinate-regularity boundary models, using
  `rncMap_C` for the constant computation.
* Mathlib contributors, polynomial evaluation, ideal extension and quotient
  ring maps. The quotient-by-bottom equivalence is from
  `Mathlib.RingTheory.Ideal.Quotient.Operations` (Kenny Lau and Patrick Massot).
-/

open MvPolynomial ToricIdeals.RationalNormalCurve

namespace ToricIdeals.RationalNormalCurve.BaseChangeSmallModels

noncomputable section

private theorem integer_degree_zero_full_polynomial :
    hankelIdeal ℤ 0 = ⊥ ∧
      Function.Bijective (Ideal.Quotient.mk (hankelIdeal ℤ 0)) := by
  refine ⟨hankelIdeal_zero ℤ, ?_, Ideal.Quotient.mk_surjective⟩
  rw [hankelIdeal_zero]
  intro p q hpq
  have h := congrArg (RingEquiv.quotientBot (Source ℤ 0)) hpq
  simpa only [RingEquiv.quotientBot_mk] using h

private theorem integer_degree_zero_evaluation (a : ℤ) :
    ∃ e : (Source ℤ 0 ⧸ hankelIdeal ℤ 0) →+* ℤ,
      e (Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1))) = a := by
  rw [hankelIdeal_zero]
  refine ⟨(MvPolynomial.eval (fun _ : Fin 1 => a)).comp
    (RingEquiv.quotientBot (Source ℤ 0)).toRingHom, ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.quotientBot_mk, MvPolynomial.eval_X]

private theorem integer_degree_zero_coordinate_and_raw_image :
    Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 0) (X (0 : Fin 1)) ≠ 1 ∧
      rncMap ℤ 0 (X (0 : Fin 1)) = 1 := by
  obtain ⟨e₀, he₀⟩ := integer_degree_zero_evaluation 0
  obtain ⟨e₁, he₁⟩ := integer_degree_zero_evaluation 1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (by simpa only [he₁, map_zero] using congrArg e₁ h)
  · intro h
    exact zero_ne_one (by simpa only [he₀, map_one] using congrArg e₀ h)
  · simp [rncMap_X, coordinateExponent]

private theorem integer_degree_one_full_polynomial :
    hankelIdeal ℤ 1 = ⊥ ∧
      Function.Bijective (Ideal.Quotient.mk (hankelIdeal ℤ 1)) := by
  refine ⟨hankelIdeal_one ℤ, ?_, Ideal.Quotient.mk_surjective⟩
  rw [hankelIdeal_one]
  intro p q hpq
  have h := congrArg (RingEquiv.quotientBot (Source ℤ 1)) hpq
  simpa only [RingEquiv.quotientBot_mk] using h

private theorem integer_degree_one_evaluation (a b : ℤ) :
    ∃ e : (Source ℤ 1 ⧸ hankelIdeal ℤ 1) →+* ℤ,
      e (Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2))) = a ∧
        e (Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2))) = b := by
  rw [hankelIdeal_one]
  refine ⟨(MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a else b)).comp
    (RingEquiv.quotientBot (Source ℤ 1)).toRingHom, ?_, ?_⟩ <;>
    simp [RingHom.comp_apply, RingEquiv.quotientBot_mk]

private theorem integer_degree_one_coordinates_retained :
    Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2)) ≠ 0 ∧
      Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (0 : Fin 2)) ≠
        Ideal.Quotient.mk (hankelIdeal ℤ 1) (X (1 : Fin 2)) := by
  obtain ⟨e₀, h₀₀, h₀₁⟩ := integer_degree_one_evaluation 1 0
  obtain ⟨e₁, _, h₁₁⟩ := integer_degree_one_evaluation 0 1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (by simpa only [h₀₀, map_zero] using congrArg e₀ h)
  · intro h
    exact one_ne_zero (by simpa only [h₁₁, map_zero] using congrArg e₁ h)
  · intro h
    exact one_ne_zero (by simpa only [h₀₀, h₀₁] using congrArg e₀ h)

private theorem diagonal_degree_two_ideal_transport :
    Ideal.map (MvPolynomial.map ((RingHom.id ℤ).prod (RingHom.id ℤ)))
      (hankelIdeal ℤ 2) = hankelIdeal (ℤ × ℤ) 2 :=
  map_hankelIdeal ((RingHom.id ℤ).prod (RingHom.id ℤ)) 2

private theorem diagonal_degree_two_extended_minor (c : ℤ × ℤ) :
    C c * MvPolynomial.map ((RingHom.id ℤ).prod (RingHom.id ℤ))
        (hankelMinor ℤ 2 (⟨(0, 1), by decide⟩ : MinorIndex 2)) ∈
      Ideal.map (MvPolynomial.map ((RingHom.id ℤ).prod (RingHom.id ℤ)))
        (hankelIdeal ℤ 2) := by
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
    (minor_mem ℤ 2 (⟨(0, 1), by decide⟩ : MinorIndex 2)))

private theorem product_idempotent_coefficients_not_diagonal :
    (¬ ∃ a : ℤ, ((RingHom.id ℤ).prod (RingHom.id ℤ)) a = (1, 0)) ∧
      (¬ ∃ a : ℤ, ((RingHom.id ℤ).prod (RingHom.id ℤ)) a = (0, 1)) := by
  constructor
  · rintro ⟨a, ha⟩
    have hfirst : a = 1 := congrArg Prod.fst ha
    have hsecond : a = 0 := congrArg Prod.snd ha
    exact one_ne_zero (hfirst.symm.trans hsecond)
  · rintro ⟨a, ha⟩
    have hfirst : a = 0 := congrArg Prod.fst ha
    have hsecond : a = 1 := congrArg Prod.snd ha
    exact zero_ne_one (hfirst.symm.trans hsecond)

private theorem product_degree_two_constant_eq_zero_iff (c : ℤ × ℤ) :
    Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c) = 0 ↔ c = 0 := by
  constructor
  · intro hzero
    have hker := hankelIdeal_le_ker (ℤ × ℤ) 2
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change rncMap (ℤ × ℤ) 2 (C c) = 0 at hker
    simpa only [rncMap_C, MvPolynomial.C_eq_zero] using hker
  · intro hc
    simp only [hc, map_zero]

private theorem product_degree_two_orthogonal_idempotents :
    let q := Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2)
    q (C ((1, 0) : ℤ × ℤ)) ≠ 0 ∧
      q (C ((0, 1) : ℤ × ℤ)) ≠ 0 ∧
      q (C ((1, 0) : ℤ × ℤ)) * q (C ((1, 0) : ℤ × ℤ)) =
        q (C ((1, 0) : ℤ × ℤ)) ∧
      q (C ((0, 1) : ℤ × ℤ)) * q (C ((0, 1) : ℤ × ℤ)) =
        q (C ((0, 1) : ℤ × ℤ)) ∧
      q (C ((1, 0) : ℤ × ℤ)) * q (C ((0, 1) : ℤ × ℤ)) = 0 := by
  dsimp only
  have hleft : ((1, 0) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.fst h)
  have hright : ((0, 1) : ℤ × ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have hleft_sq : ((1, 0) : ℤ × ℤ) * (1, 0) = (1, 0) := by ext <;> simp
  have hright_sq : ((0, 1) : ℤ × ℤ) * (0, 1) = (0, 1) := by ext <;> simp
  have hprod : ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by ext <;> simp
  refine ⟨mt (product_degree_two_constant_eq_zero_iff _).mp hleft,
    mt (product_degree_two_constant_eq_zero_iff _).mp hright, ?_, ?_, ?_⟩
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ => Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        hleft_sq
  · simpa only [MvPolynomial.C_mul, map_mul] using
      congrArg (fun c : ℤ × ℤ => Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        hright_sq
  · simpa only [MvPolynomial.C_mul, map_mul, map_zero] using
      congrArg (fun c : ℤ × ℤ => Ideal.Quotient.mk (hankelIdeal (ℤ × ℤ) 2) (C c))
        hprod

private theorem integer_to_zero_degree_two_quotient_map :
    ∃ f : (Source ℤ 2 ⧸ hankelIdeal ℤ 2) →+*
        (Source (ZMod 1) 2 ⧸ hankelIdeal (ZMod 1) 2),
      (∀ p : Source ℤ 2, f (Ideal.Quotient.mk (hankelIdeal ℤ 2) p) =
        Ideal.Quotient.mk (hankelIdeal (ZMod 1) 2)
          (MvPolynomial.map (Int.castRingHom (ZMod 1)) p)) ∧
      (∀ q, f q = 0) ∧ ¬ Function.Injective f := by
  have hI : hankelIdeal ℤ 2 ≤ (hankelIdeal (ZMod 1) 2).comap
      (MvPolynomial.map (Int.castRingHom (ZMod 1))) :=
    Ideal.map_le_iff_le_comap.mp (map_hankelIdeal (Int.castRingHom (ZMod 1)) 2).le
  let f := Ideal.quotientMap (hankelIdeal (ZMod 1) 2)
    (MvPolynomial.map (Int.castRingHom (ZMod 1))) hI
  have hsource : (1 : Source ℤ 2 ⧸ hankelIdeal ℤ 2) ≠ 0 := by
    intro hzero
    have hone : Ideal.Quotient.mk (hankelIdeal ℤ 2) (1 : Source ℤ 2) = 0 := by
      simpa only [map_one] using hzero
    have hker := hankelIdeal_le_ker ℤ 2 (Ideal.Quotient.eq_zero_iff_mem.mp hone)
    change rncMap ℤ 2 1 = 0 at hker
    exact one_ne_zero (by simpa only [map_one] using hker)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p
    exact Ideal.quotientMap_mk
  · intro q
    exact Subsingleton.elim _ _
  · intro hf
    exact hsource (hf (Subsingleton.elim (f 1) (f 0)))

private theorem no_unital_map_from_zero_ring_to_integers :
    ¬ Nonempty (ZMod 1 →+* ℤ) := by
  rintro ⟨f⟩
  have h := congrArg f (Subsingleton.elim (1 : ZMod 1) 0)
  exact one_ne_zero (by simpa only [map_one, map_zero] using h)

end

end ToricIdeals.RationalNormalCurve.BaseChangeSmallModels
