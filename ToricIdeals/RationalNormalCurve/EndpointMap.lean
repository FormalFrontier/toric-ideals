/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ToricIdeals.RationalNormalCurve
import ToricIdeals.RationalNormalCurve.QuotientMap

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Endpoint coordinates in a rational-normal-curve quotient

The endpoint map evaluates the two variables of `MvPolynomial (Fin 2) R`
at the classes of `X₀` and `Xₙ` in the quotient by the Hankel minors.
Coefficients are mapped by the quotient homomorphism. Its characteristic
lemmas and uniqueness property let users work without unfolding the map.

At degree zero the Hankel ideal is bottom and the quotient is the full
one-variable polynomial ring: both endpoint variables map to its single
variable class. At degree one the Hankel ideal is also bottom. The positive
degree hypothesis in the injectivity statement excludes the coincidence
of the two endpoints at degree zero over nontrivial coefficient rings.

For positive degree, `endpointBasis` gives a basis of the full quotient over
`MvPolynomial (Fin 2) R` through the endpoint map. Its vectors are `1` and the
interior coordinate classes `X₁, …, Xₙ₋₁`. The module in its type is the one
induced by `endpointMap.toAlgebra`; the coefficient-ring action is unchanged.
The basis and its coordinate formulas allow arbitrary commutative coefficient
rings, including the zero ring and rings with nilpotents. No numerical rank
or normality assertion is made for these rings.

## References

The Hankel quotient and its monomial parametrization are those of
`ToricIdeals.RationalNormalCurve`, formalized by Formal Frontier Agents.
The construction and uniqueness argument reuse Mathlib's multivariate
polynomial evaluation API by Johannes Hölzl, Johan Commelin and Mario Carneiro,
and its ideal-quotient API by the Mathlib contributors. The integral and
finite-module predicates are Mathlib's, developed by Kenny Lau and
Johan Commelin, respectively. The basis construction and coordinate interface
use Mathlib's `Module.Basis` API by Johannes Hölzl, Mario Carneiro and
Alexander Bentkamp.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

/-- Evaluation at the first and last variable classes in the Hankel quotient. -/
def endpointMap (n : ℕ) :
    MvPolynomial (Fin 2) R →+* (Source R n ⧸ hankelIdeal R n) :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk (hankelIdeal R n)).comp MvPolynomial.C)
    ![Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))),
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))]

/-- The endpoint map preserves the quotient image of each coefficient. -/
@[simp] theorem endpointMap_C (n : ℕ) (r : R) :
    endpointMap (R := R) n (C r) =
      Ideal.Quotient.mk (hankelIdeal R n) (C r) := by
  simp [endpointMap]

/-- A variable is evaluated at the corresponding endpoint class. -/
theorem endpointMap_X (n : ℕ) (i : Fin 2) :
    endpointMap (R := R) n (X i) =
      ![Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))),
        Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))] i := by
  simp [endpointMap]

/-- The first endpoint variable maps to the class of `X₀`. -/
@[simp] theorem endpointMap_X_zero (n : ℕ) :
    endpointMap (R := R) n (X (0 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))) := by
  simp [endpointMap_X]

/-- The second endpoint variable maps to the class of `Xₙ`. -/
@[simp] theorem endpointMap_X_one (n : ℕ) :
    endpointMap (R := R) n (X (1 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n)) := by
  simp [endpointMap_X]

/-- Coefficients and the two endpoint images determine the endpoint map. -/
theorem endpointMap_unique (n : ℕ)
    (f : MvPolynomial (Fin 2) R →+* (Source R n ⧸ hankelIdeal R n))
    (hC : ∀ r, f (C r) = Ideal.Quotient.mk (hankelIdeal R n) (C r))
    (hzero : f (X (0 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))))
    (hone : f (X (1 : Fin 2)) =
      Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n))) :
    f = endpointMap (R := R) n := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [endpointMap_C] using hC r
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [endpointMap_X_zero] using hzero
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using hone

private theorem endpointMap_zero_surjective :
    Function.Surjective (endpointMap (R := R) 0) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨C r, endpointMap_C 0 r⟩
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by simp only [map_add, hp', hq']⟩
  | mul_X p i hp =>
      obtain ⟨p', hp'⟩ := hp
      have hi : i = (0 : Fin (0 + 1)) := Fin.eq_zero i
      subst i
      exact ⟨p' * X (0 : Fin 2), by
        simp only [map_mul, endpointMap_X_zero, hp']⟩

-- The kernel equality is the existing coefficientwise Hankel-normalization
-- theorem. In particular this relation uses neither cancellation nor a domain.
private theorem quotient_coordinate_pow (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (n + 1)) :
    Ideal.Quotient.mk (hankelIdeal R n) (X i) ^ n =
      Ideal.Quotient.mk (hankelIdeal R n) (X (0 : Fin (n + 1))) ^ (n - i.val) *
        Ideal.Quotient.mk (hankelIdeal R n) (X (Fin.last n)) ^ i.val := by
  have hexponent : n • coordinateExponent n i =
      (n - i.val) • coordinateExponent n (0 : Fin (n + 1)) +
        i.val • coordinateExponent n (Fin.last n) := by
    ext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [coordinateExponent, Finsupp.coe_smul, smul_eq_mul,
        Nat.mul_comm]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [coordinateExponent, Finsupp.coe_smul, smul_eq_mul,
        Nat.mul_comm]
  have hmem : (X i : Source R n) ^ n -
      X (0 : Fin (n + 1)) ^ (n - i.val) * X (Fin.last n) ^ i.val ∈
        hankelIdeal R n := by
    rw [hankelIdeal_eq_ker R n hn]
    change rncMap R n ((X i) ^ n -
      X (0 : Fin (n + 1)) ^ (n - i.val) * X (Fin.last n) ^ i.val) = 0
    simp only [map_sub, map_mul, map_pow, rncMap_X, monomial_pow, one_pow,
      monomial_mul_monomial, one_mul]
    rw [hexponent, sub_self]
  simpa only [map_pow, map_mul] using
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hmem

/-- For every commutative coefficient ring and degree, the Hankel quotient is
integral over the two-variable polynomial ring through the endpoint map. -/
theorem endpointMap_isIntegral (n : ℕ) :
    (endpointMap (R := R) n).IsIntegral := by
  by_cases hn : n = 0
  · subst n
    exact (endpointMap (R := R) 0).isIntegral_of_surjective endpointMap_zero_surjective
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hX (i : Fin (n + 1)) :
      (endpointMap (R := R) n).IsIntegralElem
        (Ideal.Quotient.mk (hankelIdeal R n) (X i)) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C
      (X (0 : Fin 2) ^ (n - i.val) * X (1 : Fin 2) ^ i.val),
      Polynomial.monic_X_pow_sub_C _ hn, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    simp only [map_mul, map_pow, endpointMap_X_zero, endpointMap_X_one,
      quotient_coordinate_pow n hn' i, sub_self]
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa only [endpointMap_C] using
        (endpointMap (R := R) n).isIntegralElem_map (x := C r)
  | add p q hp hq =>
      simpa only [map_add] using hp.add (endpointMap (R := R) n) hq
  | mul_X p i hp =>
      simpa only [map_mul] using hp.mul (endpointMap (R := R) n) (hX i)

/-- The Hankel quotient is a finite module over the two-variable polynomial
ring through the endpoint map, for every degree. -/
theorem endpointMap_finite (n : ℕ) :
    (endpointMap (R := R) n).Finite := by
  by_cases hn : n = 0
  · subst n
    exact RingHom.Finite.of_surjective _ endpointMap_zero_surjective
  apply (endpointMap_isIntegral (R := R) n).to_finite
  have hC : (MvPolynomial.C : R →+* Source R n).FiniteType := by
    change (algebraMap R (Source R n)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hcomp : (endpointMap (R := R) n).comp MvPolynomial.C =
      (Ideal.Quotient.mk (hankelIdeal R n)).comp MvPolynomial.C := by
    ext r
    exact endpointMap_C n r
  apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
  rw [hcomp]
  exact (RingHom.FiniteType.of_surjective
    (Ideal.Quotient.mk (hankelIdeal R n)) Ideal.Quotient.mk_surjective).comp hC

-- The existing quotient parametrization turns endpoint scalars into expansion.
-- This identity holds even at degree zero; injectivity is not used here.
private theorem quotientMap_endpointMap (n : ℕ) (p : MvPolynomial (Fin 2) R) :
    quotientMap R n (endpointMap (R := R) n p) = MvPolynomial.expand n p := by
  have hcomp :
      (quotientMap R n).toRingHom.comp (endpointMap (R := R) n) =
        (MvPolynomial.expand n (R := R) (σ := Fin 2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change quotientMap R n (endpointMap (R := R) n (C r)) =
        MvPolynomial.expand n (C r)
      rw [endpointMap_C, quotientMap_C, MvPolynomial.expand_C]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change quotientMap R n (endpointMap (R := R) n (X (0 : Fin 2))) =
          MvPolynomial.expand n (X (0 : Fin 2))
        rw [endpointMap_X_zero, quotientMap_X, MvPolynomial.expand_X]
        simp [coordinateExponent, X_pow_eq_monomial]
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change quotientMap R n (endpointMap (R := R) n (X (1 : Fin 2))) =
          MvPolynomial.expand n (X (1 : Fin 2))
        rw [endpointMap_X_one, quotientMap_X, MvPolynomial.expand_X]
        simp [coordinateExponent, X_pow_eq_monomial]
  exact DFunLike.congr_fun hcomp p

/-- In positive degree the endpoint map is injective, without any domain or
nontriviality assumption on the coefficient ring. -/
theorem endpointMap_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (endpointMap (R := R) n) := by
  intro p q hpq
  apply MvPolynomial.expand_injective (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [← quotientMap_endpointMap n p, ← quotientMap_endpointMap n q, hpq]

-- These are only the target exponents of the displayed vectors, not a choice
-- of source representatives. In particular the unit has exponent zero.
private def endpointVectorExponent (n : ℕ) (i : Fin n) : Fin 2 →₀ ℕ :=
  if i.val = 0 then 0 else coordinateExponent n i.castSucc

private theorem endpointVectorExponent_second (n : ℕ) (i : Fin n) :
    endpointVectorExponent n i 1 = i.val := by
  by_cases hi : i.val = 0 <;> simp [endpointVectorExponent, coordinateExponent, hi]

-- The second coordinate modulo n recovers i; cancellation then recovers d.
private theorem endpoint_shifted_exponent_eq_iff (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin n) (d e : Fin 2 →₀ ℕ) :
    n • d + endpointVectorExponent n i = n • e + endpointVectorExponent n j ↔
      i = j ∧ d = e := by
  constructor
  · intro h
    have hsecond : n * d 1 + i.val = n * e 1 + j.val := by
      simpa only [Finsupp.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        endpointVectorExponent_second] using
        congrArg (fun a : Fin 2 →₀ ℕ ↦ a 1) h
    have hij : i = j := by
      apply Fin.ext
      have hmod := congrArg (fun a : ℕ ↦ a % n) hsecond
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt i.isLt,
        Nat.mod_eq_of_lt j.isLt] using hmod
    refine ⟨hij, ?_⟩
    subst j
    exact (nsmul_right_inj (by omega : n ≠ 0)).mp (add_right_cancel h)
  · rintro ⟨rfl, rfl⟩
    rfl

-- Coefficients in the distinct residue classes cannot cancel, regardless of
-- zero divisors or nilpotents in R. The proof is monomialwise over R itself.
private theorem coeff_expand_mul_endpoint_monomial (n : ℕ) (hn : 1 ≤ n)
    (p : MvPolynomial (Fin 2) R) (i j : Fin n) (d : Fin 2 →₀ ℕ) :
    (MvPolynomial.expand n p * monomial (endpointVectorExponent n j) 1).coeff
        (n • d + endpointVectorExponent n i) =
      if j = i then p.coeff d else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      simp only [MvPolynomial.expand_monomial, monomial_mul_monomial, mul_one,
        coeff_monomial, endpoint_shifted_exponent_eq_iff n hn]
      by_cases hji : j = i <;> simp [hji]
  | add p q hp hq =>
      simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
      by_cases hji : j = i <;> simp [hji]

-- Equal sums of coordinate indices give the same quadratic monomial in the
-- quotient. The kernel calculation works coefficientwise over every ring.
private theorem quotient_coordinate_mul_eq_of_add_eq (n : ℕ) (hn : 1 ≤ n)
    (i j k l : Fin (n + 1)) (hsum : i.val + j.val = k.val + l.val) :
    Ideal.Quotient.mk (hankelIdeal R n) (X i) *
        Ideal.Quotient.mk (hankelIdeal R n) (X j) =
      Ideal.Quotient.mk (hankelIdeal R n) (X k) *
        Ideal.Quotient.mk (hankelIdeal R n) (X l) := by
  have hexponent : coordinateExponent n i + coordinateExponent n j =
      coordinateExponent n k + coordinateExponent n l := by
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have hl : l.val ≤ n := Nat.le_of_lt_succ l.isLt
    ext q
    fin_cases q <;> simp [coordinateExponent] <;> omega
  have hmem : (X i * X j - X k * X l : Source R n) ∈ hankelIdeal R n := by
    rw [hankelIdeal_eq_ker R n hn]
    change rncMap R n (X i * X j - X k * X l) = 0
    simp only [map_sub, map_mul, rncMap_X, monomial_mul_monomial, one_mul]
    rw [hexponent, sub_self]
  simpa only [map_mul] using
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hmem

/-- In positive degree, the unit and interior coordinate classes are linearly
independent over the endpoint polynomial ring, with scalars acting through
`endpointMap`. This holds over every commutative coefficient ring. -/
theorem endpointFamily_linearIndependent (n : ℕ) (hn : 1 ≤ n) :
    @LinearIndependent (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n)
      (fun i : Fin n ↦
        if i.val = 0 then 1 else Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra) := by
  let : Algebra (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    (endpointMap (R := R) n).toAlgebra
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  let v : Fin n → Source R n ⧸ hankelIdeal R n := fun i ↦
    if i.val = 0 then 1 else Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)
  change LinearIndependent (MvPolynomial (Fin 2) R) v
  classical
  have hv (i : Fin n) :
      quotientMap R n (v i) = monomial (endpointVectorExponent n i) 1 := by
    by_cases hi : i.val = 0 <;>
      simp [v, endpointVectorExponent, hi]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hparam :
      ∑ j, MvPolynomial.expand n (c j) * monomial (endpointVectorExponent n j) 1 = 0 := by
    simpa only [map_sum, map_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      map_mul, quotientMap_endpointMap, hv] using congrArg (quotientMap R n) hc
  apply MvPolynomial.ext
  intro d
  have hd := congrArg
    (fun p : Target R ↦ p.coeff (n • d + endpointVectorExponent n i)) hparam
  simpa [MvPolynomial.coeff_sum, coeff_expand_mul_endpoint_monomial n hn] using hd

/-- In positive degree, the unit and interior coordinate classes span the full
Hankel quotient over the endpoint polynomial ring, with scalars acting through
`endpointMap`. This holds over every commutative coefficient ring. -/
theorem endpointFamily_span (n : ℕ) (hn : 1 ≤ n) :
    (⊤ : @Submodule (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra)) ≤
      @Submodule.span (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) _ _
        (@Algebra.toModule (MvPolynomial (Fin 2) R)
          (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra)
        (Set.range (fun i : Fin n ↦
          if i.val = 0 then 1 else Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc))) := by
  let : Algebra (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    (endpointMap (R := R) n).toAlgebra
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  let v : Fin n → Source R n ⧸ hankelIdeal R n := fun i ↦
    if i.val = 0 then 1 else Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)
  change ⊤ ≤ Submodule.span (MvPolynomial (Fin 2) R) (Set.range v)
  let S : Submodule (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    Submodule.span (MvPolynomial (Fin 2) R) (Set.range v)
  have hunit : (1 : Source R n ⧸ hankelIdeal R n) ∈ S := by
    have hv : v ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩ ∈ S :=
      Submodule.subset_span (Set.mem_range_self _)
    simpa only [v, ↓reduceIte] using hv
  have hscalar (p : MvPolynomial (Fin 2) R)
      (q : Source R n ⧸ hankelIdeal R n) (hq : q ∈ S) :
      endpointMap (R := R) n p * q ∈ S := by
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
      S.smul_mem p hq
  have hcoordinate (i : Fin (n + 1)) :
      Ideal.Quotient.mk (hankelIdeal R n) (X i) ∈ S := by
    by_cases hi0 : i.val = 0
    · have hi : i = (0 : Fin (n + 1)) := Fin.ext hi0
      subst i
      simpa only [endpointMap_X_zero, mul_one] using
        hscalar (X (0 : Fin 2)) 1 hunit
    · by_cases hin : i.val = n
      · have hi : i = Fin.last n := Fin.ext hin
        subst i
        simpa only [endpointMap_X_one, mul_one] using
          hscalar (X (1 : Fin 2)) 1 hunit
      · let j : Fin n := ⟨i.val, by have := i.isLt; omega⟩
        have hj0 : j.val ≠ 0 := hi0
        have hcast : j.castSucc = i := Fin.ext rfl
        have hv : v j ∈ S := Submodule.subset_span (Set.mem_range_self j)
        simpa only [v, hj0, ↓reduceIte, hcast] using hv
  -- Multiplying an interior coordinate by any coordinate extracts either
  -- the first or the last endpoint, leaving a single coordinate class.
  have hpair (j : Fin n) (i : Fin (n + 1)) :
      v j * Ideal.Quotient.mk (hankelIdeal R n) (X i) ∈ S := by
    by_cases hj0 : j.val = 0
    · simpa only [v, hj0, ↓reduceIte, one_mul] using hcoordinate i
    · simp only [v, hj0, ↓reduceIte]
      by_cases hsum : j.val + i.val ≤ n
      · let k : Fin (n + 1) := ⟨j.val + i.val, by omega⟩
        rw [quotient_coordinate_mul_eq_of_add_eq n hn j.castSucc i 0 k
          (by simp only [Fin.val_castSucc, Fin.val_zero, k]; omega)]
        simpa only [endpointMap_X_zero] using
          hscalar (X (0 : Fin 2)) _ (hcoordinate k)
      · let k : Fin (n + 1) := ⟨j.val + i.val - n, by
          have := j.isLt
          have := i.isLt
          omega⟩
        rw [quotient_coordinate_mul_eq_of_add_eq n hn j.castSucc i (Fin.last n) k
          (by simp only [Fin.val_castSucc, Fin.val_last, k]; omega)]
        simpa only [endpointMap_X_one] using
          hscalar (X (1 : Fin 2)) _ (hcoordinate k)
  have hmul (q : Source R n ⧸ hankelIdeal R n) (hq : q ∈ S)
      (i : Fin (n + 1)) :
      q * Ideal.Quotient.mk (hankelIdeal R n) (X i) ∈ S := by
    induction hq using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨j, rfl⟩ := hq
        exact hpair j i
    | zero => simpa only [zero_mul] using S.zero_mem
    | add q q' hq hq' hp hp' =>
        simpa only [add_mul] using S.add_mem hp hp'
    | smul p q hq hp =>
        simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc] using
          S.smul_mem p hp
  intro q hq
  clear hq
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (hankelIdeal R n) p ∈ S
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa only [endpointMap_C, mul_one] using hscalar (C r) 1 hunit
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul] using hmul _ hp i

/-- The basis `1, X₁, …, Xₙ₋₁` of the full Hankel quotient over its endpoint
polynomial ring. Scalars act by `p • q = endpointMap n p * q`.

The positive-degree hypothesis excludes the coincident endpoints at degree
zero. The construction allows arbitrary commutative coefficient rings; over
the zero ring this is an indexed basis, not a numerical rank assertion. -/
noncomputable def endpointBasis (R : Type u) [CommRing R] (n : ℕ) (hn : 1 ≤ n) :
    @Module.Basis (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) := by
  let : Algebra (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    (endpointMap (R := R) n).toAlgebra
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  let v : Fin n → Source R n ⧸ hankelIdeal R n := fun i ↦
    if i.val = 0 then 1 else Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)
  have endpoint_linearIndependent : LinearIndependent (MvPolynomial (Fin 2) R) v := by
    exact endpointFamily_linearIndependent (R := R) n hn
  have endpoint_span :
      ⊤ ≤ Submodule.span (MvPolynomial (Fin 2) R) (Set.range v) := by
    exact endpointFamily_span (R := R) n hn
  exact Module.Basis.mk endpoint_linearIndependent endpoint_span

/-- The endpoint basis consists of the unit followed by the interior classes. -/
theorem endpointBasis_apply (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    endpointBasis R n hn i =
      if i.val = 0 then 1 else
        Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc) := by
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  unfold endpointBasis
  exact Module.Basis.mk_apply _ _ i

/-- The first endpoint basis vector is the unit class. -/
@[simp] theorem endpointBasis_apply_zero (n : ℕ) (hn : 1 ≤ n) :
    endpointBasis R n hn ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩ = 1 := by
  simp only [endpointBasis_apply, ↓reduceIte]

/-- A positive index selects its interior coordinate class. -/
@[simp] theorem endpointBasis_apply_of_pos (n : ℕ) (hn : 1 ≤ n)
    (i : Fin n) (hi : 0 < i.val) :
    endpointBasis R n hn i =
      Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc) := by
  simp only [endpointBasis_apply, Nat.ne_of_gt hi, ↓reduceIte]

/-- The unit has just its first endpoint coordinate. -/
@[simp] theorem endpointBasis_repr_one (n : ℕ) (hn : 1 ≤ n) :
    (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn)) 1 =
      Finsupp.single ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩ 1 := by
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  simpa only [endpointBasis_apply_zero] using
    (endpointBasis R n hn).repr_self ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩

/-- An interior variable class has its corresponding unit coordinate. -/
@[simp] theorem endpointBasis_repr_X (n : ℕ) (hn : 1 ≤ n)
    (i : Fin n) (hi : 0 < i.val) :
    (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn))
        (Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)) =
      Finsupp.single i 1 := by
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  simpa only [endpointBasis_apply_of_pos (R := R) n hn i hi] using
    (endpointBasis R n hn).repr_self i

/-- An endpoint polynomial occupies only the first basis coordinate. -/
@[simp] theorem endpointBasis_repr_endpointMap (n : ℕ) (hn : 1 ≤ n)
    (p : MvPolynomial (Fin 2) R) :
    (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn))
        (endpointMap (R := R) n p) =
      Finsupp.single ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩ p := by
  let : Algebra (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    (endpointMap (R := R) n).toAlgebra
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one,
    endpointBasis_repr_one, Finsupp.smul_single'] using
    (endpointBasis R n hn).repr.map_smul p (1 : Source R n ⧸ hankelIdeal R n)

/-- Multiplication by an endpoint polynomial multiplies each basis coordinate. -/
@[simp] theorem endpointBasis_repr_endpointMap_mul (n : ℕ) (hn : 1 ≤ n)
    (p : MvPolynomial (Fin 2) R) (q : Source R n ⧸ hankelIdeal R n) (i : Fin n) :
    (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn))
        (endpointMap (R := R) n p * q) i =
      p * (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (@Algebra.toModule (MvPolynomial (Fin 2) R)
          (Source R n ⧸ hankelIdeal R n) _ _
          (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn)) q i := by
  let : Algebra (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    (endpointMap (R := R) n).toAlgebra
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  have h := congrArg (fun c : Fin n →₀ MvPolynomial (Fin 2) R ↦ c i)
    ((endpointBasis R n hn).repr.map_smul p q)
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
    Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply] using h

end

end

end ToricIdeals.RationalNormalCurve
