/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.RationalNormalCurve.Homogeneous
import ToricIdeals.RationalNormalCurve.ExponentImage
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.Module

/-!
# Monomial bases of homogeneous Hankel-quotient components

The degree-`d` component is the image of the standard homogeneous polynomial
submodule in the full Hankel quotient, with its coefficient-ring action.
`quotientHomogeneousBasis` gives this component a basis indexed by
`Fin (n * d + 1)`, over every commutative ring and for all `n` and `d`.
Its coordinates and reconstruction formulas work over zero rings and rings
with nilpotents as well as over fields. No dimension assertion or distinctness
of basis vectors over a zero ring is intended.

For positive `n`, coordinates are the coefficients of the parametrization at
`(n*d-i, i)`. The basis vectors use the terminal source exponents of the
existing Hankel normalizer. At `n = 0`, the full quotient is the one-variable
polynomial ring, and the basis vector is the class of `X 0 ^ d`; the
parametrization, which sends `X 0` to `1`, is not used for these coordinates.
No additional grading or scalar action on the quotient is introduced.
Multiplication in the full quotient adds the degrees and the basis indices,
including at `n = 0`, where it multiplies powers of the surviving variable.

Changing coefficients along any homomorphism of commutative rings preserves
these basis vectors with their indices unchanged in the full Hankel quotient.
For positive `n`, this compares quotient classes through the Hankel kernel
theorem, rather than identifying the choices of terminal representatives over
the two coefficient rings. At `n = 0`, it preserves the class of `X 0 ^ d`.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
  3.6.F, for the Hankel presentation motivating the coordinate ring.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the
  coefficient-independent exponent identities, terminal normalization and
  all-ring Hankel kernel theorem.
* Mathlib contributors, supported monomial bases, finite antidiagonals,
  coefficient algebra homomorphisms and the algebraic first isomorphism theorem.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

/-- The standard degree-`d` submodule of the full Hankel quotient, with the
canonical coefficient action induced by the quotient algebra map. -/
abbrev quotientHomogeneousSubmodule (R : Type u) [CommRing R] (n d : ℕ) :
    Submodule R (Source R n ⧸ hankelIdeal R n) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
    (Ideal.Quotient.mkₐ R (hankelIdeal R n)).toLinearMap

/-- Membership means having a homogeneous polynomial representative. -/
theorem mem_quotientHomogeneousSubmodule_iff (R : Type u) [CommRing R] (n d : ℕ)
    (x : Source R n ⧸ hankelIdeal R n) :
    x ∈ quotientHomogeneousSubmodule R n d ↔ ∃ p : Source R n,
      p.IsHomogeneous d ∧ Ideal.Quotient.mkₐ R (hankelIdeal R n) p = x :=
  Submodule.mem_map

/-- A homogeneous polynomial regarded as an element of the corresponding
submodule of the full quotient. -/
def quotientHomogeneousRepresentative (R : Type u) [CommRing R] (n d : ℕ)
    (p : Source R n) (hp : p.IsHomogeneous d) : quotientHomogeneousSubmodule R n d :=
  ⟨Ideal.Quotient.mkₐ R (hankelIdeal R n) p, Submodule.mem_map_of_mem hp⟩

/-- The underlying quotient class of a homogeneous representative. -/
@[simp]
theorem quotientHomogeneousRepresentative_coe (R : Type u) [CommRing R] (n d : ℕ)
    (p : Source R n) (hp : p.IsHomogeneous d) :
    (quotientHomogeneousRepresentative R n d p hp : Source R n ⧸ hankelIdeal R n) =
      Ideal.Quotient.mkₐ R (hankelIdeal R n) p := rfl

/-- Elements of a homogeneous quotient submodule are equal when their
underlying quotient classes are equal. -/
@[ext]
theorem quotientHomogeneousSubmodule_ext (R : Type u) [CommRing R] (n d : ℕ)
    (x y : quotientHomogeneousSubmodule R n d)
    (h : (x : Source R n ⧸ hankelIdeal R n) = y) : x = y :=
  Subtype.ext h

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

private def twoExponentAntidiagonal (k : ℕ) :
    {e : Fin 2 →₀ ℕ // e.degree = k} ≃ (Finset.antidiagonal k) where
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

private def twoExponentIndex (k : ℕ) :
    {e : Fin 2 →₀ ℕ // e.degree = k} ≃ Fin (k + 1) :=
  (twoExponentAntidiagonal k).trans (Finset.Nat.antidiagonalEquivFin k)

private theorem twoExponentIndex_symm (k : ℕ) (i : Fin (k + 1)) :
    ((twoExponentIndex k).symm i).1 =
      Finsupp.single 0 (k - i.val) + Finsupp.single 1 i.val := rfl

private def targetHomogeneousBasis (R : Type u) [CommRing R] (k : ℕ) :
    Module.Basis (Fin (k + 1)) R (MvPolynomial.homogeneousSubmodule (Fin 2) R k) :=
  ((MvPolynomial.basisRestrictSupport R {e : Fin 2 →₀ ℕ | e.degree = k}).map
    (LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) R k).symm)).reindex
    (twoExponentIndex k)

private theorem targetHomogeneousBasis_apply (R : Type u) [CommRing R] (k : ℕ)
    (i : Fin (k + 1)) :
    (targetHomogeneousBasis R k i : Target R) =
      monomial (Finsupp.single 0 (k - i.val) + Finsupp.single 1 i.val) 1 := by
  simp only [targetHomogeneousBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply]
  apply MvPolynomial.ext
  intro e
  change ((Finsupp.supportedEquivFinsupp (R := R) (M := R)
      {e : Fin 2 →₀ ℕ | e.degree = k}).symm
      (Finsupp.single ((twoExponentIndex k).symm i) (1 : R)) :
        (Fin 2 →₀ ℕ) →₀ R) e = _
  rw [Finsupp.supportedEquivFinsupp_symm_single, twoExponentIndex_symm]
  rfl

private theorem targetHomogeneousBasis_repr (R : Type u) [CommRing R] (k : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) R k) (i : Fin (k + 1)) :
    (targetHomogeneousBasis R k).repr p i =
      p.1.coeff (Finsupp.single 0 (k - i.val) + Finsupp.single 1 i.val) := by
  rw [targetHomogeneousBasis, Module.Basis.repr_reindex_apply]
  change p.1.coeff (((twoExponentIndex k).symm i).1) = _
  rfl

-- Both maps below are stock coefficient-algebra maps. In particular no
-- coefficient linearity is inferred from a ring equivalence.
private def quotientCoefficientEmbedding (R : Type u) [CommRing R] (n : ℕ)
    (hn : 1 ≤ n) : (Source R n ⧸ hankelIdeal R n) →ₐ[R] Target R :=
  (Ideal.kerLiftAlg (AddMonoidAlgebra.mapDomainAlgHom R R (rncExponent n))).comp
    (Ideal.quotientEquivAlgOfEq R (hankelIdeal_eq_ker R n hn)).toAlgHom

private theorem quotientCoefficientEmbedding_mk (R : Type u) [CommRing R] (n : ℕ)
    (hn : 1 ≤ n) (p : Source R n) :
    quotientCoefficientEmbedding R n hn (Ideal.Quotient.mkₐ R (hankelIdeal R n) p) =
      rncMap R n p := rfl

private theorem quotientCoefficientEmbedding_injective (R : Type u) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n) : Function.Injective (quotientCoefficientEmbedding R n hn) :=
  (Ideal.kerLiftAlg_injective
    (AddMonoidAlgebra.mapDomainAlgHom R R (rncExponent n))).comp
      (Ideal.quotientEquivAlgOfEq R (hankelIdeal_eq_ker R n hn)).injective

private theorem fiberNormalExponent_degree (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (t : Fin 2 →₀ ℕ) (ht : t.degree = n * d) :
    (fiberNormalExponent R n t).degree = d ∧
      rncExponent n (fiberNormalExponent R n t) = t := by
  have htotal : t 0 + t 1 = n * d := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using ht
  obtain ⟨e, he⟩ := AddMonoidHom.mem_mrange.mp
    ((mem_mrange_rncExponent_iff n t).mpr ⟨d, htotal⟩)
  have himage : rncExponent n (fiberNormalExponent R n t) = t := by
    rw [← he, fiberNormalExponent_image R n hn, normalSourceExponent_rncExponent]
  refine ⟨?_, himage⟩
  apply Nat.mul_left_cancel (by omega : 0 < n)
  calc
    n * (fiberNormalExponent R n t).degree =
        rncExponent n (fiberNormalExponent R n t) 0 +
          rncExponent n (fiberNormalExponent R n t) 1 :=
      (rncExponent_total n _).symm
    _ = n * d := by rw [himage, htotal]

private def positiveRepresentative (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (i : Fin (n * d + 1)) : quotientHomogeneousSubmodule R n d :=
  quotientHomogeneousRepresentative R n d
    (monomial (fiberNormalExponent R n ((twoExponentIndex (n * d)).symm i).1) 1)
    (isHomogeneous_monomial 1
      (fiberNormalExponent_degree R n d hn _ ((twoExponentIndex (n * d)).symm i).2).1)

private def positivePieceMap (R : Type u) [CommRing R] (n d : ℕ) (hn : 1 ≤ n) :
    quotientHomogeneousSubmodule R n d →ₗ[R]
      MvPolynomial.homogeneousSubmodule (Fin 2) R (n * d) :=
  ((quotientCoefficientEmbedding R n hn).toLinearMap.domRestrict
    (quotientHomogeneousSubmodule R n d)).codRestrict _ (by
      intro x
      obtain ⟨p, hp, hpx⟩ := (mem_quotientHomogeneousSubmodule_iff R n d x.1).mp x.2
      change (quotientCoefficientEmbedding R n hn x.1).IsHomogeneous (n * d)
      rw [← hpx, quotientCoefficientEmbedding_mk]
      exact rncMap_isHomogeneous R n d p hp)

private theorem positivePieceMap_representative (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (p : Source R n) (hp : p.IsHomogeneous d) :
    (positivePieceMap R n d hn (quotientHomogeneousRepresentative R n d p hp) : Target R) =
      rncMap R n p :=
  quotientCoefficientEmbedding_mk R n hn p

private theorem positivePieceMap_vector (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (i : Fin (n * d + 1)) :
    positivePieceMap R n d hn (positiveRepresentative R n d hn i) =
      targetHomogeneousBasis R (n * d) i := by
  apply Subtype.ext
  rw [targetHomogeneousBasis_apply]
  change rncMap R n
    (monomial (fiberNormalExponent R n ((twoExponentIndex (n * d)).symm i).1) 1) = _
  rw [rncMap_monomial,
    (fiberNormalExponent_degree R n d hn _ ((twoExponentIndex (n * d)).symm i).2).2,
    twoExponentIndex_symm]

private theorem positivePieceMap_bijective (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) : Function.Bijective (positivePieceMap R n d hn) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply quotientCoefficientEmbedding_injective R n hn
    exact congrArg Subtype.val h
  · intro p
    refine ⟨∑ i, (targetHomogeneousBasis R (n * d)).repr p i •
      positiveRepresentative R n d hn i, ?_⟩
    simp only [map_sum, map_smul, positivePieceMap_vector]
    exact (targetHomogeneousBasis R (n * d)).sum_repr p

private def positivePieceEquiv (R : Type u) [CommRing R] (n d : ℕ) (hn : 1 ≤ n) :
    quotientHomogeneousSubmodule R n d ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule (Fin 2) R (n * d) :=
  LinearEquiv.ofBijective (positivePieceMap R n d hn)
    (positivePieceMap_bijective R n d hn)

private def positiveBasis (R : Type u) [CommRing R] (n d : ℕ) (hn : 1 ≤ n) :
    Module.Basis (Fin (n * d + 1)) R (quotientHomogeneousSubmodule R n d) :=
  (targetHomogeneousBasis R (n * d)).map (positivePieceEquiv R n d hn).symm

private theorem positiveBasis_apply (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (i : Fin (n * d + 1)) :
    positiveBasis R n d hn i = positiveRepresentative R n d hn i := by
  apply (positivePieceEquiv R n d hn).injective
  rw [positiveBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact (positivePieceMap_vector R n d hn i).symm

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

private def zeroBasis (R : Type u) [CommRing R] (d : ℕ) :
    Module.Basis (Fin 1) R (quotientHomogeneousSubmodule R 0 d) :=
  (((MvPolynomial.basisRestrictSupport R {e : Fin 1 →₀ ℕ | e.degree = d}).map
    (LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 1) R d).symm)).reindex
        (oneExponentIndex d)).map
    (Submodule.equivMapOfInjective
      (Ideal.Quotient.mkₐ R (hankelIdeal R 0)).toLinearMap (zero_mk_injective R) _)

private theorem zeroBasis_apply (R : Type u) [CommRing R] (d : ℕ) (i : Fin 1) :
    (zeroBasis R d i : Source R 0 ⧸ hankelIdeal R 0) =
      Ideal.Quotient.mkₐ R (hankelIdeal R 0) (X 0 ^ d) := by
  simp only [zeroBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
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

/-- Coefficient coordinates obtained from the one-variable or positive-parameter basis. -/
private def homogeneousCoordinates (R : Type u) [CommRing R] (n d : ℕ) :
    quotientHomogeneousSubmodule R n d ≃ₗ[R] (Fin (n * d + 1) →₀ R) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ((zeroBasis R d).reindex (finCongr (by simp))).repr
  · exact (positiveBasis R n d (Nat.one_le_iff_ne_zero.mpr hn)).repr

/-- A monomial basis for the standard degree-`d` submodule of the full Hankel
quotient over an arbitrary commutative ring. For positive `n`, its `i`th vector
is represented by the terminal monomial mapping to exponent `(n*d-i,i)`.
For `n = 0`, its single vector is the class of `X 0 ^ d`.
The Hankel presentation is motivated by Vakil's *The Rising Sea*, Exercise 3.6.F. -/
def quotientHomogeneousBasis (R : Type u) [CommRing R] (n d : ℕ) :
    Module.Basis (Fin (n * d + 1)) R (quotientHomogeneousSubmodule R n d) where
  repr := private homogeneousCoordinates R n d

private theorem quotientHomogeneousBasis_eq (R : Type u) [CommRing R] (n d : ℕ) :
    quotientHomogeneousBasis R n d = { repr := homogeneousCoordinates R n d } := by
  rfl

private theorem quotientHomogeneousBasis_zero_eq (R : Type u) [CommRing R] (d : ℕ) :
    quotientHomogeneousBasis R 0 d =
      (zeroBasis R d).reindex (finCongr (by simp)) := by
  rw [quotientHomogeneousBasis_eq]
  apply Module.Basis.repr_injective
  simp [homogeneousCoordinates]

private theorem quotientHomogeneousBasis_eq_of_pos (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) : quotientHomogeneousBasis R n d = positiveBasis R n d hn := by
  have hn0 : n ≠ 0 := by omega
  rw [quotientHomogeneousBasis_eq]
  apply Module.Basis.repr_injective
  simp only [homogeneousCoordinates, dite_eq_right hn0]

/-- At `n = 0`, the vector is the degree-`d` power of the surviving variable. -/
@[simp]
theorem quotientHomogeneousBasis_zero_apply (R : Type u) [CommRing R] (d : ℕ)
    (i : Fin (0 * d + 1)) :
    (quotientHomogeneousBasis R 0 d i : Source R 0 ⧸ hankelIdeal R 0) =
      Ideal.Quotient.mkₐ R (hankelIdeal R 0) (X 0 ^ d) := by
  rw [quotientHomogeneousBasis_zero_eq, Module.Basis.reindex_apply]
  exact zeroBasis_apply R d _

/-- Positive-`n` basis vectors are the existing terminal monomial representatives. -/
theorem quotientHomogeneousBasis_apply_of_pos (R : Type u) [CommRing R] (n d : ℕ)
    (hn : 1 ≤ n) (i : Fin (n * d + 1)) :
    (quotientHomogeneousBasis R n d i : Source R n ⧸ hankelIdeal R n) =
      Ideal.Quotient.mkₐ R (hankelIdeal R n)
        (monomial (fiberNormalExponent R n
          (Finsupp.single 0 (n * d - i.val) + Finsupp.single 1 i.val)) 1) := by
  rw [quotientHomogeneousBasis_eq_of_pos R n d hn, positiveBasis_apply]
  exact congrArg
    (fun e => Ideal.Quotient.mkₐ R (hankelIdeal R n)
      (monomial (fiberNormalExponent R n e) 1))
    (twoExponentIndex_symm (n * d) i)

/-- Changing coefficients sends each homogeneous Hankel-quotient basis vector
to the vector with the same index. The equality is in the full quotient, for
arbitrary commutative coefficient rings and every `n` and `d`, including zero.
The coefficient-change map has the full Hankel quotient over `S` as its target;
it is distinct from the parametrization `quotientMap R n` into the bivariate
polynomial ring.
For positive `n`, the Hankel kernel theorem compares the quotient classes of
the independently chosen terminal representatives. -/
theorem quotientMap_quotientHomogeneousBasis
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S)
    (n d : ℕ) (i : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)
      (quotientHomogeneousBasis R n d i : Source R n ⧸ hankelIdeal R n) =
        (quotientHomogeneousBasis S n d i : Source S n ⧸ hankelIdeal S n) := by
  by_cases hn : n = 0
  · subst n
    rw [quotientHomogeneousBasis_zero_apply, quotientHomogeneousBasis_zero_apply]
    rw [Ideal.Quotient.mkₐ_eq_mk R, Ideal.quotientMap_mk,
      ← Ideal.Quotient.mkₐ_eq_mk S]
    simp only [map_pow, MvPolynomial.map_X]
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [quotientHomogeneousBasis_apply_of_pos R n d hn',
      quotientHomogeneousBasis_apply_of_pos S n d hn']
    have ht := ((twoExponentIndex (n * d)).symm i).2
    rw [twoExponentIndex_symm] at ht
    -- Equality is checked in the parametrization only after excluding `n = 0`.
    apply quotientCoefficientEmbedding_injective S n hn'
    rw [Ideal.Quotient.mkₐ_eq_mk R, Ideal.quotientMap_mk,
      ← Ideal.Quotient.mkₐ_eq_mk S]
    simp only [MvPolynomial.map_monomial, map_one,
      quotientCoefficientEmbedding_mk, rncMap_monomial,
      (fiberNormalExponent_degree R n d hn' _ ht).2,
      (fiberNormalExponent_degree S n d hn' _ ht).2]

/-- Multiplication of homogeneous basis vectors in the full Hankel quotient
adds their degrees and indices. This holds over every commutative ring,
including zero rings and rings with nilpotents, and for all `n`, `d`, and `e`.
At `n = 0`, it is the power law for the surviving variable. -/
theorem quotientHomogeneousBasis_mul (R : Type u) [CommRing R] (n d e : ℕ)
    (i : Fin (n * d + 1)) (j : Fin (n * e + 1)) :
    let k : Fin (n * (d + e) + 1) :=
      ⟨i.val + j.val, Nat.lt_succ_of_le (by
        simpa only [Nat.mul_add] using
          Nat.add_le_add (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt))⟩
    (quotientHomogeneousBasis R n d i : Source R n ⧸ hankelIdeal R n) *
        (quotientHomogeneousBasis R n e j : Source R n ⧸ hankelIdeal R n) =
      (quotientHomogeneousBasis R n (d + e) k : Source R n ⧸ hankelIdeal R n) := by
  dsimp only
  by_cases hn0 : n = 0
  · subst n
    simp only [quotientHomogeneousBasis_zero_apply, ← map_mul, ← pow_add]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hvector (a : ℕ) (l : Fin (n * a + 1)) :
        quotientCoefficientEmbedding R n hn
            (quotientHomogeneousBasis R n a l : Source R n ⧸ hankelIdeal R n) =
          monomial (Finsupp.single 0 (n * a - l.val) + Finsupp.single 1 l.val) 1 := by
      rw [quotientHomogeneousBasis_apply_of_pos R n a hn,
        quotientCoefficientEmbedding_mk, rncMap_monomial]
      have h := (fiberNormalExponent_degree R n a hn
        ((twoExponentIndex (n * a)).symm l).1 ((twoExponentIndex (n * a)).symm l).2).2
      simpa only [twoExponentIndex_symm] using
        congrArg (fun t : Fin 2 →₀ ℕ => monomial t (1 : R)) h
    apply quotientCoefficientEmbedding_injective R n hn
    simp only [map_mul, hvector, monomial_mul_monomial, mul_one]
    apply congrArg (fun t : Fin 2 →₀ ℕ => monomial t (1 : R))
    have hi : i.val ≤ n * d := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ n * e := Nat.le_of_lt_succ j.isLt
    have hdiff : n * d - i.val + (n * e - j.val) =
        n * (d + e) - (i.val + j.val) := by
      rw [Nat.mul_add]
      omega
    ext a
    fin_cases a <;> simp [hdiff]

/-- Coordinates of a homogeneous representative for positive `n` are the
coefficients of its parametrization, in increasing order of the second exponent. -/
theorem quotientHomogeneousBasis_repr_representative_of_pos (R : Type u) [CommRing R]
    (n d : ℕ) (hn : 1 ≤ n) (p : Source R n) (hp : p.IsHomogeneous d)
    (i : Fin (n * d + 1)) :
    (quotientHomogeneousBasis R n d).repr
      (quotientHomogeneousRepresentative R n d p hp) i =
        (rncMap R n p).coeff
          (Finsupp.single 0 (n * d - i.val) + Finsupp.single 1 i.val) := by
  have hn0 : n ≠ 0 := by omega
  rw [quotientHomogeneousBasis_eq]
  simp only [homogeneousCoordinates, dite_eq_right hn0,
    positiveBasis, Module.Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rw [targetHomogeneousBasis_repr]
  exact congrArg (fun q : Target R => q.coeff
    (Finsupp.single 0 (n * d - i.val) + Finsupp.single 1 i.val))
      (positivePieceMap_representative R n d (Nat.one_le_iff_ne_zero.mpr hn0) p hp)

/-- At `n = 0`, the coordinate is the coefficient of the degree-`d` monomial,
not a coefficient of the degree-collapsing parametrization. -/
theorem quotientHomogeneousBasis_repr_representative_zero (R : Type u) [CommRing R]
    (d : ℕ) (p : Source R 0) (hp : p.IsHomogeneous d) (i : Fin (0 * d + 1)) :
    (quotientHomogeneousBasis R 0 d).repr
      (quotientHomogeneousRepresentative R 0 d p hp) i = p.coeff (Finsupp.single 0 d) := by
  have hrep : quotientHomogeneousRepresentative R 0 d p hp =
      Submodule.equivMapOfInjective
        (Ideal.Quotient.mkₐ R (hankelIdeal R 0)).toLinearMap (zero_mk_injective R)
        (MvPolynomial.homogeneousSubmodule (Fin 1) R d) ⟨p, hp⟩ := rfl
  rw [hrep]
  rw [quotientHomogeneousBasis_eq]
  simp only [homogeneousCoordinates, dite_eq_left rfl, zeroBasis,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Module.Basis.repr_reindex_apply]
  rfl

/-- At `n = 1`, the vectors are the ordinary two-variable monomials. -/
theorem quotientHomogeneousBasis_one_apply (R : Type u) [CommRing R] (d : ℕ)
    (i : Fin (1 * d + 1)) :
    (quotientHomogeneousBasis R 1 d i : Source R 1 ⧸ hankelIdeal R 1) =
      Ideal.Quotient.mkₐ R (hankelIdeal R 1)
        (monomial (Finsupp.single 0 (d - i.val) + Finsupp.single 1 i.val) 1) := by
  rw [quotientHomogeneousBasis_apply_of_pos R 1 d (by decide)]
  have himage := (fiberNormalExponent_degree R 1 d (by decide)
    ((twoExponentIndex (1 * d)).symm i).1 ((twoExponentIndex (1 * d)).symm i).2).2
  rw [rncExponent_one, twoExponentIndex_symm] at himage
  simpa only [one_mul] using congrArg
    (fun e => Ideal.Quotient.mkₐ R (hankelIdeal R 1) (monomial e 1)) himage

/-- The degree-zero coordinate records a coefficient of the coefficient ring. -/
@[simp]
theorem quotientHomogeneousBasis_repr_C (R : Type u) [CommRing R] (n : ℕ) (r : R)
    (i : Fin (n * 0 + 1)) :
    (quotientHomogeneousBasis R n 0).repr
      (quotientHomogeneousRepresentative R n 0 (C r)
        (isHomogeneous_C (Fin (n + 1)) r)) i = r := by
  by_cases hn : n = 0
  · subst n
    rw [quotientHomogeneousBasis_repr_representative_zero]
    simp
  · rw [quotientHomogeneousBasis_repr_representative_of_pos R n 0
      (Nat.one_le_iff_ne_zero.mpr hn)]
    simp [rncMap_C]

/-- Reconstruction of a homogeneous representative from the coefficients of
its parametrization, for positive `n`. -/
theorem quotientHomogeneousRepresentative_eq_sum_of_pos (R : Type u) [CommRing R]
    (n d : ℕ) (hn : 1 ≤ n) (p : Source R n) (hp : p.IsHomogeneous d) :
    quotientHomogeneousRepresentative R n d p hp =
      ∑ i, (rncMap R n p).coeff
        (Finsupp.single 0 (n * d - i.val) + Finsupp.single 1 i.val) •
          quotientHomogeneousBasis R n d i := by
  symm
  simpa only [quotientHomogeneousBasis_repr_representative_of_pos R n d hn] using
    (quotientHomogeneousBasis R n d).sum_repr
      (quotientHomogeneousRepresentative R n d p hp)

/-- The finite coefficient-coordinate equivalence of the homogeneous quotient
submodule. Its inverse forms the corresponding linear combination of basis vectors. -/
def quotientHomogeneousCoordinates (R : Type u) [CommRing R] (n d : ℕ) :
    quotientHomogeneousSubmodule R n d ≃ₗ[R] (Fin (n * d + 1) → R) :=
  (quotientHomogeneousBasis R n d).equivFun

/-- Coordinates agree with the basis representation. -/
@[simp]
theorem quotientHomogeneousCoordinates_apply (R : Type u) [CommRing R] (n d : ℕ)
    (x : quotientHomogeneousSubmodule R n d) (i : Fin (n * d + 1)) :
    quotientHomogeneousCoordinates R n d x i = (quotientHomogeneousBasis R n d).repr x i :=
  rfl

/-- Inverse coordinates are an explicit finite sum of the monomial basis vectors. -/
theorem quotientHomogeneousCoordinates_symm_apply (R : Type u) [CommRing R] (n d : ℕ)
    (c : Fin (n * d + 1) → R) :
    (quotientHomogeneousCoordinates R n d).symm c =
      ∑ i, c i • quotientHomogeneousBasis R n d i :=
  (quotientHomogeneousBasis R n d).equivFun_symm_apply c

/-- Reconstruction from the coefficient coordinates in the homogeneous component. -/
theorem quotientHomogeneousBasis_sum_repr (R : Type u) [CommRing R] (n d : ℕ)
    (x : quotientHomogeneousSubmodule R n d) :
    ∑ i, (quotientHomogeneousBasis R n d).repr x i • quotientHomogeneousBasis R n d i = x :=
  (quotientHomogeneousBasis R n d).sum_repr x

/-- Equality in a homogeneous component can be checked in the finite coordinates. -/
theorem quotientHomogeneousCoordinates_ext (R : Type u) [CommRing R] (n d : ℕ)
    {x y : quotientHomogeneousSubmodule R n d}
    (h : ∀ i, quotientHomogeneousCoordinates R n d x i =
      quotientHomogeneousCoordinates R n d y i) : x = y :=
  (quotientHomogeneousCoordinates R n d).injective (funext h)

end

end ToricIdeals.RationalNormalCurve
