/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import ToricIdeals.RationalNormalCurve.HomogeneousBasis

/-!
# Scalar consequences of homogeneous-basis coefficient change

Reduction from `ZMod 4` to `ZMod 2` erases a nonzero coefficient-`2`
perturbation of any indexed homogeneous vector, including the components
with `n = 0` or `d = 0`. The surviving vector is transported by the
coefficient-change theorem for the indexed basis.

At `n = 0`, scalar multiples of the cubic vector map to scalar multiples
of the class of `X 0 ^ 3` in the full quotient, not to constants under
the parametrization. At `d = 0`, the transported scalar multiple is the
image of its coefficient under the quotient's canonical algebra map.
The coefficient rings in these two examples have independent universes.
All declarations are private.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.HomogeneousBasis`,
  for coefficient change of the indexed basis and its representative and
  coordinate laws.
* Mathlib contributors, quotient ring homomorphisms, canonical algebra
  actions, basis representations and modular coefficient reduction.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

universe u v

/-- Modular reduction forgets a nonzero nilpotent perturbation of every
indexed vector, with no restriction on either homogeneous parameter. -/
private theorem reduction_erases_basis_perturbation
    (n d : ℕ) (i j : Fin (n * d + 1)) :
    Ideal.quotientMap (hankelIdeal (ZMod 2) n)
      (MvPolynomial.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) n).le)
      ((2 : ZMod 4) •
        (quotientHomogeneousBasis (ZMod 4) n d i :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) +
        (quotientHomogeneousBasis (ZMod 4) n d j :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)) =
      (quotientHomogeneousBasis (ZMod 2) n d j :
        Source (ZMod 2) n ⧸ hankelIdeal (ZMod 2) n) ∧
    (2 : ZMod 4) •
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) +
      (quotientHomogeneousBasis (ZMod 4) n d j :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) ≠
      (quotientHomogeneousBasis (ZMod 4) n d j :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) := by
  constructor
  · have hdiv : 2 ∣ 4 := ⟨2, rfl⟩
    change Ideal.quotientMap (hankelIdeal (ZMod 2) n)
      (MvPolynomial.map (ZMod.castHom hdiv (ZMod 2)))
      ((Ideal.map_le_iff_le_comap).mp
        (map_hankelIdeal (ZMod.castHom hdiv (ZMod 2)) n).le)
      ((2 : ZMod 4) •
        (quotientHomogeneousBasis (ZMod 4) n d i :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) +
        (quotientHomogeneousBasis (ZMod 4) n d j :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)) =
      (quotientHomogeneousBasis (ZMod 2) n d j :
        Source (ZMod 2) n ⧸ hankelIdeal (ZMod 2) n)
    have htwo : ZMod.castHom hdiv (ZMod 2) (2 : ZMod 4) = 0 :=
      (map_natCast (ZMod.castHom hdiv (ZMod 2)) 2).trans
        (by decide : (2 : ZMod 2) = 0)
    rw [map_add, Algebra.smul_def (R := ZMod 4)
      (A := Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) (2 : ZMod 4)
      (quotientHomogeneousBasis (ZMod 4) n d i :
        Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n), map_mul,
      quotientMap_quotientHomogeneousBasis (ZMod 4) (ZMod 2)
        (ZMod.castHom hdiv (ZMod 2)) n d i,
      quotientMap_quotientHomogeneousBasis (ZMod 4) (ZMod 2)
        (ZMod.castHom hdiv (ZMod 2)) n d j,
      Ideal.quotientMap_algebraMap]
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
      htwo, map_zero, zero_mul, zero_add]
  · intro h
    have hz : (2 : ZMod 4) •
        (quotientHomogeneousBasis (ZMod 4) n d i :
          Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n) = 0 :=
      add_right_cancel (h.trans (zero_add _).symm)
    have hs : (2 : ZMod 4) • quotientHomogeneousBasis (ZMod 4) n d i = 0 :=
      Subtype.ext hz
    have hc := congrArg (fun x : quotientHomogeneousSubmodule (ZMod 4) n d =>
      (quotientHomogeneousBasis (ZMod 4) n d).repr x i) hs
    exact (by decide : (2 : ZMod 4) ≠ 0) (by simpa using hc)

/-- A scaled cubic vector at `n = 0` retains the cubic power of the
surviving variable after coefficient change in the full quotient. -/
private theorem quotientMap_scaled_one_variable_cube
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) :
    Ideal.quotientMap (hankelIdeal S 0) (MvPolynomial.map φ)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ 0).le)
      (r • (quotientHomogeneousBasis R 0 3 0 : Source R 0 ⧸ hankelIdeal R 0)) =
      φ r • Ideal.Quotient.mkₐ S (hankelIdeal S 0) (X 0 ^ 3) := by
  have hcoeff : Ideal.quotientMap (hankelIdeal S 0) (MvPolynomial.map φ)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ 0).le)
      (algebraMap R (Source R 0 ⧸ hankelIdeal R 0) r) =
      algebraMap S (Source S 0 ⧸ hankelIdeal S 0) (φ r) := by
    rw [Ideal.quotientMap_algebraMap]
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C] using
      (Ideal.Quotient.mk_algebraMap (R₁ := S) (hankelIdeal S 0) (φ r))
  calc
    _ = φ r • Ideal.quotientMap (hankelIdeal S 0) (MvPolynomial.map φ)
        ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ 0).le)
        (quotientHomogeneousBasis R 0 3 0 : Source R 0 ⧸ hankelIdeal R 0) := by
      rw [Algebra.smul_def (R := R) (A := Source R 0 ⧸ hankelIdeal R 0) r
        (quotientHomogeneousBasis R 0 3 0 : Source R 0 ⧸ hankelIdeal R 0),
        Algebra.smul_def (R := S) (A := Source S 0 ⧸ hankelIdeal S 0) (φ r)
          (Ideal.quotientMap (hankelIdeal S 0) (MvPolynomial.map φ)
            ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ 0).le)
            (quotientHomogeneousBasis R 0 3 0 : Source R 0 ⧸ hankelIdeal R 0)),
        map_mul, hcoeff]
    _ = _ := by
      simpa only [quotientHomogeneousBasis_zero_apply] using
        congrArg (fun x : Source S 0 ⧸ hankelIdeal S 0 => φ r • x)
          (quotientMap_quotientHomogeneousBasis R S φ 0 3 0)

/-- On the degree-zero component, scalar transport agrees with the
canonical coefficient embedding into the full target quotient. -/
private theorem quotientMap_degree_zero_coefficient
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) (r : R) (i : Fin (n * 0 + 1)) :
    Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)
      (r • (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n)) =
      algebraMap S (Source S n ⧸ hankelIdeal S n) (φ r) := by
  have hC : φ r • quotientHomogeneousBasis S n 0 i =
      quotientHomogeneousRepresentative S n 0 (C (φ r))
        (isHomogeneous_C (Fin (n + 1)) (φ r)) := by
    apply (quotientHomogeneousBasis S n 0).repr.injective
    ext j
    have hij : i = j := by omega
    subst j
    simp
  have hcoeff : Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
      ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)
      (algebraMap R (Source R n ⧸ hankelIdeal R n) r) =
      algebraMap S (Source S n ⧸ hankelIdeal S n) (φ r) := by
    rw [Ideal.quotientMap_algebraMap]
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C] using
      (Ideal.Quotient.mk_algebraMap (R₁ := S) (hankelIdeal S n) (φ r))
  calc
    _ = φ r • Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
        ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)
        (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n) := by
      rw [Algebra.smul_def (R := R) (A := Source R n ⧸ hankelIdeal R n) r
        (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n),
        Algebra.smul_def (R := S) (A := Source S n ⧸ hankelIdeal S n) (φ r)
          (Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map φ)
            ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal φ n).le)
            (quotientHomogeneousBasis R n 0 i : Source R n ⧸ hankelIdeal R n)),
        map_mul, hcoeff]
    _ = φ r • (quotientHomogeneousBasis S n 0 i :
        Source S n ⧸ hankelIdeal S n) :=
      congrArg (fun x : Source S n ⧸ hankelIdeal S n => φ r • x)
        (quotientMap_quotientHomogeneousBasis R S φ n 0 i)
    _ = (quotientHomogeneousRepresentative S n 0 (C (φ r))
        (isHomogeneous_C (Fin (n + 1)) (φ r)) :
          Source S n ⧸ hankelIdeal S n) :=
      congrArg (fun x : quotientHomogeneousSubmodule S n 0 =>
        (x : Source S n ⧸ hankelIdeal S n)) hC
    _ = _ := by
      simpa only [quotientHomogeneousRepresentative_coe,
        Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq] using
        (Ideal.Quotient.mk_algebraMap (R₁ := S) (hankelIdeal S n) (φ r))

end

end ToricIdeals.RationalNormalCurve
