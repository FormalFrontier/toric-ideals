/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import ToricIdeals.RationalNormalCurve.Augmentation
public import MultivariatePolynomials.Cotangent
import MultivariatePolynomials.EvaluationIdeal

/-!
# Cotangent coordinates at the vertex of the full Hankel quotient

For the coefficient augmentation of the full Hankel quotient, the classes of
all variables form a basis of its kernel modulo its square over the coefficient
ring. The coordinates are the raw linear coefficients of any polynomial
representative with zero constant coefficient.

The carrier is Mathlib's `Ideal.Cotangent`. Its coefficient action is inherited
along `R → Source R n → Source R n ⧸ hankelIdeal R n`: on representatives,
`r • [q] = [mk (C r) * q]`. This is not a basis over the whole quotient ring.
The construction includes every commutative ring and every `n`, including zero:
the degree-zero quotient retains `X₀`, not the parametrization value `1`.
Over a zero ring the indexed basis still exists, without a numerical rank claim.

## References

* Mathlib contributors, `Mathlib.RingTheory.Ideal.Cotangent`, for the conormal
  module of an ideal, its inherited scalar actions and quotient transport.
* Formal Frontier Agents, `MultivariatePolynomials.Cotangent`, for the
  prescribed-variable basis and linear-coefficient coordinates of the polynomial
  augmentation cotangent module.
* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve.Augmentation`, for
  the coefficient augmentation and its variable-span kernel.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- The preimage of the quotient augmentation ideal is the polynomial variable
ideal, for every coefficient ring and every degree. -/
theorem quotientAugmentation_comap_mk (R : Type u) [CommRing R] (n : ℕ) :
    (RingHom.ker (quotientAugmentation R n).toRingHom).comap
        (Ideal.Quotient.mkₐ R (hankelIdeal R n)) =
      MvPolynomial.idealOfVars (Fin (n + 1)) R := by
  ext p
  change quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) p) = 0 ↔
    p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [quotientAugmentation_mk]
  symm
  simpa only [MvPolynomial.idealOfVars, Pi.zero_apply, map_zero, sub_zero,
    MvPolynomial.eval_zero] using
    (MvPolynomial.mem_ideal_span_X_sub_C_iff (0 : Fin (n + 1) → R) p)

/-- The quotient map induces a bijection of augmentation cotangent modules,
with their canonical coefficient-ring actions. -/
theorem quotientAugmentation_mapCotangent_bijective
    (R : Type u) [CommRing R] (n : ℕ) :
    Function.Bijective
      (Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin (n + 1)) R)
        (RingHom.ker (quotientAugmentation R n).toRingHom)
        (Ideal.Quotient.mkₐ R (hankelIdeal R n))
        (quotientAugmentation_comap_mk R n).ge) := by
  let m : Ideal (Source R n) := MvPolynomial.idealOfVars (Fin (n + 1)) R
  let I : Ideal (Source R n ⧸ hankelIdeal R n) :=
    RingHom.ker (quotientAugmentation R n).toRingHom
  let f : Source R n →ₐ[R] Source R n ⧸ hankelIdeal R n :=
    Ideal.Quotient.mkₐ R (hankelIdeal R n)
  have hcomap : I.comap f = m := quotientAugmentation_comap_mk R n
  let F := Ideal.mapCotangent m I f hcomap.ge
  change Function.Bijective F
  have hmap : m.map f = I := by
    rw [← hcomap]
    exact Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective I
  have hker : RingHom.ker f = hankelIdeal R n := by
    change RingHom.ker (Ideal.Quotient.mk (hankelIdeal R n)) = hankelIdeal R n
    exact Ideal.mk_ker
  have hsq : RingHom.ker f ≤ m ^ 2 := by
    rw [hker]
    exact hankelIdeal_le_idealOfVars_sq R n
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := m.toCotangent_surjective x
    obtain ⟨b, rfl⟩ := m.toCotangent_surjective y
    change I.toCotangent ⟨f a, hcomap.ge a.property⟩ =
      I.toCotangent ⟨f b, hcomap.ge b.property⟩ at hxy
    have hab : f ((a : Source R n) - (b : Source R n)) ∈ I ^ 2 := by
      simpa only [map_sub] using (I.toCotangent_eq.mp hxy)
    rw [← hmap, ← Ideal.map_pow, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective' f Ideal.Quotient.mk_surjective,
      sup_eq_left.mpr hsq] at hab
    exact m.toCotangent_eq.mpr hab
  · intro y
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective y
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a : Source R n ⧸ hankelIdeal R n)
    have hp' : p ∈ m := by
      rw [← hcomap]
      change f p ∈ I
      rw [show f p = a from hp]
      exact a.property
    refine ⟨m.toCotangent ⟨p, hp'⟩, ?_⟩
    change I.toCotangent ⟨f p, hcomap.ge hp'⟩ = I.toCotangent a
    exact congrArg I.toCotangent (Subtype.ext hp)

/-- The quotient-variable classes form a coefficient-ring basis of the
augmentation kernel modulo its square in the full Hankel quotient.
Scalars use the canonical coefficient algebra action, for every commutative
ring and every degree, including degree zero. -/
noncomputable def quotientAugmentationCotangentBasis (R : Type u) [CommRing R] (n : ℕ) :
    Module.Basis (Fin (n + 1)) R
      (RingHom.ker (quotientAugmentation R n).toRingHom).Cotangent := by
  exact (MvPolynomial.idealOfVarsCotangentBasis (Fin (n + 1)) R).map
    (LinearEquiv.ofBijective
      (Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin (n + 1)) R)
        (RingHom.ker (quotientAugmentation R n).toRingHom)
        (Ideal.Quotient.mkₐ R (hankelIdeal R n))
        (quotientAugmentation_comap_mk R n).ge)
      (quotientAugmentation_mapCotangent_bijective R n))

/-- The `i`th basis vector is the cotangent class of the quotient class of `X i`.
The membership witness uses the existing variable-span description of the kernel. -/
@[simp] theorem quotientAugmentationCotangentBasis_apply
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    quotientAugmentationCotangentBasis R n i =
      (RingHom.ker (quotientAugmentation R n).toRingHom).toCotangent
        ⟨Ideal.Quotient.mkₐ R (hankelIdeal R n) (MvPolynomial.X i), by
          rw [ker_quotientAugmentation]
          exact Ideal.subset_span (Set.mem_range_self i)⟩ := by
  simp only [quotientAugmentationCotangentBasis, Module.Basis.map_apply,
    MvPolynomial.idealOfVarsCotangentBasis_apply, LinearEquiv.ofBijective_apply,
    Ideal.mapCotangent_toCotangent]

/-- Every polynomial representative with zero constant coefficient has cotangent
coordinates given by its raw linear coefficients. Terms of degree at least two
do not contribute, independently of the representative modulo the Hankel ideal. -/
@[simp] theorem quotientAugmentationCotangentBasis_repr_mk
    (R : Type u) [CommRing R] (n : ℕ) (p : Source R n)
    (hp : MvPolynomial.constantCoeff p = 0) (i : Fin (n + 1)) :
    (quotientAugmentationCotangentBasis R n).repr
      ((RingHom.ker (quotientAugmentation R n).toRingHom).toCotangent
        ⟨Ideal.Quotient.mkₐ R (hankelIdeal R n) p, by
          apply RingHom.mem_ker.mpr
          simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
            Ideal.Quotient.mkₐ_eq_mk, quotientAugmentation_mk] using hp⟩) i =
      p.coeff (Finsupp.single i 1) := by
  have hp' : p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R := by
    rw [← quotientAugmentation_comap_mk R n]
    change quotientAugmentation R n (Ideal.Quotient.mk (hankelIdeal R n) p) = 0
    simpa only [quotientAugmentation_mk] using hp
  let e := LinearEquiv.ofBijective
    (Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin (n + 1)) R)
      (RingHom.ker (quotientAugmentation R n).toRingHom)
      (Ideal.Quotient.mkₐ R (hankelIdeal R n))
      (quotientAugmentation_comap_mk R n).ge)
    (quotientAugmentation_mapCotangent_bijective R n)
  change ((MvPolynomial.idealOfVarsCotangentBasis (Fin (n + 1)) R).map e).repr
    (e ((MvPolynomial.idealOfVars (Fin (n + 1)) R).toCotangent ⟨p, hp'⟩)) i = _
  rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact MvPolynomial.idealOfVarsCotangentBasis_repr_toCotangent
    (Fin (n + 1)) R ⟨p, hp'⟩ i

end ToricIdeals.RationalNormalCurve
