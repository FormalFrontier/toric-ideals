/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
public import ToricIdeals.RationalNormalCurve

/-!
# Scalar base change of rational-normal-curve Hankel quotients

For a commutative `R`-algebra `S`, scalar base change of the full quotient
`Source R n ⧸ hankelIdeal R n` is described by an `S`-algebra equivalence
with `Source S n ⧸ hankelIdeal S n`. The representative formula sends
`s ⊗ₜ [p]` to `[s • MvPolynomial.map (algebraMap R S) p]`.

The statements concern every degree and arbitrary commutative rings, including
zero rings, product rings and rings with nilpotents. At degrees zero and one,
they concern the full one-variable and two-variable polynomial quotients,
respectively, not a parametrization image. No flatness or injectivity is assumed.
A ring homomorphism specializes the statements through its canonical
`RingHom.toAlgebra` structure.

## References

Credit goes to the Mathlib contributors for the tensor-quotient equivalence in
`Mathlib.RingTheory.TensorProduct.Quotient`, the polynomial tensor equivalence in
`Mathlib.RingTheory.TensorProduct.MvPolynomial`, and ideal transport through
quotient equivalences. The Hankel presentation and coefficient transport
`map_hankelIdeal` come from the existing rational-normal-curve formalization by
Formal Frontier Agents in `ToricIdeals.RationalNormalCurve`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace ToricIdeals.RationalNormalCurve

/-- Scalar base change of the full quotient by the Hankel minors, as an
`S`-algebra equivalence, for every degree and commutative coefficient algebra. -/
noncomputable def quotientBaseChangeAlgEquiv
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    S ⊗[R] (Source R n ⧸ hankelIdeal R n) ≃ₐ[S]
      (Source S n ⧸ hankelIdeal S n) := by
  let ι : Source R n →ₐ[R] S ⊗[R] Source R n :=
    Algebra.TensorProduct.includeRight
  let e : S ⊗[R] Source R n ≃ₐ[S] Source S n :=
    MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R S
  have hcomp : (e : S ⊗[R] Source R n →+* Source S n).comp ι.toRingHom =
      MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R S
      (1 ⊗ₜ[R] p) = MvPolynomial.map (algebraMap R S) p
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul
      (σ := Fin (n + 1)) R S (1 : S) p).trans (one_smul S _)
  have h : ((hankelIdeal R n).map ι.toRingHom).map
      (e : S ⊗[R] Source R n →+* Source S n) = hankelIdeal S n := by
    rw [Ideal.map_map, hcomp, map_hankelIdeal]
  exact (Algebra.TensorProduct.tensorQuotientEquiv
    (R := R) S (Source R n) S (hankelIdeal R n)).trans
      (Ideal.quotientEquivAlg (R₁ := S)
        ((hankelIdeal R n).map ι.toRingHom) (hankelIdeal S n) e h.symm)

/-- On a pure tensor of a quotient representative, scalar base change maps the
polynomial's coefficients along `algebraMap R S` and multiplies by `s`. -/
@[simp] theorem quotientBaseChangeAlgEquiv_tmul_mk
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (s : S) (p : Source R n) :
    quotientBaseChangeAlgEquiv R S n
        (s ⊗ₜ[R] (Ideal.Quotient.mk (hankelIdeal R n) p)) =
      Ideal.Quotient.mk (hankelIdeal S n)
        (s • MvPolynomial.map (algebraMap R S) p) := by
  -- The quotient equivalences act canonically on representatives.
  change Ideal.Quotient.mk (hankelIdeal S n)
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R S
      (s ⊗ₜ[R] p)) = _
  exact congrArg (Ideal.Quotient.mk (hankelIdeal S n))
    (MvPolynomial.algebraTensorAlgEquiv_tmul (σ := Fin (n + 1)) R S s p)

end ToricIdeals.RationalNormalCurve
