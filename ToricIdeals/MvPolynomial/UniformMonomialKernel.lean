/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.RingTheory.Ideal.Maps
public import ToricIdeals.MonoidAlgebra.Evaluation
import GroupRings.MonoidAlgebra.UniformBinomialKernel
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Uniform binomial kernels of monomial evaluation

For a finite variable type and a commutative target monoid, one finite set of
exponent pairs with the same monomial product generates the kernel of monomial
evaluation over every commutative coefficient ring. The finite set is independent
of the coefficient ring; neither cancellation in the target nor generation of
the target by the variable images is required.

The proof regards exponent vectors as a finitely generated commutative monoid,
uses the coefficient-independent finite family for monoid-algebra kernels, and
transports the kernel and its generators through the type-tag algebra
equivalences. Weighted evaluation identifies the transported map with polynomial
evaluation.

## References

* GroupRings' `MonoidAlgebra.uniform_fiber_span_of_fg` supplies the
  coefficient-independent finite family of same-fiber pairs.
* ToricIdeals' `MvPolynomial.aeval_single_eq_mapDomainAlgHom` identifies weighted
  monomial evaluation with the additive monoid-algebra map.
* Mathlib's `Finsupp.weight`, `AddMonoidAlgebra.toMultiplicativeAlgEquiv`,
  `MonoidAlgebra.toAdditiveAlgEquiv`, `Ideal.map_span`, and
  `Ideal.comap_map_of_bijective` provide the weight and transport APIs.
-/

@[expose] public section

noncomputable section

universe uR uι uM

namespace MvPolynomial

/-- A finite variable type admits one coefficient-independent finite family of
same-image exponent pairs spanning the kernel of monomial evaluation. -/
theorem uniform_monomial_kernel
    {ι : Type uι} {M : Type uM} [CommMonoid M] (g : ι → M) :
    Finite ι →
      ∃ E : Finset ((ι →₀ ℕ) × (ι →₀ ℕ)),
        (∀ de ∈ E,
          de.1.prod (fun i n => g i ^ n) =
            de.2.prod (fun i n => g i ^ n)) ∧
        ∀ (R : Type uR) [CommRing R],
          RingHom.ker
              (MvPolynomial.aeval (R := R)
                (fun i => MonoidAlgebra.single (g i) (1 : R))).toRingHom =
            Ideal.span
              ((fun de : (ι →₀ ℕ) × (ι →₀ ℕ) =>
                (MvPolynomial.monomial de.1 (1 : R) -
                  MvPolynomial.monomial de.2 (1 : R) : MvPolynomial ι R)) ''
                (↑E : Set ((ι →₀ ℕ) × (ι →₀ ℕ)))) := by
  classical
  intro hι
  let : Finite ι := hι
  let D := ι →₀ ℕ
  let N := Multiplicative D
  let w : D →+ Additive M :=
    Finsupp.weight (fun i => Additive.ofMul (g i))
  let f : N →* M := AddMonoidHom.toMultiplicativeLeft w
  have hf_apply (a : N) : f a = (w a.toAdd).toMul := rfl
  let : Module.Finite ℕ D := by
    dsimp only [D]
    infer_instance
  let : AddMonoid.FG D :=
    Module.Finite.iff_addMonoid_fg.mp inferInstance
  let : Monoid.FG N := by
    dsimp only [N]
    infer_instance
  have hfprod (a : N) :
      f a = a.toAdd.prod (fun i n => g i ^ n) := by
    change (Finsupp.weight (fun i => Additive.ofMul (g i)) a.toAdd).toMul = _
    simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
      toMul_sum, toMul_nsmul, toMul_ofMul]
  obtain ⟨F, hFfib, hF⟩ :
      ∃ F : Finset (N × N),
        (∀ ab ∈ F, f ab.1 = f ab.2) ∧
        ∀ (R : Type uR) [Ring R],
          RingHom.ker (MonoidAlgebra.mapDomainRingHom R f) =
            Ideal.span
              ((fun ab : N × N =>
                (MonoidAlgebra.single ab.1 (1 : R) -
                  MonoidAlgebra.single ab.2 (1 : R) : MonoidAlgebra R N)) ''
                (↑F : Set (N × N))) :=
    MonoidAlgebra.uniform_fiber_span_of_fg f
  let q : N × N → D × D := fun ab => (ab.1.toAdd, ab.2.toAdd)
  let E : Finset (D × D) := F.image q
  refine ⟨E, ?_, ?_⟩
  · intro de hde
    change de ∈ F.image q at hde
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hde
    change ab.1.toAdd.prod (fun i n => g i ^ n) =
      ab.2.toAdd.prod (fun i n => g i ^ n)
    exact (hfprod ab.1).symm.trans ((hFfib ab hab).trans (hfprod ab.2))
  · intro R _
    let e : MvPolynomial ι R ≃ₐ[R] MonoidAlgebra R N :=
      AddMonoidAlgebra.toMultiplicativeAlgEquiv R R D
    let er : MvPolynomial ι R →+* MonoidAlgebra R N :=
      e.toRingEquiv.toRingHom
    let t : MonoidAlgebra R M ≃ₐ[R] AddMonoidAlgebra R (Additive M) :=
      MonoidAlgebra.toAdditiveAlgEquiv R R M
    let Φ : MvPolynomial ι R →ₐ[R] MonoidAlgebra R M :=
      MvPolynomial.aeval (fun i => MonoidAlgebra.single (g i) (1 : R))
    let ψ : MonoidAlgebra R N →ₐ[R] MonoidAlgebra R M :=
      MonoidAlgebra.mapDomainAlgHom R R f
    have he_single (d : D) (r : R) :
        e (AddMonoidAlgebra.single d r) =
          MonoidAlgebra.single (Multiplicative.ofAdd d) r :=
      AddMonoidAlgebra.toMultiplicativeAlgEquiv_single
        (R := R) (A := R) (M := D) d r
    have ht_single (m : M) (r : R) :
        t (MonoidAlgebra.single m r) =
          AddMonoidAlgebra.single (Additive.ofMul m) r :=
      MonoidAlgebra.toAdditiveAlgEquiv_single
        (R := R) (A := R) (M := M) m r
    have htΦ : t.toAlgHom.comp Φ =
        AddMonoidAlgebra.mapDomainAlgHom R R w := by
      calc
        t.toAlgHom.comp Φ = MvPolynomial.aeval
            (fun i => AddMonoidAlgebra.single (Additive.ofMul (g i)) (1 : R)) := by
          dsimp only [Φ]
          rw [MvPolynomial.comp_aeval]
          exact congrArg (MvPolynomial.aeval (R := R))
            (funext fun i => ht_single (g i) (1 : R))
        _ = AddMonoidAlgebra.mapDomainAlgHom R R w :=
          MvPolynomial.aeval_single_eq_mapDomainAlgHom
            (fun i => Additive.ofMul (g i))
    have htψ : t.toAlgHom.comp (ψ.comp e.toAlgHom) =
        AddMonoidAlgebra.mapDomainAlgHom R R w := by
      apply MvPolynomial.algHom_ext
      intro i
      change t (ψ (e (MvPolynomial.X i))) =
        AddMonoidAlgebra.mapDomainAlgHom R R w (MvPolynomial.X i)
      simp only [MvPolynomial.X, ← MvPolynomial.single_eq_monomial]
      simp only [he_single, ψ,
        MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
        ht_single,
        AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
      exact congrArg
        (fun m : M => AddMonoidAlgebra.single (Additive.ofMul m) (1 : R))
        (hf_apply (Multiplicative.ofAdd (Finsupp.single i 1)))
    have hbridge (p : MvPolynomial ι R) : ψ (e p) = Φ p := by
      apply t.injective
      exact DFunLike.congr_fun (htψ.trans htΦ.symm) p
    have hker : RingHom.ker Φ.toRingHom =
        (RingHom.ker (MonoidAlgebra.mapDomainRingHom R f)).comap er := by
      apply Ideal.ext
      intro p
      rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      change Φ p = 0 ↔ ψ (e p) = 0
      rw [hbridge p]
    let P : D × D → MvPolynomial ι R := fun de =>
      MvPolynomial.monomial de.1 (1 : R) -
        MvPolynomial.monomial de.2 (1 : R)
    let B : N × N → MonoidAlgebra R N := fun ab =>
      MonoidAlgebra.single ab.1 (1 : R) -
        MonoidAlgebra.single ab.2 (1 : R)
    have hgen (ab : N × N) : er (P (q ab)) = B ab := by
      change e (P (q ab)) = B ab
      simp only [P, B, q, map_sub, ← MvPolynomial.single_eq_monomial,
        he_single, ofAdd_toAdd]
    have hset :
        er '' (P '' (↑E : Set (D × D))) = B '' (↑F : Set (N × N)) := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨_, ⟨de, hde, rfl⟩, rfl⟩
        change de ∈ F.image q at hde
        obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hde
        exact ⟨ab, hab, (hgen ab).symm⟩
      · rintro ⟨ab, hab, rfl⟩
        refine ⟨P (q ab), ?_, hgen ab⟩
        refine ⟨q ab, ?_, rfl⟩
        change q ab ∈ F.image q
        exact Finset.mem_image.mpr ⟨ab, hab, rfl⟩
    have hmap :
        (Ideal.span (P '' (↑E : Set (D × D)))).map er =
          Ideal.span (B '' (↑F : Set (N × N))) := by
      rw [Ideal.map_span, hset]
    change RingHom.ker Φ.toRingHom = Ideal.span (P '' (↑E : Set (D × D)))
    calc
      RingHom.ker Φ.toRingHom =
          (RingHom.ker (MonoidAlgebra.mapDomainRingHom R f)).comap er := hker
      _ = (Ideal.span (B '' (↑F : Set (N × N)))).comap er := by rw [hF R]
      _ = ((Ideal.span (P '' (↑E : Set (D × D)))).map er).comap er := by
        rw [hmap]
      _ = Ideal.span (P '' (↑E : Set (D × D))) :=
        Ideal.comap_map_of_bijective er e.bijective

end MvPolynomial
