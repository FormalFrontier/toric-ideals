/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Finsupp.Fintype
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
public import ToricIdeals.RationalNormalCurve

/-!
# Relative module finiteness of the rational normal curve parametrization

The target of `rncMap R n` is finite as a module over `Source R n` via
that map exactly when the degree is positive or the coefficient semiring
is subsingleton. The scalar action is `s • t = rncMap R n s * t`, induced
by Mathlib's `RingHom.toAlgebra` and `Algebra.toModule`.

Here `Module.Finite` means finitely generated over the source, with the
same meaning for rings and semirings. This is not finiteness over the
coefficient semiring `R`: the two-variable target is not a finite
`R`-module when `R` is nontrivial.

The statement includes degree zero, where the sole source variable maps
to `1`. It concerns the raw parametrization. Over commutative rings,
the full degree-zero Hankel quotient instead retains its sole variable
and is the one-variable polynomial ring `R[X]`.

## References

* Mathlib contributors, `Mathlib.RingTheory.Finiteness.Defs`, for
  `Module.Finite`, the finite-generation property for modules.
* Mathlib contributors, `Mathlib.Algebra.Algebra.Defs`, for
  `RingHom.toAlgebra` and `Algebra.toModule`, the induced scalar action.
-/

@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- In positive degree, the residual monomials with both exponents below `n`
span the target over the full source through the parametrization. -/
private theorem rncMap_moduleFinite_of_ne_zero (R : Type u) [CommSemiring R]
    (n : ℕ) (hn : n ≠ 0) :
    @Module.Finite (Source R n) (Target R) _ _
      (@Algebra.toModule (Source R n) (Target R) _ _ (rncMap R n).toAlgebra) := by
  classical
  let : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
  let g : Fin n × Fin n → Target R := fun ab =>
    MvPolynomial.X (0 : Fin 2) ^ ab.1.val *
      MvPolynomial.X (1 : Fin 2) ^ ab.2.val
  let P : Submodule (Source R n) (Target R) :=
    Submodule.span (Source R n) (Set.range g)
  have hzero :
      rncMap R n (MvPolynomial.X (0 : Fin (n + 1))) =
        MvPolynomial.X (0 : Fin 2) ^ n := by
    rw [rncMap_X]
    simpa [coordinateExponent] using
      (MvPolynomial.X_pow_eq_monomial (R := R) (n := (0 : Fin 2)) (e := n)).symm
  have hlast :
      rncMap R n (MvPolynomial.X (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) =
        MvPolynomial.X (1 : Fin 2) ^ n := by
    rw [rncMap_X]
    simpa [coordinateExponent] using
      (MvPolynomial.X_pow_eq_monomial (R := R) (n := (1 : Fin 2)) (e := n)).symm
  have hpow (x : Target R) (k : ℕ) :
      x ^ k = (x ^ n) ^ (k / n) * x ^ (k % n) := by
    calc
      x ^ k = x ^ (k % n + n * (k / n)) := by rw [Nat.mod_add_div]
      _ = (x ^ n) ^ (k / n) * x ^ (k % n) := by
        rw [pow_add, pow_mul, mul_comm]
  have hmon (d : Fin 2 →₀ ℕ) (r : R) : MvPolynomial.monomial d r ∈ P := by
    let a : Fin n := ⟨d 0 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    let b : Fin n := ⟨d 1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    let s : Source R n :=
      MvPolynomial.C r * MvPolynomial.X (0 : Fin (n + 1)) ^ (d 0 / n) *
        MvPolynomial.X (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ^ (d 1 / n)
    have hg : g (a, b) ∈ P :=
      Submodule.mem_span_of_mem ⟨(a, b), rfl⟩
    have hd :
        d = Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single (1 : Fin 2) (d 1) := by
      ext i
      fin_cases i <;> simp
    have hmonomial :
        MvPolynomial.monomial d r =
          MvPolynomial.C r * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
            MvPolynomial.X (1 : Fin 2) ^ (d 1) := by
      calc
        MvPolynomial.monomial d r =
            MvPolynomial.monomial
              (Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single (1 : Fin 2) (d 1)) r :=
          congrArg (fun e => MvPolynomial.monomial e r) hd
        _ = MvPolynomial.C r * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
            MvPolynomial.X (1 : Fin 2) ^ (d 1) := by
          rw [MvPolynomial.monomial_add_single,
            ← MvPolynomial.C_mul_X_pow_eq_monomial]
    have hfactor : MvPolynomial.monomial d r = s • g (a, b) := by
      rw [(rncMap R n).smul_toAlgebra]
      change MvPolynomial.monomial d r =
        rncMap R n
          (MvPolynomial.C r * MvPolynomial.X (0 : Fin (n + 1)) ^ (d 0 / n) *
            MvPolynomial.X (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ^ (d 1 / n)) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 % n) *
            MvPolynomial.X (1 : Fin 2) ^ (d 1 % n))
      rw [hmonomial, map_mul, map_mul, map_pow, map_pow, rncMap_C, hzero, hlast,
        hpow (MvPolynomial.X (0 : Fin 2)) (d 0),
        hpow (MvPolynomial.X (1 : Fin 2)) (d 1)]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [hfactor]
    exact P.smul_mem s hg
  apply Module.Finite.of_fg_top
  apply Submodule.fg_def.mpr
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  refine le_antisymm le_top ?_
  intro p _
  change p ∈ P
  exact MvPolynomial.induction_on' p hmon (fun _ _ hp hq => P.add_mem hp hq)

private theorem not_rncMap_zero_moduleFinite (R : Type u)
    [CommSemiring R] [Nontrivial R] :
    ¬ @Module.Finite (Source R 0) (Target R) _ _
      (@Algebra.toModule (Source R 0) (Target R) _ _
        (rncMap R 0).toAlgebra) := by
  let e : Source R 0 →+* R :=
    MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 1)
  have hfactor : rncMap R 0 = MvPolynomial.C.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e]
    · intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      simp [e, coordinateExponent]
  let : Algebra (Source R 0) R := e.toAlgebra
  let : Algebra (Source R 0) (Target R) := (rncMap R 0).toAlgebra
  let : Module (Source R 0) R :=
    @Algebra.toModule (Source R 0) R _ _ e.toAlgebra
  let : Module (Source R 0) (Target R) :=
    @Algebra.toModule (Source R 0) (Target R) _ _
      (rncMap R 0).toAlgebra
  let : IsScalarTower (Source R 0) R (Target R) :=
    IsScalarTower.of_algebraMap_eq' hfactor
  intro h
  let : Module.Finite (Source R 0) (Target R) := h
  let : Module.Finite R (Target R) :=
    Module.Finite.of_restrictScalars_finite (Source R 0) R (Target R)
  have hf : Finite (Fin 2 →₀ ℕ) :=
    Module.Finite.finite_basis (MvPolynomial.basisMonomials (Fin 2) R)
  exact Infinite.not_finite hf

/-- The target is a finite module over the source via `rncMap` exactly when
the degree is positive or the coefficient semiring is subsingleton. -/
theorem rncMap_moduleFinite_iff (R : Type u) [CommSemiring R] (n : ℕ) :
    @Module.Finite (Source R n) (Target R) _ _
        (@Algebra.toModule (Source R n) (Target R) _ _ (rncMap R n).toAlgebra) ↔
      n ≠ 0 ∨ Subsingleton R := by
  constructor
  · intro h
    by_cases hn : n = 0
    · right
      subst n
      rcases subsingleton_or_nontrivial R with hR | hR
      · exact hR
      · let : Nontrivial R := hR
        exact (not_rncMap_zero_moduleFinite R h).elim
    · exact Or.inl hn
  · rintro (hn | hR)
    · exact rncMap_moduleFinite_of_ne_zero R n hn
    · let : Subsingleton R := hR
      infer_instance

/-- The raw parametrization is of finite type over its source in every degree. -/
theorem rncMap_finiteType (R : Type u) [CommSemiring R] (n : ℕ) :
    @Algebra.FiniteType (Source R n) (Target R) _ _ (rncMap R n).toAlgebra := by
  let : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
  let : IsScalarTower R (Source R n) (Target R) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      exact (rncMap_C R n r).symm)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (Source R n) (Target R)

end ToricIdeals.RationalNormalCurve
