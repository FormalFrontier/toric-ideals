/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.MvPolynomial.Eval
import ToricIdeals.MvPolynomial.MonomialCosetSupport

/-!
# Consumers and boundary controls for coset support

The first consumer composes the existing group-closure and submonoid-sup APIs to
recover difference witnesses, with no new group-completion carrier. The bottom
monoid gives constant support. The two-ray example shows why the conclusion must
be membership in the generated group, rather than in the exponent monoid.

The library theorem is uniform in `S`, including the even-power monoid whose
coarse quotient grading has torsion. No ordering or torsion-free hypothesis is
available in these consumers.

## References

* Eric Wieser's `Mathlib.Algebra.Group.Subgroup.Pointwise` supplies the
  group-closure-to-submonoid construction using pointwise negation
  (`AddSubgroup.closure_toAddSubmonoid`).
* `Mathlib.Algebra.Group.Submonoid.Membership`, by Johannes Hölzl, Kenny Lau,
  Johan Commelin, Mario Carneiro, Kevin Buzzard, Amelia Livingston, and
  Yury Kudryashov, supplies the submonoid sup-membership witnesses
  (`AddSubmonoid.mem_sup`).
* `Mathlib.Algebra.Algebra.Subalgebra.Lattice`, by Kenny Lau and Yury Kudryashov,
  supplies the universal property used for the monomial generators and equalizer.
* `Mathlib.Algebra.MvPolynomial.Eval`, by Johannes Hölzl, Johan Commelin, and
  Mario Carneiro, supplies the evaluations distinguishing the two-ray adjoin from
  the polynomial algebra.
-/

namespace ToricIdealsTest

open MvPolynomial
open scoped Pointwise

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- An actual consumer of the support bridge: every supported exponent has a
difference witness in the original exponent monoid. No domain hypothesis is used. -/
theorem regular_denominator_difference_witnesses
    (S : AddSubmonoid (σ →₀ ℕ)) {b f : MvPolynomial σ R}
    (hb : b ∈ Algebra.adjoin R
      (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R)))
    (hbreg : IsLeftRegular b)
    (hbf : b * f ∈ Algebra.adjoin R
      (Set.range fun s : S => monomial (s : σ →₀ ℕ) (1 : R))) :
    ∀ n ∈ f.support, ∃ s ∈ S, ∃ t ∈ S,
      (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)) n =
        (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)) s -
          (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)) t := by
  classical
  intro n hn
  let e : (σ →₀ ℕ) →+ (σ →₀ ℤ) :=
    Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  let T := S.map e
  have hx : e n ∈ AddSubgroup.closure (T : Set (σ →₀ ℤ)) :=
    support_subset_groupClosure_of_mul_mem_adjoin_monomial S hb hbreg hbf n hn
  have hx' : e n ∈ T ⊔ -T := by
    change e n ∈ (AddSubgroup.closure (T : Set (σ →₀ ℤ))).toAddSubmonoid at hx
    simpa only [AddSubgroup.closure_toAddSubmonoid, AddSubmonoid.closure_union,
      AddSubmonoid.closure_neg, AddSubmonoid.closure_eq] using hx
  obtain ⟨a, ha, c, hc, hac⟩ := AddSubmonoid.mem_sup.mp hx'
  obtain ⟨s, hs, rfl⟩ := AddSubmonoid.mem_map.mp ha
  obtain ⟨t, ht, htc⟩ := AddSubmonoid.mem_map.mp (AddSubmonoid.mem_neg.mp hc)
  refine ⟨s, hs, t, ht, ?_⟩
  change e n = e s - e t
  rw [htc, sub_neg_eq_add]
  exact hac.symm

/-- For the bottom exponent monoid the generated group is trivial, so the
ambient-regular denominator conclusion is constant support. -/
theorem bottom_denominator_support
    {b f : MvPolynomial σ R}
    (hb : b ∈ Algebra.adjoin R
      (Set.range fun s : (⊥ : AddSubmonoid (σ →₀ ℕ)) =>
        monomial (s : σ →₀ ℕ) (1 : R)))
    (hbreg : IsLeftRegular b)
    (hbf : b * f ∈ Algebra.adjoin R
      (Set.range fun s : (⊥ : AddSubmonoid (σ →₀ ℕ)) =>
        monomial (s : σ →₀ ℕ) (1 : R))) :
    ∀ n ∈ f.support, n = 0 := by
  classical
  intro n hn
  let e : (σ →₀ ℕ) →+ (σ →₀ ℤ) :=
    Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  have h := support_subset_groupClosure_of_mul_mem_adjoin_monomial
    (⊥ : AddSubmonoid (σ →₀ ℕ)) hb hbreg hbf n hn
  have h0 : e n = 0 := by
    simpa only [AddSubmonoid.coe_bot, Set.image_singleton, map_zero,
      AddSubgroup.closure_singleton_zero, AddSubgroup.mem_bot] using h
  ext i
  have hi : (n i : ℤ) = 0 := congrArg (fun m : σ →₀ ℤ => m i) h0
  simpa using hi

/-- With `X` and `XY` in the adjoin, `X * Y` is in it and `X` is ambient
regular, but `Y` need not be in it. Its exponent does belong to the generated group. -/
theorem group_support_does_not_mean_monoid_support :
    ∃ S : AddSubmonoid (Bool →₀ ℕ),
      (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
          (Finsupp.single true 1) ∈
        AddSubgroup.closure
          ((Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)) ''
            (S : Set (Bool →₀ ℕ))) ∧
      (monomial (Finsupp.single true 1) (1 : ℤ) : MvPolynomial Bool ℤ) ∉
        Algebra.adjoin ℤ
          (Set.range fun s : S => monomial (s : Bool →₀ ℕ) (1 : ℤ)) := by
  classical
  let S : AddSubmonoid (Bool →₀ ℕ) :=
    { carrier := {m | m true ≤ m false}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change a true ≤ a false at ha
        change b true ≤ b false at hb
        change (a + b) true ≤ (a + b) false
        simpa only [Finsupp.add_apply] using add_le_add ha hb }
  let x : Bool →₀ ℕ := Finsupp.single false 1
  let y : Bool →₀ ℕ := Finsupp.single true 1
  have hx : x ∈ S := by simp [S, x]
  have hxy : x + y ∈ S := by simp [S, x, y]
  have hb : (monomial x (1 : ℤ) : MvPolynomial Bool ℤ) ∈
      Algebra.adjoin ℤ
        (Set.range fun s : S => monomial (s : Bool →₀ ℕ) (1 : ℤ)) :=
    Algebra.subset_adjoin ⟨⟨x, hx⟩, rfl⟩
  have hbf : (monomial x (1 : ℤ) : MvPolynomial Bool ℤ) * monomial y 1 ∈
      Algebra.adjoin ℤ
        (Set.range fun s : S => monomial (s : Bool →₀ ℕ) (1 : ℤ)) := by
    rw [monomial_mul_monomial, one_mul]
    exact Algebra.subset_adjoin ⟨⟨x + y, hxy⟩, rfl⟩
  have hbreg : IsLeftRegular (monomial x (1 : ℤ) : MvPolynomial Bool ℤ) :=
    isRegular_one.monomial.left
  refine ⟨S, ?_, ?_⟩
  · exact support_subset_groupClosure_of_mul_mem_adjoin_monomial S hb hbreg hbf y (by simp)
  · intro h
    let φ : MvPolynomial Bool ℤ →ₐ[ℤ] ℤ :=
      aeval (fun i : Bool => if i then 1 else 0)
    let ψ : MvPolynomial Bool ℤ →ₐ[ℤ] ℤ := aeval (fun _ : Bool => 0)
    have hA : Algebra.adjoin ℤ
        (Set.range fun s : S => monomial (s : Bool →₀ ℕ) (1 : ℤ)) ≤
        AlgHom.equalizer φ ψ := by
      apply Algebra.adjoin_le
      rintro _ ⟨m, rfl⟩
      change φ (monomial (m : Bool →₀ ℕ) 1) = ψ (monomial (m : Bool →₀ ℕ) 1)
      by_cases hm : (m : Bool →₀ ℕ) false = 0
      · have hmtrue : (m : Bool →₀ ℕ) true = 0 := by
          have hmle := m.property
          change (m : Bool →₀ ℕ) true ≤ (m : Bool →₀ ℕ) false at hmle
          exact Nat.eq_zero_of_le_zero (by simpa only [hm] using hmle)
        have hmzero : (m : Bool →₀ ℕ) = 0 := by
          ext i
          cases i <;> simp [hm, hmtrue]
        simp [φ, ψ, hmzero]
      · simp only [φ, ψ, aeval_monomial,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        simp [hm]
    have heval : φ (monomial y 1) = ψ (monomial y 1) := hA h
    norm_num [φ, ψ, aeval_monomial, y] at heval

end ToricIdealsTest
