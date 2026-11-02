/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.ZMod.Basic
import ToricIdeals.MvPolynomial.MonomialModuleFinite

/-!
# A proper finite monomial extension with infinitely many variables

Over `ZMod 4`, require the exponent of variable `0` to be even and leave all
other variables unrestricted. The resulting monomial subalgebra is proper, but
the whole polynomial algebra is finite over it: the exponents have the two
remainders `0` and `Finsupp.single 0 1`.

This example concerns coefficients with zero divisors and infinitely many
unrestricted variables. The source exponent monoid contains every independent
coordinate vector at a positive index, so it is not finitely generated. Its
finite translate cover uses parity at just one coordinate. The module structure
is induced by inclusion of the coefficient-one monomial adjoins.
-/

namespace ToricIdealsTest

open MvPolynomial
open scoped Pointwise

private def parityExponents : AddSubmonoid (ℕ →₀ ℕ) where
  carrier := {n | Even (n 0)}
  zero_mem' := Even.zero
  add_mem' := fun hm hn => hm.add hn

private theorem parity_cover :
    (↑(⊤ : AddSubmonoid (ℕ →₀ ℕ)) : Set (ℕ →₀ ℕ)) ⊆
      (parityExponents : Set (ℕ →₀ ℕ)) + {0, Finsupp.single 0 1} := by
  intro n _
  let e : ℕ →₀ ℕ := Finsupp.single 0 (n 0 % 2)
  have he : e ∈ ({0, Finsupp.single 0 1} : Set (ℕ →₀ ℕ)) := by
    rcases Nat.mod_two_eq_zero_or_one (n 0) with h | h <;> simp [e, h]
  have hs : n - e ∈ parityExponents := by
    change Even ((n - e) 0)
    simp only [Finsupp.tsub_apply, e, Finsupp.single_eq_same]
    rw [Nat.even_iff]
    omega
  have hle : e ≤ n := Finsupp.single_le_iff.mpr (Nat.mod_le (n 0) 2)
  exact Set.mem_add.mpr ⟨n - e, hs, e, he, tsub_add_cancel_of_le hle⟩

private theorem parity_adjoin_le :
    Algebra.adjoin (ZMod 4)
        (Set.range fun s : parityExponents => monomial (s : ℕ →₀ ℕ) (1 : ZMod 4)) ≤
      Algebra.adjoin (ZMod 4)
        (Set.range fun t : (⊤ : AddSubmonoid (ℕ →₀ ℕ)) =>
          monomial (t : ℕ →₀ ℕ) (1 : ZMod 4)) := by
  apply Algebra.adjoin_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨(s : ℕ →₀ ℕ), trivial⟩, rfl⟩

private theorem parity_adjoin_lt :
    Algebra.adjoin (ZMod 4)
        (Set.range fun s : parityExponents => monomial (s : ℕ →₀ ℕ) (1 : ZMod 4)) <
      Algebra.adjoin (ZMod 4)
        (Set.range fun t : (⊤ : AddSubmonoid (ℕ →₀ ℕ)) =>
          monomial (t : ℕ →₀ ℕ) (1 : ZMod 4)) := by
  refine lt_iff_le_not_ge.mpr ⟨parity_adjoin_le, ?_⟩
  intro h
  have hx : (monomial (Finsupp.single 0 1) (1 : ZMod 4) : MvPolynomial ℕ (ZMod 4)) ∈
      Algebra.adjoin (ZMod 4)
        (Set.range fun s : parityExponents => monomial (s : ℕ →₀ ℕ) (1 : ZMod 4)) :=
    h (Algebra.subset_adjoin ⟨⟨Finsupp.single 0 1, trivial⟩, rfl⟩)
  have hnot : Finsupp.single 0 1 ∉ parityExponents := by
    change ¬ Even ((Finsupp.single 0 1 : ℕ →₀ ℕ) 0)
    simp
  rcases (monomial_mem_adjoin_monomial_iff parityExponents _ _).mp hx with hs | hzero
  · exact hnot hs
  · exact (by decide : (1 : ZMod 4) ≠ 0) hzero

/-- The parity subalgebra is proper and its inclusion gives a finite module,
even with zero divisors in the coefficients and infinitely many variables. -/
example :
    Algebra.adjoin (ZMod 4)
        (Set.range fun s : parityExponents => monomial (s : ℕ →₀ ℕ) (1 : ZMod 4)) <
      Algebra.adjoin (ZMod 4)
        (Set.range fun t : (⊤ : AddSubmonoid (ℕ →₀ ℕ)) =>
          monomial (t : ℕ →₀ ℕ) (1 : ZMod 4)) ∧
    @Module.Finite
      (Algebra.adjoin (ZMod 4)
        (Set.range fun s : parityExponents => monomial (s : ℕ →₀ ℕ) (1 : ZMod 4)))
      (Algebra.adjoin (ZMod 4)
        (Set.range fun t : (⊤ : AddSubmonoid (ℕ →₀ ℕ)) =>
          monomial (t : ℕ →₀ ℕ) (1 : ZMod 4))) _ _
      (Subalgebra.inclusion parity_adjoin_le).toRingHom.toModule := by
  refine ⟨parity_adjoin_lt, ?_⟩
  apply moduleFinite_adjoin_monomial_of_subset_add
    (R := ZMod 4) (S := parityExponents) (T := ⊤)
    (E := {0, Finsupp.single 0 1}) le_top
  · exact (Set.finite_singleton (Finsupp.single 0 1)).insert 0
  · intro e _
    trivial
  · exact parity_cover

end ToricIdealsTest
