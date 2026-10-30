/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.MonoidAlgebra.CoprimeWeights
import Mathlib.RingTheory.Ideal.Maps

/-!
# Kernels of bivariate natural weights

For any ring `R` and natural numbers `a, b` not both zero, the kernel of the
stock weight pushforward with weights `(b,a)` is the principal left ideal
spanned by `X₀^(a / Nat.gcd a b) - X₁^(b / Nat.gcd a b)`. The characteristic
membership theorem uses vanishing under the raw `AddMonoidAlgebra.mapDomain`.
Noncommutative coefficient rings, zero rings and both zero-weight axes are included.

The proof reduces the weights to a coprime pair and postcomposes by injective
multiplication on the natural exponent index, not on coefficients. It reuses
`ToricIdeals.MonoidAlgebra.CoprimeWeights` and Mathlib's weight, pushforward,
natural gcd and kernel-composition APIs.

The pair `(0,0)` is excluded: its zero-weight kernel generally needs both
`X₀ - 1` and `X₁ - 1`. No surjectivity onto the full target is asserted.
-/

@[expose] public section

namespace AddMonoidAlgebra

universe u

private theorem weight_eq_mulLeft_comp_div_gcd (a b : ℕ) :
    (Finsupp.weight (fun i : Fin 2 => if i = (0 : Fin 2) then b else a) :
      (Fin 2 →₀ ℕ) →+ ℕ) =
    (AddMonoidHom.mulLeft (Nat.gcd a b)).comp
      (Finsupp.weight (fun i : Fin 2 =>
        if i = (0 : Fin 2) then b / Nat.gcd a b else a / Nat.gcd a b)) := by
  apply Finsupp.addHom_ext
  intro i n
  simp only [AddMonoidHom.comp_apply, Finsupp.weight_single, AddMonoidHom.coe_mulLeft]
  change n * (if i = 0 then b else a) =
    Nat.gcd a b * (n * (if i = 0 then b / Nat.gcd a b else a / Nat.gcd a b))
  have ha := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    calc
      n * b = n * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [hb]
      _ = Nat.gcd a b * (n * (b / Nat.gcd a b)) := by ac_rfl
  · simp only [hi, ite_false]
    calc
      n * a = n * (Nat.gcd a b * (a / Nat.gcd a b)) := by rw [ha]
      _ = Nat.gcd a b * (n * (a / Nat.gcd a b)) := by ac_rfl

/-- For a natural pair not both zero, the stock weight pushforward has kernel
spanned as a left ideal by the gcd-reduced binomial. This follows from the
coprime presentation by injective postcomposition on natural exponent indices. -/
theorem ker_mapDomainRingHom_weight_eq_span
    {R : Type u} [Ring R] {a b : ℕ} (hab : a ≠ 0 ∨ b ≠ 0) :
    RingHom.ker
      (AddMonoidAlgebra.mapDomainRingHom R
        (Finsupp.weight
          (fun i : Fin 2 => if i = (0 : Fin 2) then b else a) :
            (Fin 2 →₀ ℕ) →+ ℕ)) =
      Ideal.span
        {(single (Finsupp.single (0 : Fin 2) (a / Nat.gcd a b)) (1 : R) -
          single (Finsupp.single (1 : Fin 2) (b / Nat.gcd a b)) (1 : R) :
            AddMonoidAlgebra R (Fin 2 →₀ ℕ))} := by
  have hg : 0 < Nat.gcd a b := by
    rcases hab with ha | hb
    · exact Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
    · exact Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb)
  have hinj : Function.Injective
      (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.mulLeft (Nat.gcd a b))) := by
    intro f k hfk
    apply AddMonoidAlgebra.mapDomain_injective
      (f := fun n : ℕ => Nat.gcd a b * n)
      (fun _ _ hxy => Nat.eq_of_mul_eq_mul_left hg hxy)
    simpa only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidHom.coe_mulLeft] using hfk
  rw [weight_eq_mulLeft_comp_div_gcd, AddMonoidAlgebra.mapDomainRingHom_comp,
    RingHom.ker_comp_of_injective _ hinj]
  exact ker_mapDomainRingHom_weight_eq_span_of_coprime
    (Nat.coprime_div_gcd_div_gcd hg)

/-- Membership in the gcd-reduced principal left ideal is equivalent to
vanishing under the raw stock weight pushforward, for any ring and any
natural pair not both zero. -/
theorem mem_span_iff_mapDomain_weight_eq_zero
    {R : Type u} [Ring R] {a b : ℕ} (hab : a ≠ 0 ∨ b ≠ 0)
    {f : AddMonoidAlgebra R (Fin 2 →₀ ℕ)} :
    f ∈ Ideal.span
      {(single (Finsupp.single (0 : Fin 2) (a / Nat.gcd a b)) (1 : R) -
        single (Finsupp.single (1 : Fin 2) (b / Nat.gcd a b)) (1 : R) :
          AddMonoidAlgebra R (Fin 2 →₀ ℕ))} ↔
      AddMonoidAlgebra.mapDomain
        (Finsupp.weight
          (fun i : Fin 2 => if i = (0 : Fin 2) then b else a) :
            (Fin 2 →₀ ℕ) →+ ℕ) f = 0 := by
  rw [← ker_mapDomainRingHom_weight_eq_span hab, RingHom.mem_ker,
    AddMonoidAlgebra.mapDomainRingHom_apply]

end AddMonoidAlgebra
