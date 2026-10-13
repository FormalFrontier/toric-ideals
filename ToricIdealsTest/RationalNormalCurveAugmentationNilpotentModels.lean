/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ToricIdeals.RationalNormalCurve

/-!
# Surviving nilpotent coefficients in Hankel quotients

The coefficient `2` in `ZMod 4` is nonzero with square zero. In every degree,
including zero and one, its canonical coefficient class in the full quotient by
the Hankel minors is also nonzero with square zero. The quotient witness is
identified both with the class of `C 2` and with the canonical coefficient
`algebraMap`.

If this constant class were zero, `C 2` would belong to the Hankel ideal and
hence to the parametrization kernel. The parametrization preserves constants,
so injectivity of `MvPolynomial.C` would force `2 = 0`. This argument needs only
containment in the kernel, not equality with the kernel. Square zero follows
from the two ring homomorphisms' power laws.

## References

The constant-class proofs follow the rational-normal-curve reduced and domain
models by Formal Frontier Agents and the coefficient-preservation argument in
`quotient_isReduced_iff`. They use Mathlib's monoid-algebra, constant-polynomial
and ideal-quotient APIs.
-/

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve.NilpotentModels

noncomputable section

private theorem two_mod_four_nonzero_square_zero :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  constructor <;> decide

/-- The nonzero square-zero coefficient `2` survives as its canonical
coefficient class in the full Hankel quotient in every degree. -/
private theorem two_mod_four_all_degrees_nilpotent_witness :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      ∀ n : ℕ, ∃ q : Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n,
        q = algebraMap (ZMod 4) (Source (ZMod 4) n ⧸ hankelIdeal (ZMod 4) n)
          (2 : ZMod 4) ∧
        q = Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (C (2 : ZMod 4)) ∧
        q ≠ 0 ∧ q ^ 2 = 0 := by
  refine ⟨two_mod_four_nonzero_square_zero.1, two_mod_four_nonzero_square_zero.2, ?_⟩
  intro n
  refine ⟨Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (C (2 : ZMod 4)), ?_, rfl, ?_, ?_⟩
  · simpa only [MvPolynomial.algebraMap_eq] using
      Ideal.Quotient.mk_algebraMap (ZMod 4) (hankelIdeal (ZMod 4) n) (2 : ZMod 4)
  · intro hzero
    have hker := hankelIdeal_le_ker (ZMod 4) n
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have htarget : (C (2 : ZMod 4) : Target (ZMod 4)) = 0 := by
      simpa only [RingHom.mem_ker, rncMap_C] using hker
    apply two_mod_four_nonzero_square_zero.1
    apply MvPolynomial.C_injective (Fin 2) (ZMod 4)
    simpa only [map_zero] using htarget
  · simpa only [map_pow, map_zero] using
      congrArg (fun c : ZMod 4 ↦ Ideal.Quotient.mk (hankelIdeal (ZMod 4) n) (C c))
        two_mod_four_nonzero_square_zero.2

end

end ToricIdeals.RationalNormalCurve.NilpotentModels
