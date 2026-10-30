/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals
import Mathlib.Tactic.NormNum

/-! # A nonzero cusp binomial through the root-import API

The two exponent vectors below have weight `17` for weights `(3,2)`.
The binomial is not the defining generator and is nonzero over the integers.
Its ideal membership is detected by the natural-weight pushforward.
-/

open AddMonoidAlgebra

private theorem cusp_binomial_mem_and_ne_zero :
    let d : Fin 2 →₀ ℕ := Finsupp.single 0 5 + Finsupp.single 1 1
    let e : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 7
    (single d (1 : ℤ) - single e 1 : AddMonoidAlgebra ℤ (Fin 2 →₀ ℕ)) ∈
        Ideal.span {single (Finsupp.single (0 : Fin 2) 2) (1 : ℤ) -
          single (Finsupp.single (1 : Fin 2) 3) (1 : ℤ)} ∧
      (single d (1 : ℤ) - single e 1 : AddMonoidAlgebra ℤ (Fin 2 →₀ ℕ)) ≠ 0 := by
  dsimp only
  constructor
  · apply (mem_span_iff_mapDomain_weight_eq_zero_of_coprime
      (a := 2) (b := 3) (by decide)).2
    change (mapDomainRingHom ℤ (Finsupp.weight
      (fun i : Fin 2 => if i = 0 then 3 else 2))) _ = 0
    rw [map_sub]
    norm_num [mapDomain_single, map_add, Finsupp.weight_single]
  · intro h
    have hd : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 7 : Fin 2 →₀ ℕ) ≠
        Finsupp.single 0 5 + Finsupp.single 1 1 := by
      intro heq
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
      norm_num [Finsupp.single_apply] at this
    have hc := congrArg (fun f : AddMonoidAlgebra ℤ (Fin 2 →₀ ℕ) =>
      f.coeff (Finsupp.single 0 5 + Finsupp.single 1 1)) h
    simp [coeff_sub, coeff_single, hd] at hc
