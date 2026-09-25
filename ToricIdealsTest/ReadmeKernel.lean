/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ToricIdeals.RationalNormalCurve

/-! # README example: the positive-degree kernel through a direct leaf import -/

open ToricIdeals.RationalNormalCurve

universe u

private theorem readme_degree_two_kernel (k : Type u) [CommRing k] :
    hankelIdeal k 2 = RingHom.ker (rncMap k 2) :=
  hankelIdeal_eq_ker k 2 (by decide)
