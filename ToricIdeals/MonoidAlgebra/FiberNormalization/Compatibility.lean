/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.FiberNormalization

/-!
# Compatibility names for coefficientwise fiber normalization

The coefficientwise normalization theorems for additive monoid algebras live in
`GroupRings.MonoidAlgebra.FiberNormalization`, in the root `AddMonoidAlgebra`
namespace. This module also provides their names in
`ToricIdeals.AddMonoidAlgebra`.

The theorems apply to left ideals over arbitrary coefficient rings, without
commutativity or surjectivity assumptions. The first theorem allows an arbitrary
target index type and index function; the kernel and membership theorems use
an additive exponent homomorphism.

## References

Formal Frontier Agents, the coefficientwise fiber-normalization theorems in
`GroupRings.MonoidAlgebra.FiberNormalization`.
-/

public section

namespace ToricIdeals

@[deprecated (since := "2026-11-04")]
alias AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero :=
  _root_.AddMonoidAlgebra.mem_ideal_of_mapDomain_eq_zero

@[deprecated (since := "2026-11-04")]
alias AddMonoidAlgebra.ker_mapDomainRingHom_le :=
  _root_.AddMonoidAlgebra.ker_mapDomainRingHom_le

@[deprecated (since := "2026-11-04")]
alias AddMonoidAlgebra.ideal_eq_ker_mapDomainRingHom :=
  _root_.AddMonoidAlgebra.ideal_eq_ker_mapDomainRingHom

@[deprecated (since := "2026-11-04")]
alias AddMonoidAlgebra.mem_ideal_iff_mapDomain_eq_zero :=
  _root_.AddMonoidAlgebra.mem_ideal_iff_mapDomain_eq_zero

end ToricIdeals
