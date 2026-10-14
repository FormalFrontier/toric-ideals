/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.RationalNormalCurve.ExponentImage

/-!
# Surjectivity of the rational-normal-curve parametrization

The raw polynomial map `rncMap R n` sends `xᵢ` to `a^(n-i) b^i`. It reaches
the full bivariate polynomial target exactly when `n = 1` or the coefficient
semiring is subsingleton. This holds over arbitrary commutative semirings,
in every coefficient universe and every natural-number degree.

At degree one the exponent map is the identity, and surjectivity of coefficient
transport gives a preimage for every polynomial. With subsingleton coefficients
the target itself is subsingleton. Conversely, over nontrivial coefficients,
the first target variable has coefficient one at exponent `(1,0)`. The exponent
image criterion forces `n` to divide its total one if this variable is reached.

This concerns the full polynomial source and target, not a quotient or the
parametrization image. At degree zero the raw map sends its sole variable to
`1`, whereas the full degree-zero Hankel quotient retains its indeterminate.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve` and
  `ToricIdeals.RationalNormalCurve.ExponentImage`, for the parametrization,
  the coefficient-vanishing API and the exponent-image divisibility criterion.
* Mathlib contributors, `Mathlib.Data.Finsupp.Basic` and
  `Mathlib.Algebra.MonoidAlgebra.Defs`, for surjectivity of coefficient transport
  and the coefficient equivalence.
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Basic` and
  `Mathlib.Logic.Function.Basic`, for variable coefficients and surjectivity
  onto subsingleton targets.
-/

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

/-- The raw rational-normal-curve parametrization reaches the full bivariate
polynomial target exactly in degree one or over a subsingleton coefficient
semiring. This includes degree zero and every coefficient universe, with no
nontriviality, domain, ring or positive-degree hypothesis. The proof combines
Mathlib's coefficient transport with the exponent-image divisibility criterion. -/
theorem rncMap_surjective_iff (R : Type u) [CommSemiring R] (n : ℕ) :
    Function.Surjective (rncMap R n) ↔ n = 1 ∨ Subsingleton R := by
  constructor
  · intro hsurj
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let : Nontrivial R := hR
      left
      by_contra hn
      have hnot : Finsupp.single (0 : Fin 2) 1 ∉ Set.range (rncExponent n) := by
        intro hmem
        have hdiv := (mem_mrange_rncExponent_iff n (Finsupp.single (0 : Fin 2) 1)).mp
          (AddMonoidHom.mem_mrange.mpr hmem)
        exact hn (by simpa using hdiv)
      obtain ⟨p, hp⟩ := hsurj (MvPolynomial.X (0 : Fin 2))
      have hcoeff := coeff_rncMap_of_not_mem_range R n p
        (Finsupp.single (0 : Fin 2) 1) hnot
      rw [hp, MvPolynomial.coeff_X_same] at hcoeff
      exact one_ne_zero hcoeff
  · rintro (rfl | hR)
    · have hexp : Function.Surjective (rncExponent 1) :=
        fun d => ⟨d, rncExponent_one d⟩
      intro q
      obtain ⟨d, hd⟩ := Finsupp.mapDomain_surjective (M := R) hexp q.coeff
      refine ⟨AddMonoidAlgebra.ofCoeff d, ?_⟩
      rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
      apply AddMonoidAlgebra.coeff_injective
      simpa only [AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff] using hd
    · let : Subsingleton R := hR
      exact Function.surjective_to_subsingleton (rncMap R n)

end

end

end ToricIdeals.RationalNormalCurve
