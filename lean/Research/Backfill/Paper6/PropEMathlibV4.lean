import Research.Backfill.Paper6.PropEExclusion

/-!
# Proposition E's first sentence in the V4 Mathlib primitive contract

V4 retains the module name ChallengeV3 and namespace BackfillPaper6.V3.
Root must resolve that module to statements-v4/ChallengeV3.lean and rebuild
the imported local sources against the V4 statement snapshot.

The complete PropE proof candidate and its actual numerical certificate chain
are not accepted dependencies at this author handoff. This module takes the
first conjunct of that real complete theorem; it does not introduce a premise
or replace any pending dependency with an axiom. No validation is claimed.

This restatement contributes zero independent mathematical-result credit.
-/

set_option autoImplicit false

namespace Paper6MathlibRestatementsV4

/-- Actual multivariate polynomials, both bounds, actual evaluation and all eight
excluded weights appear without any extra premise or squarefree restriction. -/
theorem propE_mathlib :
    ∀ p : MvPolynomial (Fin 14) (ZMod 2), p.support.card ≤ 5 → p.totalDegree ≤ 7 →
      hammingNorm (fun x : Fin 14 → ZMod 2 => MvPolynomial.eval x p) ∉
        ({322, 326, 330, 334, 16050, 16054, 16058, 16062} : Finset ℕ) := by
  intro p hterms hdegree
  exact Paper6FiveExclusion.check_PropE.1 p hterms hdegree

/-- Exact retained V4 contract; this check does not certify pending dependencies. -/
theorem check_PropE_mathlib : BackfillPaper6.V3.PropE_mathlib := propE_mathlib

end Paper6MathlibRestatementsV4

#print axioms Paper6MathlibRestatementsV4.propE_mathlib
#print axioms Paper6MathlibRestatementsV4.check_PropE_mathlib
#print Paper6MathlibRestatementsV4.check_PropE_mathlib
