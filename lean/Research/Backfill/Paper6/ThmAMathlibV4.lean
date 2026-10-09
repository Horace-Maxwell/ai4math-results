import Research.Backfill.Paper6.ThmA

/-!
# Theorem A in the unchanged Mathlib primitives of the V4 contract

V4 retains the module name ChallengeV3 and namespace BackfillPaper6.V3.
Root must resolve that module to statements-v4/ChallengeV3.lean and rebuild
the imported local sources against the V4 statement snapshot.

This is a restatement of the existing actual Theorem A proof, not an additional
independent mathematical result. Source candidate only; no run is claimed.
-/

set_option autoImplicit false

namespace Paper6MathlibRestatementsV4

/-- Every primitive condition and all seventeen explicit weights are retained. -/
theorem thmA_mathlib :
    ∀ w ∈ ({354, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196,
        8198, 8202, 8206, 8210, 16030} : Finset ℕ),
      ∃ p : MvPolynomial (Fin 14) (ZMod 2),
        p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
          hammingNorm (fun x : Fin 14 → ZMod 2 => MvPolynomial.eval x p) = w := by
  intro w hw
  obtain ⟨p, hdegree, hterms, hweight⟩ := Paper6ThmA.thmA w hw
  exact ⟨p, hdegree, hterms, hweight⟩

/-- Exact retained V4 contract, with its compatibility namespace unchanged. -/
theorem check_ThmA_mathlib : BackfillPaper6.V3.ThmA_mathlib := thmA_mathlib

end Paper6MathlibRestatementsV4

#print axioms Paper6MathlibRestatementsV4.thmA_mathlib
#print axioms Paper6MathlibRestatementsV4.check_ThmA_mathlib
#print Paper6MathlibRestatementsV4.check_ThmA_mathlib
