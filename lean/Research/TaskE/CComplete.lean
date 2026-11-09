import Research.Backfill.Paper1.Prop31
import Research.TaskE.C0Complete
import Research.TaskE.C1AltComplete
import Research.TaskE.C1One
import Research.TaskE.C1Long
import Research.TaskE.CFiveChain
import Research.TaskE.CTerminal

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

/-- Full original C, with no upper bound on the exponent. -/
lemma full_C {a : ℕ} (ha : 3 ≤ a) {q : ℝ} (hq : 5 ≤ q) : CondC a 3 q := by
  classical
  intro g hg hga hneg hplus
  by_cases hhigh : 2 * deltaK a 3 < DeltaC a 3 g
  · exact Or.inl hhigh
  right
  have hlow : DeltaC a 3 g ≤ 2 * deltaK a 3 := le_of_not_gt hhigh
  have hna := CodexPaper1.Prop31.last_not_pmAlt hga hneg
  refine ⟨?_, five_chain a ha q hq g hg hna, terminal_ratios a ha q hq g hg hna⟩
  intro k _hk y hy c hc hanti
  have hu := ik_unit_positive hq hy
  rcases k with _ | k
  · have hh := c0_zero a ha q hq g hg hga hneg hplus hlow y hy c hc
      (by simpa only [Nat.zero_add, pow_one, neg_one_mul] using hanti)
    simpa [mu, muSeq] using hh
  rcases k with _ | k
  · have hs : Icc (1 : ℕ) 1 = {1} := by decide
    have hh : (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 g +
        psi a 3 q y c (fun i => -mu q 0 * g i) >
        q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 g) := by
      by_cases halt : IsPmAlt a c
      · exact c1_one_alt a ha q hq g hg hna y hu.1.le hu.2 c hc halt
      · exact c1_one_nonalt a ha q hq g hg hna y hu.1.le hu.2 c hc halt
    simpa only [Nat.zero_add, hs, sum_singleton, pow_one, Nat.cast_one, sub_self, neg_one_mul] using hh
  · exact c1_long a ha q hq g hg hna (k + 2) (by omega) y hu.1.le hu.2 c hc

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.full_C
