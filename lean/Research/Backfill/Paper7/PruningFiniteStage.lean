import Research.Backfill.Paper7.PruningPareto
import Research.Backfill.Paper7.PQListCoverage
import Research.Backfill.Paper7.DReachCompletion
import Research.Backfill.Paper7.CertifiedOutputExactness

/-! Source-only PARTIAL stage: precisely conjuncts 1, 2, 6, 7, 8 and 10 of
PruningAndEnumerationCompleteness. This theorem is not the complete contract.
The missing spectral guards and canonical search completeness remain explicit. -/
set_option autoImplicit false

namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem pruning_finite_stage :
    (∀ cyc b N s, Admissible cyc b N s →
      ∃ t, ParetoMaximal cyc b N t ∧ FeatureDominates b s t) ∧
    (∀ b N : ℕ, b ≤ N → Enumerated b N = {x | Budget b N x}) ∧
    (∀ r w t : ℕ, t < 3072 →
      (reachD1 r w t ↔ ∃ x : PQ r, weight x = w ∧ theta x = t)) ∧
    (∀ r w Q t : ℕ, t < 3072 →
      (reachD2 r w Q t ↔ ∃ x : PQ r, weight x = w ∧ qSum x = Q ∧ theta x = t)) ∧
    (∀ load cyc : Bool, ∀ b N d : ℕ, 3 ≤ b → Even b → b ≤ N → N ≤ 49 → d ≤ b →
      ∀ x : PQ b, weight («prefix» d x) ≤ N-b →
      (DReachable load cyc b N (b-d) (weight («prefix» d x))
        (qSum («prefix» d x)) (prefixTheta d x).toNat ↔
        ∃ y : PQ b, b + weight y ≤ N ∧ «prefix» d y = «prefix» d x ∧
          MomentPass cyc load false b N y)) ∧
    (∀ v b N, RunDomain v b N → ∀ x : PQ b,
      (x ∈ CertifiedOutputs v b N ↔
        x ∈ LeafSet v b N ∧ IsIntegralGraph (SG b x.1 x.2))) := by
  refine ⟨admissible_has_pareto_maximal, enumerated_eq_budget, reachD1_iff,
    reachD2_iff, ?_, ?_⟩
  · intro load cyc b N d _hb he hbN hN hd x hx
    exact dReachable_completion_iff load cyc b N d he hbN hN hd x hx
  · intro v b N _hDomain x
    exact certifiedOutputs_iff v b N x
#print axioms Paper7Pruning.pruning_finite_stage

end Paper7Pruning
