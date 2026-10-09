import Research.Backfill.Paper6.LiteralCertificates
import Research.Backfill.Paper6.LiteralVennBounds3
import Research.Backfill.Paper6.LiteralVennWeight3

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem low_weight3 (S : Fin 3 → Finset (Fin 12))
    (hcard : ∀ i, (S i).card ≤ 6)
    (hsmall : hammingNorm (fun x : Pt 12 => ∑ i : Fin 3, ∏ j ∈ S i, x j) ≤ 161) :
    hammingNorm (fun x : Pt 12 => ∑ i : Fin 3, ∏ j ∈ S i, x j) ∈ smallWeights := by
  have hc := counts_complete3 ((venn S ({0} : Finset (Fin 3))).card) ((venn S ({1} : Finset (Fin 3))).card) ((venn S ({0, 1} : Finset (Fin 3))).card) ((venn S ({2} : Finset (Fin 3))).card) ((venn S ({0, 2} : Finset (Fin 3))).card) ((venn S ({1, 2} : Finset (Fin 3))).card) ((venn S ({0, 1, 2} : Finset (Fin 3))).card)
    (actual_venn_bounds3 S hcard) all_counts3
  exact okayWeight_sound
    (hammingNorm (fun x : Pt 12 => ∑ i : Fin 3, ∏ j ∈ S i, x j))
    (Eq.mpr
      (congrArg (fun z : ℤ => okayWeight z = true) (actual_venn_weight3 S))
      hc)
    hsmall

#print axioms Paper6LiteralLouWang.low_weight3

end Paper6LiteralLouWang
