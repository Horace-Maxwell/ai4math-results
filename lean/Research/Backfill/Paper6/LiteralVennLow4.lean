import Research.Backfill.Paper6.LiteralCertificates
import Research.Backfill.Paper6.LiteralVennBounds4
import Research.Backfill.Paper6.LiteralVennWeight4

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem low_weight4 (S : Fin 4 → Finset (Fin 12))
    (hcard : ∀ i, (S i).card ≤ 6)
    (hsmall : hammingNorm (fun x : Pt 12 => ∑ i : Fin 4, ∏ j ∈ S i, x j) ≤ 161) :
    hammingNorm (fun x : Pt 12 => ∑ i : Fin 4, ∏ j ∈ S i, x j) ∈ smallWeights := by
  have hc := counts_complete4 ((venn S ({0} : Finset (Fin 4))).card) ((venn S ({1} : Finset (Fin 4))).card) ((venn S ({0, 1} : Finset (Fin 4))).card) ((venn S ({2} : Finset (Fin 4))).card) ((venn S ({0, 2} : Finset (Fin 4))).card) ((venn S ({1, 2} : Finset (Fin 4))).card) ((venn S ({0, 1, 2} : Finset (Fin 4))).card) ((venn S ({3} : Finset (Fin 4))).card) ((venn S ({0, 3} : Finset (Fin 4))).card) ((venn S ({1, 3} : Finset (Fin 4))).card) ((venn S ({0, 1, 3} : Finset (Fin 4))).card) ((venn S ({2, 3} : Finset (Fin 4))).card) ((venn S ({0, 2, 3} : Finset (Fin 4))).card) ((venn S ({1, 2, 3} : Finset (Fin 4))).card) ((venn S ({0, 1, 2, 3} : Finset (Fin 4))).card)
    (actual_venn_bounds4 S hcard) all_counts4
  exact okayWeight_sound
    (hammingNorm (fun x : Pt 12 => ∑ i : Fin 4, ∏ j ∈ S i, x j))
    (Eq.mpr
      (congrArg (fun z : ℤ => okayWeight z = true) (actual_venn_weight4 S))
      hc)
    hsmall

#print axioms Paper6LiteralLouWang.low_weight4

end Paper6LiteralLouWang
