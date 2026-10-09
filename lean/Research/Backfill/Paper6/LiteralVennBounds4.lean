import Research.Backfill.Paper6.LiteralVennFinite4

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem actual_venn_bounds4 (S : Fin 4 → Finset (Fin 12))
    (hcard : ∀ i, (S i).card ≤ 6) :
    countBounds4 ((venn S ({0} : Finset (Fin 4))).card) ((venn S ({1} : Finset (Fin 4))).card) ((venn S ({0, 1} : Finset (Fin 4))).card) ((venn S ({2} : Finset (Fin 4))).card) ((venn S ({0, 2} : Finset (Fin 4))).card) ((venn S ({1, 2} : Finset (Fin 4))).card) ((venn S ({0, 1, 2} : Finset (Fin 4))).card) ((venn S ({3} : Finset (Fin 4))).card) ((venn S ({0, 3} : Finset (Fin 4))).card) ((venn S ({1, 3} : Finset (Fin 4))).card) ((venn S ({0, 1, 3} : Finset (Fin 4))).card) ((venn S ({2, 3} : Finset (Fin 4))).card) ((venn S ({0, 2, 3} : Finset (Fin 4))).card) ((venn S ({1, 2, 3} : Finset (Fin 4))).card) ((venn S ({0, 1, 2, 3} : Finset (Fin 4))).card) := by
  have ht := union_card_as_venn_sum S ({0, 1, 2, 3} : Finset (Fin 4))
  rw [Paper6LiteralVennFinite.sum_meeting4_15] at ht
  have htotal : (({0, 1, 2, 3} : Finset (Fin 4)).biUnion S).card ≤ 12 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (({0, 1, 2, 3} : Finset (Fin 4)).biUnion S)
  have hc0 := union_card_as_venn_sum S ({0} : Finset (Fin 4))
  rw [Finset.singleton_biUnion, Paper6LiteralVennFinite.sum_meeting4_1] at hc0
  have hd0 := hcard (0 : Fin 4)
  have hc1 := union_card_as_venn_sum S ({1} : Finset (Fin 4))
  rw [Finset.singleton_biUnion, Paper6LiteralVennFinite.sum_meeting4_2] at hc1
  have hd1 := hcard (1 : Fin 4)
  have hc2 := union_card_as_venn_sum S ({2} : Finset (Fin 4))
  rw [Finset.singleton_biUnion, Paper6LiteralVennFinite.sum_meeting4_4] at hc2
  have hd2 := hcard (2 : Fin 4)
  have hc3 := union_card_as_venn_sum S ({3} : Finset (Fin 4))
  rw [Finset.singleton_biUnion, Paper6LiteralVennFinite.sum_meeting4_8] at hc3
  have hd3 := hcard (3 : Fin 4)
  exact ⟨le_trans (le_of_eq ht.symm) htotal,
    le_trans (le_of_eq hc0.symm) hd0,
    le_trans (le_of_eq hc1.symm) hd1,
    le_trans (le_of_eq hc2.symm) hd2,
    le_trans (le_of_eq hc3.symm) hd3⟩

#print axioms Paper6LiteralLouWang.actual_venn_bounds4

end Paper6LiteralLouWang
