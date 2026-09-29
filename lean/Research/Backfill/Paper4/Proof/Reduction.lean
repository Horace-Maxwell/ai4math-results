import Research.Backfill.Paper4.Proof.ReductionBasics

/-! Proof source for the full Section 4 reduction statement.
Acceptance evidence is recorded separately. -/

set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_Sec4_reduction : Challenge.Sec4_reduction := by
  classical
  intro V _ G hcard hmedian
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htriangle : G.CliqueFree 3 := check_Sec4_median_triangleFree V G hmedian
  obtain ⟨v, hv⟩ := check_Sec4_nonCutVertex V G hmedian.1
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro t ht
    exact htriangle _ ((SimpleGraph.isNClique_induce_iff (G := G) {v}ᶜ t 3).mp ht)
  · obtain ⟨w, hw⟩ := exists_ne v
    exact (hmedian.1 v w).nonempty_neighborSet_left hw.symm
  · intro a b hva hvb hab
    have hclique : G.IsNClique 3 {v, a, b} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hva, hvb, hab⟩
    exact htriangle _ hclique

#print axioms check_Sec4_reduction

end CodexPaper4
