import Research.Backfill.Paper4.Challenge

/-! Proof source for the two basic graph reductions in Section 4.
Acceptance evidence is recorded separately. -/

set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_Sec4_median_triangleFree : Challenge.Sec4_median_triangleFree := by
  classical
  intro V _ G hmedian t ht
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ :=
    (SimpleGraph.is3Clique_iff (G := G)).mp ht
  obtain ⟨m, hm, _⟩ := hmedian.2 a b c
  rcases hm with ⟨hmab, hmac, hmbc⟩
  have hdab : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
  have hdac : G.dist a c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hac
  have hdbc : G.dist b c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbc
  change G.dist a m + G.dist m b = G.dist a b at hmab
  change G.dist a m + G.dist m c = G.dist a c at hmac
  change G.dist b m + G.dist m c = G.dist b c at hmbc
  rw [G.dist_comm (u := m) (v := b), hdab] at hmab
  rw [G.dist_comm (u := m) (v := c), hdac] at hmac
  rw [G.dist_comm (u := m) (v := c), hdbc] at hmbc
  omega

theorem check_Sec4_nonCutVertex : Challenge.Sec4_nonCutVertex := by
  intro V _ _ G hconn
  exact hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial

#print axioms check_Sec4_median_triangleFree
#print axioms check_Sec4_nonCutVertex

end CodexPaper4
