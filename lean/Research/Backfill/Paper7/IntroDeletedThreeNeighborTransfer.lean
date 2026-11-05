import Research.Backfill.Paper7.IntroStrictSpectrumThreeNeighbors
import Research.Backfill.Paper7.IntroOffCycleStrictBounds
import Research.Backfill.Paper7.IntroOffCycleTerminal
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! Exact degree and true-leaf transfer from the actual deleted-attachment
component. No terminal shape or positive complementary count is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroNonattachmentFour
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroCutGap Paper7IntroHighVertex Paper7IntroHighBranch
open Paper7IntroStrictCut Paper7IntroCycleComplement Paper7IntroPendantFour
open Paper7UnicyclicAttachment Paper7IntroTerminalExistence Paper7IntroStrictNeighbors

theorem deleted_component_degree_restore_explicit
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    (D : (vertexDeletedGraph G a).ConnectedComponent)
    [Fintype D.supp] [DecidableEq D.supp] [DecidableRel D.toSimpleGraph.Adj]
    (i : D.supp) :
    G.degree i.val.val = D.toSimpleGraph.degree i +
      if G.Adj i.val.val a then 1 else 0 := by
  have hd : D.toSimpleGraph.degree i = (vertexDeletedGraph G a).degree i.val := by
    rw [← D.toSimpleGraph.ncard_neighborSet i,
      ← (vertexDeletedGraph G a).ncard_neighborSet i.val]
    exact component_neighborSet_ncard_eq (vertexDeletedGraph G a) D i
  rw [hd]
  exact vertex_deleted_degree_restore G a i.val
#print axioms Paper7IntroNonattachmentFour.deleted_component_degree_restore_explicit

theorem deleted_degree_three_true_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    (D : (vertexDeletedGraph G a).ConnectedComponent)
    [Fintype D.supp] [DecidableEq D.supp] [DecidableRel D.toSimpleGraph.Adj]
    (hspec : ∀ t ∈ spec D.toSimpleGraph, t < 2)
    (x : D.supp) (hxa : G.Adj x.val.val a) (hx : D.toSimpleGraph.degree x = 3)
    (hbridge : ∀ j, G.Adj x.val.val j → G.IsBridge s(x.val.val, j)) :
    (∃ k, G.Adj x.val.val k ∧ G.degree k = 1 ∧ k ≠ a) ∧
      ∀ j, G.Adj x.val.val j → j ≠ a → G.degree j ≤ 2 := by
  have hno (j : V) (hxj : G.Adj x.val.val j) : ¬G.Adj j a := by
    exact fun hja => bridge_vertex_no_neighbor_triangle G x.val.val hbridge
      a j hxa hxj hja
  obtain ⟨k, hxk, hk⟩ := spectrum_lt_two_degree_three_has_leaf_neighbor
    D.toSimpleGraph D.connected_toSimpleGraph hspec x hx
  have hkrestore := deleted_component_degree_restore_explicit G a D k
  have hka : ¬G.Adj k.val.val a := hno k.val.val hxk
  rw [ite_eq_right hka, add_zero, hk] at hkrestore
  refine ⟨⟨k.val.val, hxk, hkrestore, k.val.property⟩, ?_⟩
  intro j hxj hja
  let j' : {q : V // q ≠ a} := ⟨j, hja⟩
  have hjD : j' ∈ D.supp := D.mem_supp_of_adj_mem_supp x.property hxj
  let z : D.supp := ⟨j', hjD⟩
  have hxz : D.toSimpleGraph.Adj x z := hxj
  have hz2 : D.toSimpleGraph.degree z ≤ 2 := by
    by_contra hz
    exact spectrum_lt_two_no_adjacent_high_degrees D.toSimpleGraph
      D.connected_toSimpleGraph hspec x z hxz (by omega) (by omega)
  have hr := deleted_component_degree_restore_explicit G a D z
  have hnot : ¬G.Adj z.val.val a := hno j hxj
  rw [ite_eq_right hnot, add_zero] at hr
  change G.degree j = D.toSimpleGraph.degree z at hr
  omega
#print axioms Paper7IntroNonattachmentFour.deleted_degree_three_true_neighbors

private theorem deleted_degree_four_true_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    (D : (vertexDeletedGraph G a).ConnectedComponent)
    [Fintype D.supp] [DecidableEq D.supp] [DecidableRel D.toSimpleGraph.Adj]
    (hspec : ∀ t ∈ spec D.toSimpleGraph, t < 2)
    (x : D.supp) (hxa : G.Adj x.val.val a) (hx : G.degree x.val.val = 4)
    (hbridge : ∀ j, G.Adj x.val.val j → G.IsBridge s(x.val.val, j)) :
    (∃ k, G.Adj x.val.val k ∧ G.degree k = 1 ∧ k ≠ a) ∧
      ∀ j, G.Adj x.val.val j → j ≠ a → G.degree j ≤ 2 := by
  have hr := deleted_component_degree_restore_explicit G a D x
  rw [ite_eq_left hxa] at hr
  have hx3 : D.toSimpleGraph.degree x = 3 := by omega
  exact deleted_degree_three_true_neighbors G a D hspec x hxa hx3 hbridge

private theorem strict_spectrum_change_instances
    {U : Type} (H : SimpleGraph U) (fi fj : Fintype U)
    (di dj : DecidableEq U) (ei ej : DecidableRel H.Adj)
    (h : ∀ t ∈ @spec U fi di H ei, t < 2) :
    ∀ t ∈ @spec U fj dj H ej, t < 2 := by
  cases Subsingleton.elim fi fj
  cases Subsingleton.elim di dj
  cases Subsingleton.elim ei ej
  exact h

private theorem deleted_degree_four_true_neighbors_induce
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    (D : (vertexDeletedGraph G a).ConnectedComponent)
    (hspec : ∀ t ∈ spec ((vertexDeletedGraph G a).induce D.supp), t < 2)
    (x : D.supp) (hxa : G.Adj x.val.val a) (hx : G.degree x.val.val = 4)
    (hbridge : ∀ j, G.Adj x.val.val j → G.IsBridge s(x.val.val, j)) :
    (∃ k, G.Adj x.val.val k ∧ G.degree k = 1 ∧ k ≠ a) ∧
      ∀ j, G.Adj x.val.val j → j ≠ a → G.degree j ≤ 2 := by
  have hfinite : Finite D.supp :=
    Finite.of_injective (fun i : D.supp => i.val.val) (by
      intro i j hij
      exact Subtype.ext (Subtype.ext hij))
  let fD : Fintype D.supp := @Fintype.ofFinite D.supp hfinite
  let dD : DecidableEq D.supp := Classical.decEq D.supp
  let eD : DecidableRel ((vertexDeletedGraph G a).induce D.supp).Adj :=
    fun _ _ => Classical.propDecidable _
  have hspecD : ∀ t ∈ @spec D.supp fD dD
      ((vertexDeletedGraph G a).induce D.supp) eD, t < 2 :=
    strict_spectrum_change_instances ((vertexDeletedGraph G a).induce D.supp)
      _ fD _ dD _ eD hspec
  have hspecT : ∀ t ∈ @spec D.supp fD dD D.toSimpleGraph eD, t < 2 := by
    simpa only [SimpleGraph.ConnectedComponent.toSimpleGraph] using hspecD
  exact @deleted_degree_four_true_neighbors V _ _ G _ a D fD dD eD
    hspecT x hxa hx hbridge

theorem intro21_even_attachment_degree_four_neighbor_structure
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4) :
    (∃ k, G.Adj x.val.val k ∧ G.degree k = 1 ∧ k ≠ a.val.val) ∧
      ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j ≤ 2 := by
  let u : {q : V // q ≠ a.val.val} := ⟨x.val.val, hxa.ne⟩
  obtain ⟨D, huD⟩ : ∃ D : (vertexDeletedGraph G a.val.val).ConnectedComponent,
      u ∈ D.supp := ⟨(vertexDeletedGraph G a.val.val).connectedComponentMk u, rfl⟩
  have hp := intro21_even_attachment_residual_positive_and_degree_bound
    G b hG hI hn hb r w hw hlen C a.val a.property c hac D u
    huD x.val.property x.property
  have hspec : ∀ t ∈ spec ((vertexDeletedGraph G a.val.val).induce D.supp), t < 2 :=
    deleted_component_spectrum_lt_two_of_complement_Ngt_positive G hG.1
      (intro21_even_Ngt_two_le_one G b hG hI hn hb) a.val.val D hp.1
  have hbridge : ∀ j, G.Adj x.val.val j → G.IsBridge s(x.val.val, j) := by
    intro j hxj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen
      x.val.val j x.val.property hxj
  exact deleted_degree_four_true_neighbors_induce G a.val.val D hspec ⟨u, huD⟩ hxa hx hbridge
#print axioms Paper7IntroNonattachmentFour.intro21_even_attachment_degree_four_neighbor_structure

end Paper7IntroNonattachmentFour
