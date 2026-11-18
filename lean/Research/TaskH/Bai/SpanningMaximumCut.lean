import Research.TaskH.Bai.SpanningCutBasic

/-! Finite maximization, single-vertex and actual-component flips, without cut oracles. -/
set_option autoImplicit false
universe u
namespace TaskH.Bai
open SimpleGraph Finset
variable {V : Type u}

/-- Finite maximization over all Boolean functions on the original vertex carrier. -/
theorem exists_maximum_cut_color (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] :
    ∃ c : V → Bool, ∀ d : V → Bool,
      (spanningCut G d).edgeFinset.card ≤ (spanningCut G c).edgeFinset.card := by
  classical
  obtain ⟨c, _, hc⟩ := (Finset.univ : Finset (V → Bool)).exists_max_image
    (fun c => (spanningCut G c).edgeFinset.card) (by simp)
  exact ⟨c, fun d => hc d (Finset.mem_univ d)⟩

/-- Maximal edge count forces the actual half-degree inequality at every vertex. -/
theorem maximum_cut_half_degree (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (c : V → Bool)
    (hmax : ∀ d : V → Bool,
      (spanningCut G d).edgeFinset.card ≤ (spanningCut G c).edgeFinset.card) :
    ∀ v : V, G.degree v ≤ 2 * (spanningCut G c).degree v := by
  classical
  intro v
  let d : V → Bool := cutFlip c {v}
  have hdeleted_sets := congrArg (fun J : SimpleGraph V => J.edgeSet.ncard)
    (singleton_flip_delete_incidence G c v)
  have hdelete_new := SimpleGraph.card_edgeFinset_deleteIncidenceSet (spanningCut G d) v
  have hdelete_old := SimpleGraph.card_edgeFinset_deleteIncidenceSet (spanningCut G c) v
  simp only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at hdelete_new hdelete_old
  have hdeleted : (spanningCut G d).edgeSet.ncard - (spanningCut G d).degree v =
      (spanningCut G c).edgeSet.ncard - (spanningCut G c).degree v := by
    calc
      (spanningCut G d).edgeSet.ncard - (spanningCut G d).degree v =
          ((spanningCut G d).deleteIncidenceSet v).edgeSet.ncard := hdelete_new.symm
      _ = ((spanningCut G c).deleteIncidenceSet v).edgeSet.ncard := hdeleted_sets
      _ = (spanningCut G c).edgeSet.ncard - (spanningCut G c).degree v := hdelete_old
  have he := hmax d
  have hdegree_old := (spanningCut G c).degree_le_card_edgeFinset (v := v)
  have hdegree_new := (spanningCut G d).degree_le_card_edgeFinset (v := v)
  simp only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at he hdegree_old hdegree_new
  have hlocal : (spanningCut G d).degree v ≤ (spanningCut G c).degree v := by
    omega
  have hsub : (spanningCut G c).neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr
      (((spanningCut G c).mem_neighborFinset v w).mp hw).1
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  rw [← singleton_flip_neighborFinset G c v] at hpart
  change (spanningCut G d).degree v + (spanningCut G c).degree v = G.degree v at hpart
  omega

/-- Flipping the actual reachable component proves connectedness from original connectedness. -/
theorem maximum_cut_connected (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (c : V → Bool)
    (hmax : ∀ d : V → Bool,
      (spanningCut G d).edgeFinset.card ≤ (spanningCut G c).edgeFinset.card)
    (hG : G.Connected) : (spanningCut G c).Connected := by
  classical
  refine { preconnected := ?_, nonempty := hG.nonempty }
  intro a b
  by_contra hn
  let S : Set V := {v | (spanningCut G c).Reachable a v}
  have ha : a ∈ S := SimpleGraph.Reachable.refl a
  have hb : b ∉ S := hn
  obtain ⟨p⟩ := hG a b
  obtain ⟨x, hx, y, hy, hxy⟩ := cut_walk_crossing G S p ha hb
  have hclosed : ∀ ⦃u v : V⦄, (spanningCut G c).Adj u v → (u ∈ S ↔ v ∈ S) := by
    intro u v huv
    constructor
    · intro hu
      exact (show (spanningCut G c).Reachable a u from hu).trans huv.reachable
    · intro hv
      exact (show (spanningCut G c).Reachable a v from hv).trans huv.symm.reachable
  have hnot : ¬(spanningCut G c).Adj x y := by
    intro h
    exact hy ((hclosed h).mp hx)
  have hle := cut_flip_le_of_edge_closed G c S hclosed
  have hnew := cut_flip_adds_boundary_edge G c S hx hy hxy hnot
  have hsubset : (spanningCut G c).edgeFinset ⊆
      (spanningCut G (cutFlip c S)).edgeFinset := SimpleGraph.edgeFinset_mono hle
  have hedge_new : s(x, y) ∈ (spanningCut G (cutFlip c S)).edgeFinset := by
    exact SimpleGraph.mem_edgeFinset.mpr hnew
  have hedge_old : s(x, y) ∉ (spanningCut G c).edgeFinset := by
    intro he
    exact hnot (SimpleGraph.mem_edgeFinset.mp he)
  have hproper : (spanningCut G c).edgeFinset ⊂
      (spanningCut G (cutFlip c S)).edgeFinset := by
    exact (Finset.ssubset_iff_of_subset hsubset).mpr ⟨s(x, y), hedge_new, hedge_old⟩
  have hlt := Finset.card_lt_card hproper
  have hbound := hmax (cutFlip c S)
  omega

/-- Complete original finite-graph existence: no chosen maximum cut is an input. -/
theorem exists_spanning_bipartite_half_degree (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] :
    ∃ c : V → Bool, spanningCut G c ≤ G ∧ (spanningCut G c).IsBipartite ∧
      (∀ v : V, G.degree v ≤ 2 * (spanningCut G c).degree v) ∧
      (G.Connected → (spanningCut G c).Connected) := by
  obtain ⟨c, hc⟩ := exists_maximum_cut_color G
  exact ⟨c, spanningCut_le G c, spanningCut_bipartite G c,
    maximum_cut_half_degree G c hc, maximum_cut_connected G c hc⟩

/-- The integral odd minimum-degree bound transports on the same original V. -/
theorem exists_spanning_bipartite_minimum_degree (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (q : ℕ) (hq : 1 ≤ q)
    (hdeg : ∀ v : V, 2 * q - 1 ≤ G.degree v) :
    ∃ c : V → Bool, spanningCut G c ≤ G ∧ (spanningCut G c).IsBipartite ∧
      (∀ v : V, q ≤ (spanningCut G c).degree v) ∧
      (G.Connected → (spanningCut G c).Connected) := by
  obtain ⟨c, hle, hbi, hhalf, hconn⟩ := exists_spanning_bipartite_half_degree G
  refine ⟨c, hle, hbi, ?_, hconn⟩
  intro v
  have hg := hdeg v
  have hh := hhalf v
  omega

#print axioms exists_maximum_cut_color
#print axioms maximum_cut_half_degree
#print axioms maximum_cut_connected
#print axioms exists_spanning_bipartite_half_degree
#print axioms exists_spanning_bipartite_minimum_degree
end TaskH.Bai
