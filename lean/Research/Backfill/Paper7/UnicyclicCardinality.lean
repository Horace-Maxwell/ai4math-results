import Research.Backfill.Paper7.UnicyclicBasic
import Mathlib

/-! Uncompiled generic unicyclic cardinality bridge. The parent generic
helpers are themselves uncompiled; no main theorem acceptance is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Unicyclic
open SimpleGraph BackfillPaper7.Challenge

theorem unicyclic_delete_cycle_edge_isTree {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {b : ℕ} (hG : IsUnicyclicWithCycle G b)
    {s : Finset (Sym2 V)} (hs : s ∈ cycleEdgeSets G b)
    {e : Sym2 V} (he : e ∈ s) : (G.deleteEdges {e}).IsTree := by
  obtain ⟨u, c, hc, hlen, hcs⟩ := hs
  have hec : e ∈ c.edges := List.mem_toFinset.mp (hcs.symm ▸ he)
  have hn : ¬ G.IsBridge e := fun h => h.notMem_edges_of_isCycle hc hec
  refine ⟨hG.1.preconnected.connected_deleteEdges_of_not_isBridge hn, ?_⟩
  intro v w hw
  let wl := w.mapLe (G.deleteEdges_le {e})
  have hwl : wl.IsCycle := hw.mapLe (G.deleteEdges_le {e})
  obtain ⟨t, _ht, huniq⟩ := hG.2
  have hsets : wl.edges.toFinset = s :=
    (huniq wl.length wl.edges.toFinset ⟨v, wl, hwl, rfl, rfl⟩).trans
      (huniq b s ⟨u, c, hc, hlen, hcs⟩).symm
  have hewl : e ∈ wl.edges := List.mem_toFinset.mp (hsets.symm ▸ he)
  have hedges : wl.edges = w.edges := by
    simp only [wl, Walk.edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq]
  rw [hedges] at hewl
  have hdel := w.edges_subset_edgeSet hewl
  rw [SimpleGraph.edgeSet_deleteEdges] at hdel
  exact hdel.2 rfl
#print axioms Paper7Unicyclic.unicyclic_delete_cycle_edge_isTree

theorem unicyclic_card_edges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) : G.edgeFinset.card = Fintype.card V := by
  classical
  obtain ⟨s, hs, _⟩ := hG.2
  have hspos : 0 < s.card := by
    rw [cycleEdgeSet_card hs]
    exact lt_of_lt_of_le (by decide : 0 < 3) (unicyclic_three_le hG)
  obtain ⟨e, he⟩ := Finset.card_pos.mp hspos
  have ht := (unicyclic_delete_cycle_edge_isTree hG hs he).card_edgeFinset
  have heG : e ∈ G.edgeFinset := by
    obtain ⟨u, c, _hc, _hlen, hcs⟩ := hs
    have hec : e ∈ c.edges := List.mem_toFinset.mp (hcs.symm ▸ he)
    simpa only [SimpleGraph.mem_edgeFinset] using c.edges_subset_edgeSet hec
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨e, heG⟩
  have hdel : (G.deleteEdges ({e} : Set (Sym2 V))).edgeFinset =
      G.edgeFinset.erase e := by
    ext a
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase]
    exact and_comm
  rw [hdel, Finset.card_erase_of_mem heG] at ht
  omega
#print axioms Paper7Unicyclic.unicyclic_card_edges
end Paper7Unicyclic
