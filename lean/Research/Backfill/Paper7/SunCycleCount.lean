import Research.Backfill.Paper7.SunCycleSupport
import Research.Backfill.Paper7.CycleEdgeMinimality
import Research.Backfill.Paper7.OddGirthWalkBridge

/-! Unique simple-cycle edge set of the actual generalized sun graph, with
arbitrary arm data. No unicyclicity or setup contract is assumed. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

namespace Paper7SunMoments

def sunCycleHom (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    SimpleGraph.cycleGraph b →g sunGraph b L where
  toFun := Sum.inl
  map_rel' := fun {i j} h => (Paper7Cleared.sun_cycle_adj_iff b L hb i j).mpr h

theorem cycleGraph_adj_mem_cycle_edges (n : ℕ) (i j : Fin (n + 3))
    (hij : (SimpleGraph.cycleGraph (n + 3)).Adj i j) :
    s(i, j) ∈ (SimpleGraph.cycleGraph.cycle n).edges := by
  let c := SimpleGraph.cycleGraph.cycle n
  have hc : c.IsCycle := SimpleGraph.cycleGraph.isCycle_cycle
  have hh : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, by simp [c]⟩
  have hg : (SimpleGraph.cycleGraph (n + 3)).IsCycles := by
    intro v _
    rw [SimpleGraph.ncard_neighborSet, SimpleGraph.cycleGraph_degree_three_le]
  exact Walk.adj_toSubgraph_iff_mem_edges.mp
    ((hc.adj_toSubgraph_iff_of_isCycles hg
      (c.mem_verts_toSubgraph.mpr (hh.mem_support i)) j).mpr hij)

theorem sun_reference_cycle (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    ∃ u : SunV b L, ∃ c : (sunGraph b L).Walk u u,
      c.IsCycle ∧ c.length = b ∧
        ∀ i j : Fin b, (sunGraph b L).Adj (Sum.inl i) (Sum.inl j) →
          s(Sum.inl i, Sum.inl j) ∈ c.edges := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  let f := sunCycleHom (n + 3) L hb
  let c := (SimpleGraph.cycleGraph.cycle n).map f
  have hf : Function.Injective f := Sum.inl_injective
  refine ⟨Sum.inl 0, c, SimpleGraph.cycleGraph.isCycle_cycle.map hf, ?_, ?_⟩
  · exact (Walk.length_map f (SimpleGraph.cycleGraph.cycle n)).trans
      SimpleGraph.cycleGraph.length_cycle
  · intro i j hij
    have he := cycleGraph_adj_mem_cycle_edges n i j
      ((Paper7Cleared.sun_cycle_adj_iff (n + 3) L hb i j).mp hij)
    change s(Sum.inl i, Sum.inl j) ∈ ((SimpleGraph.cycleGraph.cycle n).map f).edges
    rw [Walk.edges_map]
    exact List.mem_map.mpr ⟨s(i, j), he, rfl⟩

theorem sun_cycle_edgeFinset_subset_reference {b : ℕ} {L : Fin b → List ℕ}
    {u v : SunV b L} (w : (sunGraph b L).Walk u u) (hw : w.IsCycle)
    (c : (sunGraph b L).Walk v v)
    (hcovers : ∀ i j : Fin b, (sunGraph b L).Adj (Sum.inl i) (Sum.inl j) →
      s(Sum.inl i, Sum.inl j) ∈ c.edges) : w.edges.toFinset ⊆ c.edges.toFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hxy : w.toSubgraph.Adj x y :=
      Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp he)
    have hx : x ∈ w.support := w.mem_verts_toSubgraph.mp (w.toSubgraph.edge_vert hxy)
    have hy : y ∈ w.support := w.mem_verts_toSubgraph.mp (w.toSubgraph.edge_vert hxy.symm)
    obtain ⟨i, rfl⟩ := sun_cycle_support_root w hw x hx
    obtain ⟨j, rfl⟩ := sun_cycle_support_root w hw y hy
    exact List.mem_toFinset.mpr (hcovers i j (w.toSubgraph.adj_sub hxy))

theorem sun_cycle_unique_data (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    ∃ s : Finset (Sym2 (SunV b L)), s ∈ cycleEdgeSets (sunGraph b L) b ∧
      ∀ (ell : ℕ) (t : Finset (Sym2 (SunV b L))),
        t ∈ cycleEdgeSets (sunGraph b L) ell → ell = b ∧ t = s := by
  obtain ⟨u, c, hc, hclen, hcover⟩ := sun_reference_cycle b L hb
  refine ⟨c.edges.toFinset, ⟨u, c, hc, hclen, rfl⟩, ?_⟩
  intro ell t ht
  obtain ⟨v, w, hw, hwlen, hwt⟩ := ht
  have heq := Paper7Cycles.cycle_edgeFinset_eq_of_subset hw hc
    (sun_cycle_edgeFinset_subset_reference w hw c hcover)
  have hcard := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup hw.isTrail.edges_nodup,
    List.toFinset_card_of_nodup hc.isTrail.edges_nodup,
    Walk.length_edges, Walk.length_edges, hwlen, hclen] at hcard
  exact ⟨hcard, hwt.symm.trans heq⟩

theorem sun_cycleCount (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (ell : ℕ) :
    cycleCount (sunGraph b L) ell = if ell = b then 1 else 0 := by
  obtain ⟨s, hs, huniq⟩ := sun_cycle_unique_data b L hb
  by_cases hell : ell = b
  · subst ell
    have hset : cycleEdgeSets (sunGraph b L) b = {s} := by
      ext t
      constructor
      · intro ht
        exact Set.mem_singleton_iff.mpr (huniq b t ht).2
      · rintro rfl
        exact hs
    simp only [cycleCount, hset, Set.ncard_singleton, ite_true]
  · have hset : cycleEdgeSets (sunGraph b L) ell = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hell (huniq ell t ht).1
    simp only [cycleCount, hset, Set.ncard_empty, ite_eq_right hell]

theorem sun_isOddGirth (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    IsOddGirth (sunGraph b L) b := by
  obtain ⟨s, hs, huniq⟩ := sun_cycle_unique_data b L hb
  refine ⟨hodd, ?_, ?_⟩
  · obtain ⟨u, c, hc, hclen, _⟩ := hs
    exact ⟨u, c, hc, hclen⟩
  · intro u c hc _
    exact le_of_eq ((huniq c.length c.edges.toFinset ⟨u, c, hc, rfl, rfl⟩).1.symm)

theorem sun_no_short_odd_closedWalk {b : ℕ} {L : Fin b → List ℕ} (hb : 3 ≤ b)
    {u : SunV b L} (w : (sunGraph b L).Walk u u) (hodd : Odd w.length)
    (hlen : w.length < b) : False := by
  obtain ⟨s, _hs, huniq⟩ := sun_cycle_unique_data b L hb
  obtain ⟨v, c, hc, _hcodd, hcle, _hcedges⟩ :=
    Paper7OddWalk.exists_odd_cycle_length_le w hodd
  have hcb := (huniq c.length c.edges.toFinset ⟨v, c, hc, rfl, rfl⟩).1
  omega

end Paper7SunMoments

#print axioms Paper7SunMoments.sunCycleHom
#print axioms Paper7SunMoments.cycleGraph_adj_mem_cycle_edges
#print axioms Paper7SunMoments.sun_reference_cycle
#print axioms Paper7SunMoments.sun_cycle_edgeFinset_subset_reference
#print axioms Paper7SunMoments.sun_cycle_unique_data
#print axioms Paper7SunMoments.sun_cycleCount
#print axioms Paper7SunMoments.sun_isOddGirth
#print axioms Paper7SunMoments.sun_no_short_odd_closedWalk
