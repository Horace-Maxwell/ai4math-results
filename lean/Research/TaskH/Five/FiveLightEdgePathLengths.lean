import Research.TaskH.Five.FiveLightEdgePaths

/-! The ordinary noncommon neighbor color gives length at least six.
Only the separate missing-color argument may strengthen this to eight. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

noncomputable def lightDeletedEdgeVertexColoring {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) :
    (G.induce {x | x ≠ u}).Coloring (Fin 5) := by
  classical
  refine SimpleGraph.Coloring.mk (fun x => c x.val) ?_
  intro a b hab
  apply c.valid
  refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
  intro he
  have heq : s(a.val, b.val) = s(u, v) := Set.mem_singleton_iff.mp he
  rcases Sym2.eq_iff.mp heq with ⟨ha, _⟩ | ⟨_, hb⟩
  · exact a.property ha
  · exact b.property hb

def lightClosedDeletedEdgePath {u v : V} (huv : G.Adj u v)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) : G.Walk v v :=
  .cons huv.symm (p.mapLe (G.deleteEdges_le {s(u, v)}))

theorem lightClosedDeletedEdgePath_isCycle {u v : V} (huv : G.Adj u v)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (hp : p.IsPath) :
    (lightClosedDeletedEdgePath huv p).IsCycle := by
  rw [lightClosedDeletedEdgePath, Walk.cons_isCycle_iff]
  refine ⟨hp.mapLe _, ?_⟩
  intro he
  rw [Walk.edges_mapLe_eq_edges] at he
  have hd := (SimpleGraph.deleteEdges_adj.mp (p.adj_of_mem_edges he)).2
  exact hd (by simp [Sym2.eq_swap])

theorem lightClosedDeletedEdgePath_length {u v : V} (huv : G.Adj u v)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) :
    (lightClosedDeletedEdgePath huv p).length = p.length + 1 := by
  simp [lightClosedDeletedEdgePath, Walk.length_cons]

theorem lightClosedDeletedEdgePath_mem {u v : V} (huv : G.Adj u v)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (n : ℕ) (hn : n ≤ p.length) :
    p.getVert n ∈ (lightClosedDeletedEdgePath huv p).support := by
  rw [lightClosedDeletedEdgePath, Walk.support_cons, Walk.support_mapLe_eq_support]
  exact List.mem_cons_of_mem _
    (Walk.mem_support_iff_exists_getVert.mpr ⟨n, rfl, hn⟩)

theorem rainbow_forbids_two_color_path_four (hr : RainbowFiveCycles G)
    {u v : V} (huv : G.Adj u v)
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c u) b)) : p.length ≠ 4 := by
  intro hl
  have h1u : p.getVert 1 ≠ u := by
    intro he
    have hn := (hp.getVert_eq_start_iff (by omega : 1 ≤ p.length)).mp he
    omega
  have h3u : p.getVert 3 ≠ u := by
    intro he
    have hn := (hp.getVert_eq_start_iff (by omega : 3 ≤ p.length)).mp he
    omega
  let d := lightDeletedEdgeVertexColoring c
  let q := lightClosedDeletedEdgePath huv p
  have hq : q.IsCycle := lightClosedDeletedEdgePath_isCycle huv p hp
  have hql : q.length = 5 := by
    rw [lightClosedDeletedEdgePath_length, hl]
  have hc1 : c (p.getVert 1) = b := by
    simpa using light_swap_color_at p c b hf 1 (by omega)
  have hc3 : c (p.getVert 3) = b := by
    simpa using light_swap_color_at p c b hf 3 (by omega)
  have heq := hr u d q hq hql ⟨p.getVert 1, h1u⟩ ⟨p.getVert 3, h3u⟩
    (lightClosedDeletedEdgePath_mem huv p 1 (by omega))
    (lightClosedDeletedEdgePath_mem huv p 3 (by omega))
    (hc1.trans hc3.symm)
  have hv : p.getVert 1 = p.getVert 3 := congrArg Subtype.val heq
  have hn := hp.getVert_injOn (by change 1 ≤ p.length; omega)
    (by change 3 ≤ p.length; omega) hv
  omega

theorem noncommon_forbids_two_color_path_two {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (hno : ∀ w : V, G.Adj u w → G.Adj v w → c w ≠ b)
    (p : (G.deleteEdges {s(u, v)}).Walk u v)
    (hf : Follows p c (Equiv.swap (c u) b)) : p.length ≠ 2 := by
  intro hl
  have h0 := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
  have h1 := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
  have hend : p.getVert 2 = v := by simpa only [hl] using p.getVert_length
  rw [Walk.getVert_zero] at h0
  rw [hend] at h1
  apply hno (p.getVert 1) (SimpleGraph.deleteEdges_adj.mp h0).1
    (SimpleGraph.deleteEdges_adj.mp h1).1.symm
  simpa using light_swap_color_at p c b hf 1 (by omega)

theorem critical_exists_long_noncommon_two_color_path
    (hcrit : IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    {u v : V} (huv : G.Adj u v)
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5) (hb : b ≠ c u)
    (hno : ∀ w : V, G.Adj u w → G.Adj v w → c w ≠ b) :
    ∃ p : (G.deleteEdges {s(u, v)}).Walk u v,
      p.IsPath ∧ Follows p c (Equiv.swap (c u) b) ∧
      (∀ q : (G.deleteEdges {s(u, v)}).Walk u v,
        Follows q c (Equiv.swap (c u) b) → p.length ≤ q.length) ∧
      6 ≤ p.length ∧ p.length % 2 = 0 := by
  obtain ⟨p, hp, hf, hmin, hpos, heven⟩ :=
    critical_exists_shortest_two_color_path hcrit huv c b hb
  have h2 := noncommon_forbids_two_color_path_two c b hno p hf
  have h4 := rainbow_forbids_two_color_path_four hr huv c b p hp hf
  exact ⟨p, hp, hf, hmin, by omega, heven⟩

end TaskH.Five

#print axioms TaskH.Five.lightDeletedEdgeVertexColoring
#print axioms TaskH.Five.lightClosedDeletedEdgePath
#print axioms TaskH.Five.lightClosedDeletedEdgePath_isCycle
#print axioms TaskH.Five.lightClosedDeletedEdgePath_length
#print axioms TaskH.Five.lightClosedDeletedEdgePath_mem
#print axioms TaskH.Five.rainbow_forbids_two_color_path_four
#print axioms TaskH.Five.noncommon_forbids_two_color_path_two
#print axioms TaskH.Five.critical_exists_long_noncommon_two_color_path
