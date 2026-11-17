import Research.TaskH.Five.FiveLightEdgeColorBudget
import Research.TaskH.Five.FiveLightEdgeMissingColor

/-! Actual color-class lower bounds supplied by middle vertices of the
shortest paths. All neighbor sets are those of the original graph. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem light_fiber_union_bound [DecidableEq V]
    (S T : Finset V) (c : V → Fin 5) (a : Fin 5) :
    (lightColorFiber S c a).card + (lightColorFiber T c a).card ≤
      (lightColorFiber Finset.univ c a).card +
        (lightColorFiber (S ∩ T) c a).card := by
  classical
  have hinter : lightColorFiber S c a ∩ lightColorFiber T c a =
      lightColorFiber (S ∩ T) c a := by
    ext x
    simp [lightColorFiber, and_assoc, and_left_comm, and_comm]
  have hsub : lightColorFiber S c a ∪ lightColorFiber T c a ⊆
      lightColorFiber Finset.univ c a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hc := Finset.card_union_add_card_inter (lightColorFiber S c a)
    (lightColorFiber T c a)
  rw [hinter] at hc
  have hs := Finset.card_le_card hsub
  omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem light_middle_not_neighbors {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (hb : b ≠ c u) (he : c u = c v)
    (p : (G.deleteEdges {s(u, v)}).Walk u v)
    (hf : Follows p c (Equiv.swap (c u) b))
    (hmin : ∀ q : (G.deleteEdges {s(u, v)}).Walk u v,
      Follows q c (Equiv.swap (c u) b) → p.length ≤ q.length)
    (n : ℕ) (hn : n ≤ p.length) (hc : c (p.getVert n) = b)
    (hnfirst : n ≠ 1) (hnlast : n + 1 ≠ p.length) :
    ¬ G.Adj u (p.getVert n) ∧ ¬ G.Adj v (p.getVert n) := by
  classical
  have hnu : p.getVert n ≠ u := by
    intro hu
    exact hb (hc.symm.trans (congrArg c hu))
  have hnv : p.getVert n ≠ v := by
    intro hv
    exact hb (hc.symm.trans ((congrArg c hv).trans he.symm))
  constructor
  · intro ha
    have hd : (G.deleteEdges {s(u, v)}).Adj u (p.getVert n) := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨ha, ?_⟩
      intro hm
      exact hnv (Sym2.congr_right.mp (Set.mem_singleton_iff.mp hm))
    exact hnfirst (light_shortest_neighbor_at_start p c b hb hf hmin n hn hc hd)
  · intro ha
    have hd : (G.deleteEdges {s(u, v)}).Adj (p.getVert n) v := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨ha.symm, ?_⟩
      intro hm
      exact hnu (Sym2.congr_left.mp (Set.mem_singleton_iff.mp hm))
    exact hnlast (light_shortest_neighbor_at_end p c b hb he hf hmin n hn hc hd)

theorem light_noncommon_neighbor_fibers_disjoint {u v : V}
    (c : V → Fin 5) (b : Fin 5)
    (hno : ∀ w : V, G.Adj u w → G.Adj v w → c w ≠ b) :
    Disjoint (lightColorFiber (G.neighborFinset u) c b)
      (lightColorFiber (G.neighborFinset v) c b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hu hv
  have huc := Finset.mem_filter.mp hu
  have hvc := Finset.mem_filter.mp hv
  exact hno w ((G.mem_neighborFinset u w).mp huc.1)
    ((G.mem_neighborFinset v w).mp hvc.1) huc.2

theorem light_path_six_class_bound {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (hb : b ≠ c u) (he : c u = c v)
    (hno : ∀ w : V, G.Adj u w → G.Adj v w → c w ≠ b)
    (p : (G.deleteEdges {s(u, v)}).Walk u v)
    (hf : Follows p c (Equiv.swap (c u) b))
    (hmin : ∀ q : (G.deleteEdges {s(u, v)}).Walk u v,
      Follows q c (Equiv.swap (c u) b) → p.length ≤ q.length)
    (hlen : 6 ≤ p.length) :
    (lightColorFiber (G.neighborFinset u) c b).card +
      (lightColorFiber (G.neighborFinset v) c b).card + 1 ≤
        (lightColorFiber Finset.univ c b).card := by
  classical
  let A := lightColorFiber (G.neighborFinset u) c b
  let B := lightColorFiber (G.neighborFinset v) c b
  have hc : c (p.getVert 3) = b := by
    simpa using light_swap_color_at p c b hf 3 (by omega)
  have hn := light_middle_not_neighbors c b hb he p hf hmin 3 (by omega) hc
    (by decide) (by omega)
  have hnot : p.getVert 3 ∉ A ∪ B := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hn.1 ((G.mem_neighborFinset u (p.getVert 3)).mp (Finset.mem_filter.mp hm).1)
    · exact hn.2 ((G.mem_neighborFinset v (p.getVert 3)).mp (Finset.mem_filter.mp hm).1)
  have hsub : insert (p.getVert 3) (A ∪ B) ⊆ lightColorFiber Finset.univ c b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot,
    Finset.card_union_of_disjoint (light_noncommon_neighbor_fibers_disjoint c b hno)] at hh
  exact hh

theorem light_path_eight_nonbase_class_bound {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (hb : b ≠ c u) (he : c u = c v)
    (hno : ∀ w : V, G.Adj u w → G.Adj v w → c w ≠ b)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c u) b))
    (hmin : ∀ q : (G.deleteEdges {s(u, v)}).Walk u v,
      Follows q c (Equiv.swap (c u) b) → p.length ≤ q.length)
    (hlen : 8 ≤ p.length) :
    (lightColorFiber (G.neighborFinset u) c b).card +
      (lightColorFiber (G.neighborFinset v) c b).card + 2 ≤
        (lightColorFiber Finset.univ c b).card := by
  classical
  let A := lightColorFiber (G.neighborFinset u) c b
  let B := lightColorFiber (G.neighborFinset v) c b
  have hc3 : c (p.getVert 3) = b := by
    simpa using light_swap_color_at p c b hf 3 (by omega)
  have hc5 : c (p.getVert 5) = b := by
    simpa using light_swap_color_at p c b hf 5 (by omega)
  have hn3 := light_middle_not_neighbors c b hb he p hf hmin 3 (by omega) hc3
    (by decide) (by omega)
  have hn5 := light_middle_not_neighbors c b hb he p hf hmin 5 (by omega) hc5
    (by decide) (by omega)
  have hnot3 : p.getVert 3 ∉ A ∪ B := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hn3.1 ((G.mem_neighborFinset u (p.getVert 3)).mp (Finset.mem_filter.mp hm).1)
    · exact hn3.2 ((G.mem_neighborFinset v (p.getVert 3)).mp (Finset.mem_filter.mp hm).1)
  have hnot5 : p.getVert 5 ∉ A ∪ B := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hn5.1 ((G.mem_neighborFinset u (p.getVert 5)).mp (Finset.mem_filter.mp hm).1)
    · exact hn5.2 ((G.mem_neighborFinset v (p.getVert 5)).mp (Finset.mem_filter.mp hm).1)
  have hne : p.getVert 3 ≠ p.getVert 5 := by
    intro heq
    have hi := hp.getVert_injOn (by change 3 ≤ p.length; omega)
      (by change 5 ≤ p.length; omega) heq
    omega
  have hnot35 : p.getVert 3 ∉ insert (p.getVert 5) (A ∪ B) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hnot3⟩
  have hsub : insert (p.getVert 3) (insert (p.getVert 5) (A ∪ B)) ⊆
      lightColorFiber Finset.univ c b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc3⟩
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc5⟩
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot35, Finset.card_insert_of_notMem hnot5,
    Finset.card_union_of_disjoint (light_noncommon_neighbor_fibers_disjoint c b hno)] at hh
  simpa only [Nat.add_assoc] using hh

omit [DecidableRel G.Adj] in
theorem light_path_eight_base_class_bound {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c u) b)) (hlen : 8 ≤ p.length) :
    5 ≤ (lightColorFiber Finset.univ c (c u)).card := by
  classical
  let z : Fin 5 → V := fun j => p.getVert (2 * j.val)
  have hz : Function.Injective z := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have he := hp.getVert_injOn (by change 2 * i.val ≤ p.length; omega)
      (by change 2 * j.val ≤ p.length; omega) hij
    apply Fin.ext
    omega
  have hsub : (Finset.univ.image z) ⊆ lightColorFiber Finset.univ c (c u) := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    have hj := j.isLt
    have hc := light_swap_color_at p c b hf (2 * j.val) (by omega)
    have heven : (2 * j.val) % 2 = 0 := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [ite_eq_left heven] using hc⟩
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hz, Finset.card_univ,
    Fintype.card_fin] using hh

end TaskH.Five

#print axioms TaskH.Five.light_fiber_union_bound
#print axioms TaskH.Five.light_middle_not_neighbors
#print axioms TaskH.Five.light_noncommon_neighbor_fibers_disjoint
#print axioms TaskH.Five.light_path_six_class_bound
#print axioms TaskH.Five.light_path_eight_nonbase_class_bound
#print axioms TaskH.Five.light_path_eight_base_class_bound
