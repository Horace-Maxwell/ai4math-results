import Research.TaskV.Stanley.AnchorSides
import Research.TaskV.Stanley.StarCore

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem terminal_in_cut (hG : G.IsTree) {s : Finset V} (cut : connectedCut G s) :
    ∃ a ∈ s, ∃! b, G.Adj a b := by
  classical
  let S := (s : Set V)
  obtain ⟨u⟩ := cut.1.nonempty
  obtain ⟨v⟩ := cut.2.nonempty
  obtain ⟨a,ha,b,hb,hab⟩ := connected_crossing (s:=S) hG.connected.preconnected u.property v.property
  have cross {p q : V} (hp : p ∈ s) (hq : q ∉ s) (pq : G.Adj p q) :
      p=a ∧ q=b := crossing_edge_unique (s:=S) hG.isAcyclic hab ha hb pq hp hq
        cut.1.preconnected cut.2.preconnected
  by_cases ns : Nontrivial S
  · let := ns
    have tG : (G.induce S).IsTree := ⟨cut.1,hG.isAcyclic.induce S⟩
    obtain ⟨i,j,ne,hi,hj⟩ := tG.exists_ne_and_degree_eq_one
    have one (w : S) (hw : w.val ≠ a) (deg : (G.induce S).degree w = 1) :
        ∃! y, G.Adj w.val y := by
      obtain ⟨k,hk,hu⟩ := (G.induce S).degree_eq_one_iff_existsUnique_adj.mp deg
      refine ⟨k.val,hk,?_⟩
      intro y hy
      by_cases ins : y ∈ s
      · exact congrArg Subtype.val (hu ⟨y,ins⟩ hy)
      · exact (hw (cross w.property ins hy).1).elim
    by_cases e : i.val = a
    · exact ⟨j.val,j.property,one j (fun f => ne (Subtype.ext (e.trans f.symm))) hj⟩
    · exact ⟨i.val,i.property,one i e hi⟩
  · let : Subsingleton S := not_nontrivial_iff_subsingleton.mp ns
    refine ⟨a,ha,b,hab,?_⟩
    intro y hy
    by_cases h : y ∈ s
    · exact (hy.ne (congrArg Subtype.val (Subsingleton.elim (⟨a,ha⟩ : S) ⟨y,h⟩))).elim
    · exact (cross ha h hy).2

theorem core_terminal_iff_count {n : ℕ} {J : SimpleGraph (Fin n)} (v : ↥(core J)) :
    (∃! w, (coreGraph J).Adj v w) ↔ ((neighbors J v) ∩ core J).card = 1 := by
  classical
  constructor
  · rintro ⟨w,hw,hu⟩
    apply card_eq_one.mpr
    refine ⟨w.val,?_⟩
    ext x
    constructor
    · intro h
      have hx := mem_inter.mp h
      exact mem_singleton.mpr (congrArg Subtype.val
        (hu ⟨x,hx.2⟩ (show J.Adj v x from mem_stanleyNeighbors.mp hx.1)))
    · rintro h
      have e := mem_singleton.mp h
      subst x
      exact mem_inter.mpr ⟨mem_stanleyNeighbors.mpr hw,w.property⟩
  · intro h
    obtain ⟨y,e⟩ := card_eq_one.mp h
    have hy : y ∈ (neighbors J v) ∩ core J := e ▸ mem_singleton_self y
    refine ⟨⟨y,(mem_inter.mp hy).2⟩,mem_stanleyNeighbors.mp (mem_inter.mp hy).1,?_⟩
    intro x hx
    apply Subtype.ext
    apply mem_singleton.mp
    rw [← e]
    exact mem_inter.mpr ⟨mem_stanleyNeighbors.mpr hx,x.property⟩

end
end StanleyContinuation
