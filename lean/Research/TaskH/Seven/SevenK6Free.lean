import Research.TaskH.Seven.SevenK6CliqueSeparation
import Research.TaskH.Seven.SevenSingletonDegree

/-!
Choose one actual outside neighbor of each six-clique vertex. Unique
attachment labels and the actual path exclusions separate their closed
outside neighborhoods. The six neighborhoods each contain at least eight
vertices, so the graph has at least 54 vertices.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_clique_root_outside_nonempty (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q) (i : Fin 6) :
    (packingNeighborsIn G (sixCliqueSet q)ᶜ (q i)).Nonempty := by
  have hout := packingNeighborsIn_compl_lower (sixCliqueSet q) (q i) 8 5 (hdegree _)
    (six_clique_root_inside_card_le_five q hq i)
  apply Finset.card_pos.mp
  omega

noncomputable def sixCliqueChosenNeighbor (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q) (i : Fin 6) : V :=
  (six_clique_root_outside_nonempty hdegree q hq i).choose

theorem sixCliqueChosenNeighbor_mem (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q) (i : Fin 6) :
    sixCliqueChosenNeighbor hdegree q hq i ∈ packingNeighborsIn G (sixCliqueSet q)ᶜ (q i) :=
  (six_clique_root_outside_nonempty hdegree q hq i).choose_spec

theorem sixCliqueChosenNeighbor_outside (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q) (i : Fin 6) :
    sixCliqueChosenNeighbor hdegree q hq i ∉ sixCliqueSet q :=
  Finset.mem_compl.mp (Finset.mem_filter.mp (sixCliqueChosenNeighbor_mem hdegree q hq i)).1

theorem sixCliqueChosenNeighbor_adj (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q) (i : Fin 6) :
    G.Adj (q i) (sixCliqueChosenNeighbor hdegree q hq i) :=
  (Finset.mem_filter.mp (sixCliqueChosenNeighbor_mem hdegree q hq i)).2

omit [Fintype V] [DecidableRel G.Adj] in
theorem six_clique_attachment_root_unique (q : Fin 6 → V)
    (hout : ∀ x ∉ sixCliqueSet q, (sixCliqueHooks G q x).card ≤ 1)
    (x : V) (hx : x ∉ sixCliqueSet q) (i j : Fin 6)
    (hix : G.Adj (q i) x) (hjx : G.Adj (q j) x) : i = j := by
  classical
  have hmem : ∀ a : Fin 6, a ∈ sixCliqueHooks G q x ↔ G.Adj x (q a) := by
    intro a
    simp only [sixCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : i ∈ sixCliqueHooks G q x := (hmem i).mpr hix.symm
  have hj : j ∈ sixCliqueHooks G q x := (hmem j).mpr hjx.symm
  exact Finset.card_le_one.mp (hout x hx) i hi j hj

theorem sixCliqueChosenNeighbor_injective (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hout : ∀ x ∉ sixCliqueSet q, (sixCliqueHooks G q x).card ≤ 1) :
    Function.Injective (sixCliqueChosenNeighbor hdegree q hq) := by
  intro i j he
  apply six_clique_attachment_root_unique q hout
    (sixCliqueChosenNeighbor hdegree q hq i) (sixCliqueChosenNeighbor_outside hdegree q hq i) i j
    (sixCliqueChosenNeighbor_adj hdegree q hq i)
  rw [he]
  exact sixCliqueChosenNeighbor_adj hdegree q hq j

noncomputable def sixCliqueClosedOutside (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 6 → V) (x : V) : Finset V :=
  insert x (packingNeighborsIn G (sixCliqueSet q)ᶜ x)

theorem six_clique_closed_outside_subset (q : Fin 6 → V) (x : V)
    (hx : x ∉ sixCliqueSet q) : sixCliqueClosedOutside G q x ⊆ (sixCliqueSet q)ᶜ := by
  classical
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_compl.mpr hx
  · exact (Finset.mem_filter.mp hz).1

theorem eight_le_six_clique_closed_outside (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hout : ∀ x ∉ sixCliqueSet q, (sixCliqueHooks G q x).card ≤ 1)
    (x : V) (hx : x ∉ sixCliqueSet q) : 8 ≤ (sixCliqueClosedOutside G q x).card := by
  classical
  have hin : (packingNeighborsIn G (sixCliqueSet q) x).card ≤ 1 := by
    rw [six_clique_neighbors_card q hq x]
    exact hout x hx
  have h7 := packingNeighborsIn_compl_lower (sixCliqueSet q) x 8 1 (hdegree x) hin
  have hxN : x ∉ packingNeighborsIn G (sixCliqueSet q)ᶜ x := by
    intro hxN
    exact (Finset.mem_filter.mp hxN).2.ne rfl
  rw [sixCliqueClosedOutside, Finset.card_insert_of_notMem hxN]
  omega

theorem six_clique_chosen_closed_disjoint (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 9 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hout : ∀ x ∉ sixCliqueSet q, (sixCliqueHooks G q x).card ≤ 1)
    (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (sixCliqueClosedOutside G q (sixCliqueChosenNeighbor hdegree q hq i))
      (sixCliqueClosedOutside G q (sixCliqueChosenNeighbor hdegree q hq j)) := by
  classical
  let x := sixCliqueChosenNeighbor hdegree q hq i
  let x' := sixCliqueChosenNeighbor hdegree q hq j
  have hx : x ∉ sixCliqueSet q := sixCliqueChosenNeighbor_outside hdegree q hq i
  have hx' : x' ∉ sixCliqueSet q := sixCliqueChosenNeighbor_outside hdegree q hq j
  have hix : G.Adj (q i) x := sixCliqueChosenNeighbor_adj hdegree q hq i
  have hjx' : G.Adj (q j) x' := sixCliqueChosenNeighbor_adj hdegree q hq j
  have hxx' : x ≠ x' := (sixCliqueChosenNeighbor_injective hdegree q hq hout).ne hij
  have hno := critical_six_clique_no_cross_edge hcrit hr hn q hq hclique i j hij x x' hx hx' hix hjx'
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  rcases Finset.mem_insert.mp hzi with hzi | hzi
  · rcases Finset.mem_insert.mp hzj with hzj | hzj
    · exact hxx' (hzi.symm.trans hzj)
    · have hadj := (Finset.mem_filter.mp hzj).2
      rw [hzi] at hadj
      exact hno hadj.symm
  · rcases Finset.mem_insert.mp hzj with hzj | hzj
    · have hadj := (Finset.mem_filter.mp hzi).2
      rw [hzj] at hadj
      exact hno hadj
    · have hz : z ∉ sixCliqueSet q :=
        Finset.mem_compl.mp (Finset.mem_filter.mp hzi).1
      exact critical_six_clique_no_cross_common_neighbor hcrit hr hn q hq hclique
        i j hij x x' z hx hx' hz hxx' hix hjx'
        (Finset.mem_filter.mp hzi).2 (Finset.mem_filter.mp hzj).2

/-- This is a closed-neighborhood count in the actual graph, with the six
rows indexed by real selected neighbors of its six actual clique vertices. -/
theorem six_clique_closed_neighborhood_packing (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 9 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hout : ∀ x ∉ sixCliqueSet q, (sixCliqueHooks G q x).card ≤ 1) :
    54 ≤ Fintype.card V := by
  classical
  let H := (sixCliqueSet q)ᶜ
  let N : Fin 6 → Finset V := fun i =>
    sixCliqueClosedOutside G q (sixCliqueChosenNeighbor hdegree q hq i)
  have hsub : ∀ i, N i ⊆ H := fun i => six_clique_closed_outside_subset q _
    (sixCliqueChosenNeighbor_outside hdegree q hq i)
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 8 ≤
      (H.filter (fun z => z ∈ N i)).card := by
    intro i _hi
    have he : H.filter (fun z => z ∈ N i) = N i := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun hz => hz.2, fun hz => ⟨hsub i hz, hz⟩⟩
    rw [he]
    exact eight_le_six_clique_closed_outside hdegree q hq hout _
      (sixCliqueChosenNeighbor_outside hdegree q hq i)
  have hcol : ∀ z ∈ H,
      ((Finset.univ : Finset (Fin 6)).filter (fun i => z ∈ N i)).card ≤ 1 := by
    intro z _hz
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hd := six_clique_chosen_closed_disjoint hcrit hr hn hdegree q hq hclique hout i j hij
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hdouble : (∑ i : Fin 6, (H.filter (fun z => z ∈ N i)).card) =
      ∑ z ∈ H, ((Finset.univ : Finset (Fin 6)).filter (fun i => z ∈ N i)).card := by
    convert FiniteBudget.relation_double_count (Finset.univ : Finset (Fin 6)) H
      (fun i z => z ∈ N i) using 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro x _
      congr 1
      ext z
      simp only [Finset.mem_filter]
  have hlow : 48 ≤ ∑ i : Fin 6, (H.filter (fun z => z ∈ N i)).card := by
    calc
      48 = ∑ _i : Fin 6, 8 := by norm_num
      _ ≤ ∑ i : Fin 6, (H.filter (fun z => z ∈ N i)).card := Finset.sum_le_sum hrow
  have hhigh : (∑ z ∈ H, ((Finset.univ : Finset (Fin 6)).filter
      (fun i => z ∈ N i)).card) ≤ H.card := by
    calc
      _ ≤ ∑ _z ∈ H, 1 := Finset.sum_le_sum hcol
      _ = H.card := by simp
  have hpack : 48 ≤ H.card := hlow.trans (hdouble.le.trans hhigh)
  have hcard := Finset.card_add_card_compl (sixCliqueSet q)
  rw [sixCliqueSet_card q hq] at hcard
  change 6 + H.card = Fintype.card V at hcard
  omega

theorem equality_cliqueFree_six (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8) : G.CliqueFree 6 := by
  classical
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn9 := noncomplete_card_ge_nine hcrit hs hr hnot
  have hd : ∀ x : V, 8 ≤ G.degree x := fun x => noncomplete_degree_ge_eight hcrit hs hr hnot x
  have hn51 := critical_card_le_fifty_one hcrit hs hr hn9 hc
  by_contra hfree
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hfree
  have he : Function.Injective e := e.injective
  have hclique : ∀ i j : Fin 6, i ≠ j → G.Adj (e i) (e j) := by
    intro i j hij
    exact e.map_rel_iff.mpr (by simpa using hij)
  have hout : ∀ x ∉ sixCliqueSet e, (sixCliqueHooks G e x).card ≤ 1 := by
    intro x hx
    apply equality_six_clique_outside_hooks_le_one hcrit hc hnot e he hclique x
    intro i hxi
    apply hx
    rw [hxi]
    exact (mem_sixCliqueSet e _).mpr ⟨i, rfl⟩
  have hn54 := six_clique_closed_neighborhood_packing hcrit hr hn9 hd e he hclique hout
  omega

theorem equality_noncomplete_degree_ge_ten (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8) (v : V) :
    10 ≤ G.degree v :=
  critical_degree_ge_ten_of_cliqueFree_six hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) (equality_cliqueFree_six hcrit hc hnot) v

end TaskH.Seven

#print axioms TaskH.Seven.six_clique_root_outside_nonempty
#print axioms TaskH.Seven.sixCliqueChosenNeighbor
#print axioms TaskH.Seven.sixCliqueChosenNeighbor_mem
#print axioms TaskH.Seven.sixCliqueChosenNeighbor_outside
#print axioms TaskH.Seven.sixCliqueChosenNeighbor_adj
#print axioms TaskH.Seven.six_clique_attachment_root_unique
#print axioms TaskH.Seven.sixCliqueChosenNeighbor_injective
#print axioms TaskH.Seven.sixCliqueClosedOutside
#print axioms TaskH.Seven.six_clique_closed_outside_subset
#print axioms TaskH.Seven.eight_le_six_clique_closed_outside
#print axioms TaskH.Seven.six_clique_chosen_closed_disjoint
#print axioms TaskH.Seven.six_clique_closed_neighborhood_packing
#print axioms TaskH.Seven.equality_cliqueFree_six
#print axioms TaskH.Seven.equality_noncomplete_degree_ge_ten
