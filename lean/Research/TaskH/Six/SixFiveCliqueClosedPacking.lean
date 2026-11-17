import Research.TaskH.Six.SixFiveCliqueSeparation

/-!
Choose one actual outside neighbor of each five-clique vertex. Unique
attachment labels and the actual path exclusions separate their closed
outside neighborhoods. The five neighborhoods each contain at least eight
vertices, so the graph has at least 45 vertices.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem five_clique_neighbors_card (q : Fin 5 → V) (hq : Function.Injective q) (x : V) :
    (packingNeighborsIn G (fiveCliqueSet q) x).card = (fiveCliqueHooks G q x).card := by
  classical
  have he : packingNeighborsIn G (fiveCliqueSet q) x = (fiveCliqueHooks G q x).image q := by
    ext z
    simp only [packingNeighborsIn, fiveCliqueSet, fiveCliqueHooks, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hxi⟩
      exact ⟨i, hxi, rfl⟩
    · rintro ⟨i, hxi, rfl⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
  rw [he, Finset.card_image_of_injective _ hq]

omit [Fintype V] in
theorem five_clique_root_inside_card_le_four (q : Fin 5 → V)
    (hq : Function.Injective q) (i : Fin 5) :
    (packingNeighborsIn G (fiveCliqueSet q) (q i)).card ≤ 4 := by
  classical
  have hmem : q i ∈ fiveCliqueSet q := (mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩
  have hsub : packingNeighborsIn G (fiveCliqueSet q) (q i) ⊆ (fiveCliqueSet q).erase (q i) := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
  have hh := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hmem, fiveCliqueSet_card q hq] at hh

theorem five_clique_root_outside_nonempty (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q) (i : Fin 5) :
    (packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i)).Nonempty := by
  have hout := packingNeighborsIn_compl_lower (fiveCliqueSet q) (q i) 8 4 (hdegree _)
    (five_clique_root_inside_card_le_four q hq i)
  apply Finset.card_pos.mp
  omega

noncomputable def fiveCliqueChosenNeighbor (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q) (i : Fin 5) : V :=
  (five_clique_root_outside_nonempty hdegree q hq i).choose

theorem fiveCliqueChosenNeighbor_mem (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q) (i : Fin 5) :
    fiveCliqueChosenNeighbor hdegree q hq i ∈ packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i) :=
  (five_clique_root_outside_nonempty hdegree q hq i).choose_spec

theorem fiveCliqueChosenNeighbor_outside (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q) (i : Fin 5) :
    fiveCliqueChosenNeighbor hdegree q hq i ∉ fiveCliqueSet q :=
  Finset.mem_compl.mp (Finset.mem_filter.mp (fiveCliqueChosenNeighbor_mem hdegree q hq i)).1

theorem fiveCliqueChosenNeighbor_adj (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q) (i : Fin 5) :
    G.Adj (q i) (fiveCliqueChosenNeighbor hdegree q hq i) :=
  (Finset.mem_filter.mp (fiveCliqueChosenNeighbor_mem hdegree q hq i)).2

omit [Fintype V] [DecidableRel G.Adj] in
theorem five_clique_attachment_root_unique (q : Fin 5 → V)
    (hout : ∀ x ∉ fiveCliqueSet q, (fiveCliqueHooks G q x).card ≤ 1)
    (x : V) (hx : x ∉ fiveCliqueSet q) (i j : Fin 5)
    (hix : G.Adj (q i) x) (hjx : G.Adj (q j) x) : i = j := by
  classical
  have hmem : ∀ a : Fin 5, a ∈ fiveCliqueHooks G q x ↔ G.Adj x (q a) := by
    intro a
    simp only [fiveCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : i ∈ fiveCliqueHooks G q x := (hmem i).mpr hix.symm
  have hj : j ∈ fiveCliqueHooks G q x := (hmem j).mpr hjx.symm
  exact Finset.card_le_one.mp (hout x hx) i hi j hj

theorem fiveCliqueChosenNeighbor_injective (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hout : ∀ x ∉ fiveCliqueSet q, (fiveCliqueHooks G q x).card ≤ 1) :
    Function.Injective (fiveCliqueChosenNeighbor hdegree q hq) := by
  intro i j he
  apply five_clique_attachment_root_unique q hout
    (fiveCliqueChosenNeighbor hdegree q hq i) (fiveCliqueChosenNeighbor_outside hdegree q hq i) i j
    (fiveCliqueChosenNeighbor_adj hdegree q hq i)
  rw [he]
  exact fiveCliqueChosenNeighbor_adj hdegree q hq j

noncomputable def fiveCliqueClosedOutside (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 5 → V) (x : V) : Finset V :=
  insert x (packingNeighborsIn G (fiveCliqueSet q)ᶜ x)

theorem five_clique_closed_outside_subset (q : Fin 5 → V) (x : V)
    (hx : x ∉ fiveCliqueSet q) : fiveCliqueClosedOutside G q x ⊆ (fiveCliqueSet q)ᶜ := by
  classical
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_compl.mpr hx
  · exact (Finset.mem_filter.mp hz).1

theorem eight_le_five_clique_closed_outside (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hout : ∀ x ∉ fiveCliqueSet q, (fiveCliqueHooks G q x).card ≤ 1)
    (x : V) (hx : x ∉ fiveCliqueSet q) : 8 ≤ (fiveCliqueClosedOutside G q x).card := by
  classical
  have hin : (packingNeighborsIn G (fiveCliqueSet q) x).card ≤ 1 := by
    rw [five_clique_neighbors_card q hq x]
    exact hout x hx
  have h7 := packingNeighborsIn_compl_lower (fiveCliqueSet q) x 8 1 (hdegree x) hin
  have hxN : x ∉ packingNeighborsIn G (fiveCliqueSet q)ᶜ x := by
    intro hxN
    exact (Finset.mem_filter.mp hxN).2.ne rfl
  rw [fiveCliqueClosedOutside, Finset.card_insert_of_notMem hxN]
  omega

theorem five_clique_chosen_closed_disjoint (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 8 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hout : ∀ x ∉ fiveCliqueSet q, (fiveCliqueHooks G q x).card ≤ 1)
    (i j : Fin 5) (hij : i ≠ j) :
    Disjoint (fiveCliqueClosedOutside G q (fiveCliqueChosenNeighbor hdegree q hq i))
      (fiveCliqueClosedOutside G q (fiveCliqueChosenNeighbor hdegree q hq j)) := by
  classical
  let x := fiveCliqueChosenNeighbor hdegree q hq i
  let x' := fiveCliqueChosenNeighbor hdegree q hq j
  have hx : x ∉ fiveCliqueSet q := fiveCliqueChosenNeighbor_outside hdegree q hq i
  have hx' : x' ∉ fiveCliqueSet q := fiveCliqueChosenNeighbor_outside hdegree q hq j
  have hix : G.Adj (q i) x := fiveCliqueChosenNeighbor_adj hdegree q hq i
  have hjx' : G.Adj (q j) x' := fiveCliqueChosenNeighbor_adj hdegree q hq j
  have hxx' : x ≠ x' := (fiveCliqueChosenNeighbor_injective hdegree q hq hout).ne hij
  have hno := critical_five_clique_no_cross_edge hcrit hr hn q hq hclique i j hij x x' hx hx' hix hjx'
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
    · have hz : z ∉ fiveCliqueSet q :=
        Finset.mem_compl.mp (Finset.mem_filter.mp hzi).1
      exact critical_five_clique_no_cross_common_neighbor hcrit hr hn q hq hclique
        i j hij x x' z hx hx' hz hxx' hix hjx'
        (Finset.mem_filter.mp hzi).2 (Finset.mem_filter.mp hzj).2

/-- This is a closed-neighborhood count in the actual graph, with the five
rows indexed by real selected neighbors of its five actual clique vertices. -/
theorem five_clique_closed_neighborhood_packing (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 8 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hout : ∀ x ∉ fiveCliqueSet q, (fiveCliqueHooks G q x).card ≤ 1) :
    45 ≤ Fintype.card V := by
  classical
  let H := (fiveCliqueSet q)ᶜ
  let N : Fin 5 → Finset V := fun i =>
    fiveCliqueClosedOutside G q (fiveCliqueChosenNeighbor hdegree q hq i)
  have hsub : ∀ i, N i ⊆ H := fun i => five_clique_closed_outside_subset q _
    (fiveCliqueChosenNeighbor_outside hdegree q hq i)
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 8 ≤
      (H.filter (fun z => z ∈ N i)).card := by
    intro i _hi
    have he : H.filter (fun z => z ∈ N i) = N i := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun hz => hz.2, fun hz => ⟨hsub i hz, hz⟩⟩
    rw [he]
    exact eight_le_five_clique_closed_outside hdegree q hq hout _
      (fiveCliqueChosenNeighbor_outside hdegree q hq i)
  have hcol : ∀ z ∈ H,
      ((Finset.univ : Finset (Fin 5)).filter (fun i => z ∈ N i)).card ≤ 1 := by
    intro z _hz
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hd := five_clique_chosen_closed_disjoint hcrit hr hn hdegree q hq hclique hout i j hij
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hdouble : (∑ i : Fin 5, (H.filter (fun z => z ∈ N i)).card) =
      ∑ z ∈ H, ((Finset.univ : Finset (Fin 5)).filter (fun i => z ∈ N i)).card := by
    convert FiniteBudget.relation_double_count (Finset.univ : Finset (Fin 5)) H
      (fun i z => z ∈ N i) using 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro x _
      congr 1
      ext z
      simp only [Finset.mem_filter]
  have hlow : 40 ≤ ∑ i : Fin 5, (H.filter (fun z => z ∈ N i)).card := by
    calc
      40 = ∑ _i : Fin 5, 8 := by norm_num
      _ ≤ ∑ i : Fin 5, (H.filter (fun z => z ∈ N i)).card := Finset.sum_le_sum hrow
  have hhigh : (∑ z ∈ H, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => z ∈ N i)).card) ≤ H.card := by
    calc
      _ ≤ ∑ _z ∈ H, 1 := Finset.sum_le_sum hcol
      _ = H.card := by simp
  have hpack : 40 ≤ H.card := hlow.trans (hdouble.le.trans hhigh)
  have hcard := Finset.card_add_card_compl (fiveCliqueSet q)
  rw [fiveCliqueSet_card q hq] at hcard
  change 5 + H.card = Fintype.card V at hcard
  omega

theorem equality_cliqueFree_five (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) : G.CliqueFree 5 := by
  classical
  have hs : ShortSixCycles G := equality_shortSixCycles hcrit hc
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hb := critical_noncomplete_bounds hcrit hs hr hc hnot
  by_contra hfree
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hfree
  have he : Function.Injective e := e.injective
  have hclique : ∀ i j : Fin 5, i ≠ j → G.Adj (e i) (e j) := by
    intro i j hij
    exact e.map_rel_iff.mpr (by simpa using hij)
  have hout : ∀ x ∉ fiveCliqueSet e, (fiveCliqueHooks G e x).card ≤ 1 := by
    intro x hx
    apply equality_five_clique_outside_hooks_le_one hcrit hc hnot e he hclique x
    intro i hxi
    apply hx
    rw [hxi]
    exact (mem_fiveCliqueSet e _).mpr ⟨i, rfl⟩
  have h45 := five_clique_closed_neighborhood_packing hcrit hr hb.1
    (fun x => (hb.2.2 x).1) e he hclique hout
  have hn37 := hb.2.1
  omega

end TaskH.Six

#print axioms TaskH.Six.five_clique_neighbors_card
#print axioms TaskH.Six.five_clique_root_inside_card_le_four
#print axioms TaskH.Six.five_clique_root_outside_nonempty
#print axioms TaskH.Six.fiveCliqueChosenNeighbor
#print axioms TaskH.Six.fiveCliqueChosenNeighbor_mem
#print axioms TaskH.Six.fiveCliqueChosenNeighbor_outside
#print axioms TaskH.Six.fiveCliqueChosenNeighbor_adj
#print axioms TaskH.Six.five_clique_attachment_root_unique
#print axioms TaskH.Six.fiveCliqueChosenNeighbor_injective
#print axioms TaskH.Six.fiveCliqueClosedOutside
#print axioms TaskH.Six.five_clique_closed_outside_subset
#print axioms TaskH.Six.eight_le_five_clique_closed_outside
#print axioms TaskH.Six.five_clique_chosen_closed_disjoint
#print axioms TaskH.Six.five_clique_closed_neighborhood_packing
#print axioms TaskH.Six.equality_cliqueFree_five
