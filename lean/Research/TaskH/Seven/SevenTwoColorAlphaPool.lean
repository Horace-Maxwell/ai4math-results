import Research.TaskH.Seven.SevenTwoColorPathPositions

/-! The real old-singleton-colored Q-neighbor pool. Two actual internal
alpha positions outside this pool, plus the actual singleton center, leave
at most two pool points in the whole alpha class. All four labels are covered
by actual endpoints of the actual seven-edge paths; the witnesses may coincide.
No injectivity of the label-to-hub assignment is asserted. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def DegreeTwelveFrame.alphaQPool {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset {x : V // x ≠ v} :=
  Finset.univ.filter (fun z => c z = (F.singletonIndex 0).val ∧
    ∃ j : Fin 5, G.Adj z.val (F.splitB j).val)

theorem DegreeTwelveFrame.alphaQPool_card_le_two_of_path
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7) : F.alphaQPool.card ≤ 2 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let T : Finset {x : V // x ≠ v} := {p.getVert 0, p.getVert 2, p.getVert 4}
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    intro he
    have hh := hp.getVert_injOn (by change 0 ≤ p.length; omega)
      (by change 2 ≤ p.length; omega) he
    omega
  have h04 : p.getVert 0 ≠ p.getVert 4 := by
    intro he
    have hh := hp.getVert_injOn (by change 0 ≤ p.length; omega)
      (by change 4 ≤ p.length; omega) he
    omega
  have h24 : p.getVert 2 ≠ p.getVert 4 := by
    intro he
    have hh := hp.getVert_injOn (by change 2 ≤ p.length; omega)
      (by change 4 ≤ p.length; omega) he
    omega
  have hT : T.card = 3 := by
    have h0not : p.getVert 0 ∉ ({p.getVert 2, p.getVert 4} :
        Finset {x : V // x ≠ v}) := by
      intro hm
      rcases Finset.mem_insert.mp hm with he | he
      · exact h02 he
      · exact h04 (Finset.mem_singleton.mp he)
    have h2not : p.getVert 2 ∉ ({p.getVert 4} :
        Finset {x : V // x ≠ v}) := by
      intro hm
      exact h24 (Finset.mem_singleton.mp hm)
    change (insert (p.getVert 0) (insert (p.getVert 2) {p.getVert 4}) :
      Finset {x : V // x ≠ v}).card = 3
    rw [Finset.card_insert_of_notMem h0not,
      Finset.card_insert_of_notMem h2not, Finset.card_singleton]
  have hcol (n : ℕ) (hn : n ≤ p.length) (heven : n % 2 = 0) :
      c (p.getVert n) = (F.singletonIndex 0).val := by
    have hh := twoColor_color_at p c (F.pairIndex i).val hf n hn
    rw [ite_eq_left heven] at hh
    exact hh.trans (F.center_color 0)
  have hTsub : T ⊆ deletedColorClass v c (F.singletonIndex 0).val := by
    intro z hz
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (mem_deletedColorClass v c _ _).mpr (hcol 0 (by omega) (by decide))
    · exact (mem_deletedColorClass v c _ _).mpr (hcol 2 (by omega) (by decide))
    · exact (mem_deletedColorClass v c _ _).mpr (hcol 4 (by omega) (by decide))
  have hpoolsub : F.alphaQPool ⊆ deletedColorClass v c (F.singletonIndex 0).val := by
    intro z hz
    exact (mem_deletedColorClass v c _ z).mpr (Finset.mem_filter.mp hz).2.1
  have h0out : p.getVert 0 ∉ F.alphaQPool := by
    intro hz
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hz).2.2
    rw [Walk.getVert_zero] at hj
    exact (F.splitAB_adjacencies j (hF j)).2.2.2 hj
  have h2out : p.getVert 2 ∉ F.alphaQPool := by
    intro hz
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hz).2.2
    exact F.seven_path_position_two_not_adj_Q (equality_rainbowSevenCycles hcrit hc)
      hF i j p hp hf hl hj
  have h4out : p.getVert 4 ∉ F.alphaQPool := by
    intro hz
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hz).2.2
    exact F.seven_path_position_four_not_adj_Q (equality_rainbowSevenCycles hcrit hc)
      i j p hp hf hl hj
  have hd : Disjoint F.alphaQPool T := by
    apply Finset.disjoint_left.mpr
    intro z hz hzT
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hzT
    rcases hzT with rfl | rfl | rfl
    · exact h0out hz
    · exact h2out hz
    · exact h4out hz
  have hsub : F.alphaQPool ∪ T ⊆ deletedColorClass v c (F.singletonIndex 0).val :=
    Finset.union_subset hpoolsub hTsub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hT] at hcard
  have hclass := equality_singletonColorClass_card_le_five hcrit hc hnot v c
    (F.singletonIndex 1) (F.singletonIndex 0)
    (F.singletonIndex.injective.ne (by decide : (1 : Fin 2) ≠ 0))
  omega

theorem DegreeTwelveFrame.connected_pair_hits_alphaQPool
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (hi : i ∈ F.connectedPairSet) :
    ∃ z ∈ F.alphaQPool, G.Adj z.val (F.splitB i).val := by
  obtain ⟨p, _hp, hf, _hmin, hl⟩ := F.connectedPairSet_seven_paths hcrit hc hnot hF i hi
  refine ⟨p.getVert 6, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hh := twoColor_color_at p c (F.pairIndex i).val hf 6 (by omega)
      have hcol : c (p.getVert 6) = c (F.centerD 0) := by simpa using hh
      exact hcol.trans (F.center_color 0)
    · refine ⟨i, ?_⟩
      have hlast : p.getVert 7 = F.splitBD i := by simpa only [hl] using p.getVert_length
      have he := p.adj_getVert_succ (i := 6) (by omega)
      rw [hlast] at he
      exact he
  · have hlast : p.getVert 7 = F.splitBD i := by simpa only [hl] using p.getVert_length
    have he := p.adj_getVert_succ (i := 6) (by omega)
    rw [hlast] at he
    exact he

theorem equality_fixed_pureSplit_two_hubs_cover_four_pairs
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    F.alphaQPool.card ≤ 2 ∧ 4 ≤ F.connectedPairSet.card ∧
      ∀ i ∈ F.connectedPairSet, ∃ z ∈ F.alphaQPool, G.Adj z.val (F.splitB i).val := by
  have hfour := F.connectedPairSet_card_ge_four hcrit hc hnot hv hF
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < F.connectedPairSet.card)
  obtain ⟨p, hp, hf, _, hl⟩ := F.connectedPairSet_seven_paths hcrit hc hnot hF i hi
  exact ⟨F.alphaQPool_card_le_two_of_path hcrit hc hnot hF i p hp hf hl, hfour,
    fun j hj => F.connected_pair_hits_alphaQPool hcrit hc hnot hF j hj⟩

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaQPool
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaQPool_card_le_two_of_path
#print axioms TaskH.Seven.DegreeTwelveFrame.connected_pair_hits_alphaQPool
#print axioms TaskH.Seven.equality_fixed_pureSplit_two_hubs_cover_four_pairs
