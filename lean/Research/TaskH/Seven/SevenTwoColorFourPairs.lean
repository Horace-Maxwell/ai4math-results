import Research.TaskH.Seven.SevenTwoColorFrameSwap

/-! At least four actual connected pairs for a fixed INTERNAL pure-split
Frame.  The statement does not assert the missing original all-colorings
pure-split theorem, or min13. No new coloring is assumed pure split: the
already original all-colorings first-step coverage suffices after the swap. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def DegreeTwelveFrame.connectedPairSet {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => F.splitBD i ∈ twoColorComponent c
    (F.singletonIndex 0).val (F.pairIndex i).val (F.centerD 0))

theorem DegreeTwelveFrame.disconnected_pairs_card_le_one
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    ((Finset.univ : Finset (Fin 5)).filter (fun i => F.splitBD i ∉ twoColorComponent c
      (F.singletonIndex 0).val (F.pairIndex i).val (F.centerD 0))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hiout := (Finset.mem_filter.mp hi).2
  have hjout := (Finset.mem_filter.mp hj).2
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
    by_contra! hh
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ {i, j} := by
      intro k _
      by_cases hki : k = i
      · exact Finset.mem_insert.mpr (Or.inl hki)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh k hki)))
    have hle := Finset.card_le_card hsub
    have htwo : ({i, j} : Finset (Fin 5)).card ≤ 2 := Finset.card_le_two
    have hfive : 5 ≤ ({i, j} : Finset (Fin 5)).card := by simpa using hle
    omega
  have hiU := F.disconnected_pair_universal_A hcrit hc hnot hv hF i hiout
  have hjU := F.disconnected_pair_universal_A hcrit hc hnot hv hF j hjout
  exact F.pureSplit_no_triangle_A (equality_cliqueFree_five hcrit hc hnot) hF
    i j k hij (Ne.symm hki) (Ne.symm hkj)
    (hiU j (Ne.symm hij)) (hiU k hki) (hjU k hkj)

theorem DegreeTwelveFrame.connectedPairSet_card_ge_four
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    4 ≤ F.connectedPairSet.card := by
  have hbad := F.disconnected_pairs_card_le_one hcrit hc hnot hv hF
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 5)))
    (fun i => F.splitBD i ∈ twoColorComponent c (F.singletonIndex 0).val
      (F.pairIndex i).val (F.centerD 0))
  change F.connectedPairSet.card + _ = _ at hsum
  norm_num only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

theorem DegreeTwelveFrame.connectedPairSet_seven_paths
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (hi : i ∈ F.connectedPairSet) :
    ∃ p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
      p.IsPath ∧ Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) ∧
      (∀ q : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
        Follows q c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) →
        p.length ≤ q.length) ∧ p.length = 7 := by
  have hreach := (Finset.mem_filter.mp hi).2
  have hac : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
  apply F.connected_splitB_seven_path hcrit hc hnot hF i
  simpa only [hac] using hreach

theorem equality_fixed_pureSplit_four_seven_paths
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    ∃ I : Finset (Fin 5), 4 ≤ I.card ∧
      ∀ i ∈ I, ∃ p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
        p.IsPath ∧ Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) ∧
        p.length = 7 := by
  refine ⟨F.connectedPairSet, F.connectedPairSet_card_ge_four hcrit hc hnot hv hF, ?_⟩
  intro i hi
  obtain ⟨p, hp, hf, _, hl⟩ := F.connectedPairSet_seven_paths hcrit hc hnot hF i hi
  exact ⟨p, hp, hf, hl⟩

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.connectedPairSet
#print axioms TaskH.Seven.DegreeTwelveFrame.disconnected_pairs_card_le_one
#print axioms TaskH.Seven.DegreeTwelveFrame.connectedPairSet_card_ge_four
#print axioms TaskH.Seven.DegreeTwelveFrame.connectedPairSet_seven_paths
#print axioms TaskH.Seven.equality_fixed_pureSplit_four_seven_paths
