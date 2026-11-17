import Research.TaskH.Seven.SevenSplitLeafIncidence

/-! A true common outside center neighbor has all neighbors in {a,b} union
the actual residual pool. The three actual disjoint pools force36>33. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.common_center_neighbor_cases
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1)
    (z : V) (hwz : G.Adj w z) :
    z = (F.center 0).val ∨ z = (F.center 1).val ∨ z ∈ F.residualPool := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have hwA := (Finset.mem_inter.mp hw).1
  have hwB := (Finset.mem_inter.mp hw).2
  have hwO := (Finset.mem_filter.mp hwA).1
  by_cases hzO : z ∈ rootOutside G v
  · right; right
    apply F.mem_residualPool_iff.mpr
    refine ⟨hzO, ?_, ?_, ?_, ?_⟩
    · intro hzA
      exact F.pureSplit_no_centerPool_edge hr hF z w hzA hwB hwz.symm
    · intro hzB
      exact F.pureSplit_no_centerPool_edge hr hF w z hwA hzB hwz
    · intro hzX
      exact F.pureSplit_centerPool_one_no_A_pool_edge hr hF w z hwB hzX hwz
    · intro hzY
      exact F.pureSplit_centerPool_zero_no_B_pool_edge hr hF w z hwA hzY hwz
  · have hzN : z ∈ insert v (G.neighborFinset v) := by
      by_contra hn
      exact hzO (Finset.mem_compl.mpr hn)
    rcases Finset.mem_insert.mp hzN with hzv | hzN
    · have hvw : G.Adj v w := by rw [hzv] at hwz; exact hwz.symm
      exact ((Finset.mem_compl.mp hwO) (Finset.mem_insert.mpr
        (Or.inr ((G.mem_neighborFinset v w).mpr hvw)))).elim
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzN⟩
      rcases F.split_neighbor_cases zz with ⟨j, hj⟩ | ⟨i, hi | hi⟩
      · change z = (F.center j).val at hj
        fin_cases j
        · exact Or.inl hj
        · exact Or.inr (Or.inl hj)
      · change z = (F.splitA i).val at hi
        have hwX : w ∈ F.splitPoolA := Finset.mem_filter.mpr
          ⟨hwO, i, by rw [← hi]; exact hwz⟩
        exact ((Finset.disjoint_left.mp (F.pureSplit_centerPool_one_disjoint_A hr hF))
          hwB hwX).elim
      · change z = (F.splitB i).val at hi
        have hwY : w ∈ F.splitPoolB := Finset.mem_filter.mpr
          ⟨hwO, i, by rw [← hi]; exact hwz⟩
        exact ((Finset.disjoint_left.mp (F.pureSplit_centerPool_zero_disjoint_B hr hF))
          hwA hwY).elim

theorem DegreeTwelveFrame.common_center_residual_card_ge_ten
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1) : 10 ≤ F.residualPool.card := by
  classical
  have hsub : G.neighborFinset w ⊆ insert (F.center 0).val (insert (F.center 1).val F.residualPool) := by
    intro z hz
    have hzw := (G.mem_neighborFinset w z).mp hz
    rcases F.common_center_neighbor_cases (equality_rainbowSevenCycles hcrit hc) hF w hw z hzw
      with h0 | h1 | hZ
    · exact Finset.mem_insert.mpr (Or.inl h0)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h1)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hZ)))
  have hh := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hh
  have h0 := Finset.card_insert_le (F.center 0).val (insert (F.center 1).val F.residualPool)
  have h1 := Finset.card_insert_le (F.center 1).val F.residualPool
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot w
  omega

theorem equality_degreeTwelve_centerPools_disjoint
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    Disjoint (F.centerPool 0) (F.centerPool 1) := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  apply Finset.disjoint_left.mpr
  intro w hwA hwB
  have hw := Finset.mem_inter.mpr ⟨hwA, hwB⟩
  have hX := F.common_center_splitPoolA_card_ge_thirteen hcrit hc hnot hF w hw
  have hY := F.common_center_splitPoolB_card_ge_thirteen hcrit hc hnot hF w hw
  have hZ := F.common_center_residual_card_ge_ten hcrit hc hnot hF w hw
  have hXY := F.pureSplit_splitPools_disjoint (equality_rainbowSevenCycles hcrit hc) hF
  have hdis : Disjoint (F.splitPoolA ∪ F.splitPoolB) F.residualPool := by
    apply Finset.disjoint_left.mpr
    intro z hz hzZ
    have hz' := F.mem_residualPool_iff.mp hzZ
    rcases Finset.mem_union.mp hz with h | h
    · exact hz'.2.2.2.1 h
    · exact hz'.2.2.2.2 h
  have hsub : (F.splitPoolA ∪ F.splitPoolB) ∪ F.residualPool ⊆ rootOutside G v := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · rcases Finset.mem_union.mp h with hx | hy
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hy).1
    · exact (F.mem_residualPool_iff.mp h).1
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hXY] at hh
  have hn : (rootOutside G v).card ≤ 33 := by
    change ((insert v (G.neighborFinset v))ᶜ : Finset V).card ≤ 33
    exact equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  omega

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_neighbor_cases
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_residual_card_ge_ten
#print axioms TaskH.Seven.equality_degreeTwelve_centerPools_disjoint
