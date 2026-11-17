import Research.TaskH.Seven.SevenSplitCommonCenterBudget

/-! Once the actual center edge is excluded, either center has at most the
root and its five own-side leaves inside N[v], hence at least six actual
outside neighbors. No outside-cover premise is used. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.pureSplit_centerPool_zero_card_ge_six
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : 6 ≤ (F.centerPool 0).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let a := (F.center 0).val
  let N := insert v (G.neighborFinset v)
  let P := (Finset.univ : Finset (Fin 5)).image (fun i => (F.splitA i).val)
  let I := (G.neighborFinset a).filter (fun z => z ∈ N)
  have hab := equality_degreeTwelve_centers_not_adj hcrit hc hnot hv F hF
  have hsub : I ⊆ insert v P := by
    intro z hz
    have haz := (G.mem_neighborFinset a z).mp (Finset.mem_filter.mp hz).1
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).2 with hzv | hzv
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases F.split_neighbor_cases zz with ⟨j, hj⟩ | ⟨i, hi | hi⟩
      · change z = (F.center j).val at hj
        fin_cases j
        · exact (haz.ne hj.symm).elim
        · exact (hab (by rw [hj] at haz; exact haz)).elim
      · change z = (F.splitA i).val at hi
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, hi.symm⟩))
      · change z = (F.splitB i).val at hi
        exact ((F.splitAB_adjacencies i (hF i)).2.2.2
          (by rw [hi] at haz; exact haz)).elim
  have hP : P.card ≤ 5 := by
    have hh := Finset.card_image_le (s := (Finset.univ : Finset (Fin 5)))
      (f := fun i => (F.splitA i).val)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  have hI : I.card ≤ 6 := by
    have hh := Finset.card_le_card hsub
    have hb := Finset.card_insert_le v P
    omega
  have hp := Finset.card_filter_add_card_filter_not (s := G.neighborFinset a) (p := fun z => z ∈ N)
  have hout : (G.neighborFinset a).filter (fun z => z ∉ N) = F.centerPool 0 := by
    ext z
    simp only [DegreeTwelveFrame.centerPool, rootOutside, Finset.mem_filter,
      Finset.mem_compl, G.mem_neighborFinset]
    change (G.Adj a z ∧ z ∉ N) ↔ (z ∉ N ∧ G.Adj a z)
    exact and_comm
  rw [hout, G.card_neighborFinset_eq_degree] at hp
  change I.card + (F.centerPool 0).card = G.degree a at hp
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot a
  omega

theorem DegreeTwelveFrame.pureSplit_centerPool_one_card_ge_six
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : 6 ≤ (F.centerPool 1).card := by
  have h := F.swapCenters.pureSplit_centerPool_zero_card_ge_six hcrit hc hnot hv
    (F.swapCenters_pureSplit hF)
  simpa only [F.swapCenters_centerPool_zero] using h

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_zero_card_ge_six
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_one_card_ge_six
