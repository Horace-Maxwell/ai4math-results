import Research.TaskH.Seven.SevenPureSplit
import Research.TaskH.Seven.SevenSplitCommonCenterPaths
import Research.TaskH.Seven.SevenTwoColorResidual

/-! Actual split-leaf internal graph and outside incidence. Triangle-free
Mantel gives38 incidences on each side; a real common center neighbor makes
the side independent, giving50 incidences and the proved capacity four. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def splitGraphA {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : SimpleGraph (Fin 5) :=
  G.comap (fun i => (F.splitA i).val)

noncomputable def splitAOutsideDegree {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : ℕ :=
  ((rootOutside G v).filter (fun z => G.Adj (F.splitA i).val z)).card

theorem splitA_outside_add_internal_ge_ten
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5) :
    10 ≤ splitAOutsideDegree F i + (splitGraphA F).degree i := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let p := (F.splitA i).val
  let N := insert v (G.neighborFinset v)
  let L := (splitGraphA F).neighborFinset i
  let I := (G.neighborFinset p).filter (fun z => z ∈ N)
  let B := insert v (insert (F.center 0).val (L.image (fun j => (F.splitA j).val)))
  have hi := F.splitAB_adjacencies i (hF i)
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hsub : I ⊆ B := by
    intro z hz
    have hpz := (G.mem_neighborFinset p z).mp (Finset.mem_filter.mp hz).1
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).2 with hzv | hzv
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases F.split_neighbor_cases zz with ⟨j, hj⟩ | ⟨j, hj | hj⟩
      · change z = (F.center j).val at hj
        fin_cases j
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hj)))
        · exact (hi.2.1 (by rw [hj] at hpz; exact hpz.symm)).elim
      · change z = (F.splitA j).val at hj
        have hjL : j ∈ L := by
          apply ((splitGraphA F).mem_neighborFinset i j).mpr
          change G.Adj p (F.splitA j).val
          rw [← hj]
          exact hpz
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_image.mpr ⟨j, hjL, hj.symm⟩))))
      · change z = (F.splitB j).val at hj
        exact (F.pureSplit_cross_not_adj hr hF i j (by rw [← hj]; exact hpz)).elim
  have hI : I.card ≤ 2 + (splitGraphA F).degree i := by
    have hh := Finset.card_le_card hsub
    have him : (L.image (fun j => (F.splitA j).val)).card ≤ L.card := Finset.card_image_le
    have h0 := Finset.card_insert_le v (insert (F.center 0).val (L.image (fun j => (F.splitA j).val)))
    have h1 := Finset.card_insert_le (F.center 0).val (L.image (fun j => (F.splitA j).val))
    have hL : L.card = (splitGraphA F).degree i := (splitGraphA F).card_neighborFinset_eq_degree i
    change I.card ≤ (insert v (insert (F.center 0).val (L.image (fun j => (F.splitA j).val)))).card at hh
    omega
  have hp := Finset.card_filter_add_card_filter_not (s := G.neighborFinset p) (p := fun z => z ∈ N)
  have hout : (G.neighborFinset p).filter (fun z => z ∉ N) =
      (rootOutside G v).filter (fun z => G.Adj p z) := by
    ext z
    simp only [Finset.mem_filter, G.mem_neighborFinset, rootOutside, Finset.mem_compl]
    change (G.Adj p z ∧ z ∉ N) ↔ (z ∉ N ∧ G.Adj p z)
    exact and_comm
  rw [hout, G.card_neighborFinset_eq_degree] at hp
  change I.card + splitAOutsideDegree F i = G.degree p at hp
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot p
  omega

theorem splitGraphA_cliqueFree_three
    (hfree : G.CliqueFree 5) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : (splitGraphA F).CliqueFree 3 := by
  classical
  intro S hS
  let e : Fin 3 ≃ ↥S := (Finset.equivFinOfCardEq hS.2).symm
  have hne : ∀ i j : Fin 3, i ≠ j → (e i).val ≠ (e j).val := by
    intro i j hij he
    exact hij (e.injective (Subtype.ext he))
  exact F.pureSplit_no_triangle_A hfree hF (e 0).val (e 1).val (e 2).val
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    (hS.1 (e 0).property (e 1).property (hne 0 1 (by decide)))
    (hS.1 (e 0).property (e 2).property (hne 0 2 (by decide)))
    (hS.1 (e 1).property (e 2).property (hne 1 2 (by decide)))

theorem splitA_total_outside_ge_thirty_eight
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    38 ≤ ∑ i : Fin 5, splitAOutsideDegree F i := by
  classical
  have hrow : 50 ≤ (∑ i : Fin 5, splitAOutsideDegree F i) +
      ∑ i : Fin 5, (splitGraphA F).degree i := by
    calc
      50 = ∑ _i : Fin 5, 10 := by norm_num
      _ ≤ ∑ i : Fin 5, (splitAOutsideDegree F i + (splitGraphA F).degree i) :=
        Finset.sum_le_sum (fun i _ => splitA_outside_add_internal_ge_ten hcrit hc hnot F hF i)
      _ = _ := Finset.sum_add_distrib
  have he : (splitGraphA F).edgeFinset.card ≤ SimpleGraph.turanNumber 5 2 := by
    simpa only [Fintype.card_fin] using
      (splitGraphA_cliqueFree_three (equality_cliqueFree_five hcrit hc hnot) F hF).card_edgeFinset_le (r := 2)
  rw [SimpleGraph.turanNumber_two] at he
  norm_num at he
  have hs := (splitGraphA F).sum_degrees_eq_twice_card_edges
  omega

theorem splitA_pool_incidence {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    (∑ i : Fin 5, splitAOutsideDegree F i) =
      ∑ z ∈ F.splitPoolA, ((Finset.univ : Finset (Fin 5)).filter
        (fun i => G.Adj z (F.splitA i).val)).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let R : Fin 5 → V → Prop := fun i z => G.Adj z (F.splitA i).val
  have hrow : ∀ i, splitAOutsideDegree F i = (F.splitPoolA.filter (R i)).card := by
    intro i
    have he : (rootOutside G v).filter (fun z => G.Adj (F.splitA i).val z) =
        F.splitPoolA.filter (R i) := by
      ext z
      simp only [DegreeTwelveFrame.splitPoolA, Finset.mem_filter, R]
      exact ⟨fun h => ⟨⟨h.1, i, h.2.symm⟩, h.2.symm⟩,
        fun h => ⟨h.1.1, h.2.symm⟩⟩
    exact congrArg Finset.card he
  calc
    _ = ∑ i : Fin 5, (F.splitPoolA.filter (R i)).card := Finset.sum_congr rfl (fun i _ => hrow i)
    _ = _ := FiniteBudget.relation_double_count Finset.univ F.splitPoolA R

theorem DegreeTwelveFrame.pureSplit_splitPoolA_card_ge_eight
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : 8 ≤ F.splitPoolA.card := by
  have hlo := splitA_total_outside_ge_thirty_eight hcrit hc hnot F hF
  rw [splitA_pool_incidence] at hlo
  have hhi : (∑ z ∈ F.splitPoolA, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => G.Adj z (F.splitA i).val)).card) ≤ F.splitPoolA.card * 5 := by
    calc
      _ ≤ ∑ _z ∈ F.splitPoolA, 5 := Finset.sum_le_sum (fun z _ => by
        simpa only [Fintype.card_fin] using (Finset.card_le_univ
          ((Finset.univ : Finset (Fin 5)).filter (fun i => G.Adj z (F.splitA i).val))))
      _ = _ := by simp
  omega

theorem DegreeTwelveFrame.common_center_splitPoolA_card_ge_thirteen
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1) : 13 ≤ F.splitPoolA.card := by
  classical
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hdeg : ∀ i : Fin 5, (splitGraphA F).degree i = 0 := by
    intro i
    rw [← (splitGraphA F).card_neighborFinset_eq_degree]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have he := ((splitGraphA F).mem_neighborFinset i j).mp hj
    by_cases hij : i = j
    · subst j
      exact he.ne rfl
    · exact F.common_center_A_independent hr hF w hw i j hij he
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 10 ≤ splitAOutsideDegree F i := by
    intro i _hi
    have h := splitA_outside_add_internal_ge_ten hcrit hc hnot F hF i
    rw [hdeg] at h
    omega
  have hlo : 50 ≤ ∑ i : Fin 5, splitAOutsideDegree F i := by
    calc
      50 = ∑ _i : Fin 5, 10 := by norm_num
      _ ≤ _ := Finset.sum_le_sum hrow
  rw [splitA_pool_incidence] at hlo
  have hhi : (∑ z ∈ F.splitPoolA, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => G.Adj z (F.splitA i).val)).card) ≤ F.splitPoolA.card * 4 := by
    calc
      _ ≤ ∑ _z ∈ F.splitPoolA, 4 := Finset.sum_le_sum (fun z hz =>
        F.common_center_outside_A_capacity_four hr hF w hw z (Finset.mem_filter.mp hz).1)
      _ = _ := by simp
  omega

theorem DegreeTwelveFrame.pureSplit_splitPoolB_card_ge_eight
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : 8 ≤ F.splitPoolB.card := by
  have h := F.swapCenters.pureSplit_splitPoolA_card_ge_eight hcrit hc hnot (F.swapCenters_pureSplit hF)
  simpa only [F.swapCenters_splitPoolA hF] using h

theorem DegreeTwelveFrame.common_center_splitPoolB_card_ge_thirteen
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1) : 13 ≤ F.splitPoolB.card := by
  have hw' : w ∈ F.swapCenters.centerPool 0 ∩ F.swapCenters.centerPool 1 := by
    apply Finset.mem_inter.mpr
    exact ⟨by simpa only [F.swapCenters_centerPool_zero] using (Finset.mem_inter.mp hw).2,
      by simpa only [F.swapCenters_centerPool_one] using (Finset.mem_inter.mp hw).1⟩
  have h := F.swapCenters.common_center_splitPoolA_card_ge_thirteen hcrit hc hnot
    (F.swapCenters_pureSplit hF) w hw'
  simpa only [F.swapCenters_splitPoolA hF] using h

end TaskH.Seven
#print axioms TaskH.Seven.splitGraphA
#print axioms TaskH.Seven.splitAOutsideDegree
#print axioms TaskH.Seven.splitA_outside_add_internal_ge_ten
#print axioms TaskH.Seven.splitGraphA_cliqueFree_three
#print axioms TaskH.Seven.splitA_total_outside_ge_thirty_eight
#print axioms TaskH.Seven.splitA_pool_incidence
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_splitPoolA_card_ge_eight
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_splitPoolA_card_ge_thirteen
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_splitPoolB_card_ge_eight
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_splitPoolB_card_ge_thirteen
