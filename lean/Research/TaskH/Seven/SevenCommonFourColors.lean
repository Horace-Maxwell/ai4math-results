import Research.TaskH.Seven.SevenCommonFive

/-! At h4 every multi-representative outside point has the ONE noncommon
pair color. Its whole old class has at most seven points, two already being
actual root neighbors; hence at most five such outside points remain. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_third_common_of_card_ge_three {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hcard : 3 ≤ F.commonColors.card)
    (i j : ↥F.commonColors) : ∃ k : ↥F.commonColors, k ≠ i ∧ k ≠ j := by
  classical
  by_contra! hh
  have hs : (Finset.univ : Finset ↥F.commonColors) ⊆ {i, j} := by
    intro k _hk
    by_cases hki : k = i
    · exact Finset.mem_insert.mpr (Or.inl hki)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh k hki)))
  have hc := Finset.card_le_card hs
  have hc' : F.commonColors.card ≤ ({i, j} : Finset ↥F.commonColors).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hc
  have hp : ({i, j} : Finset ↥F.commonColors).card ≤ 2 := Finset.card_le_two
  omega

theorem multi_common_outside_color_is_noncommon
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hcard : 3 ≤ F.commonColors.card)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hm : 2 ≤ (commonPoolHits F z.val).card) :
    ∃ gamma : Fin 5, gamma ∉ F.commonColors ∧ c z = (F.pairIndex gamma).val := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (commonPoolHits F z.val).card)
  have hzi := (mem_commonPoolHits F z.val i).mp hi
  have hzj := (mem_commonPoolHits F z.val j).mp hj
  obtain ⟨k, hki, hkj⟩ := exists_third_common_of_card_ge_three F hcard i j
  have H := three_common_representatives_outside_color_constraints hr F i j k hij
    (Ne.symm hki) (Ne.symm hkj) z hz hzi hzj
  have hni : c z ≠ (F.pairIndex i.val).val := H.2.2.1
  have hnj : c z ≠ (F.pairIndex j.val).val := H.2.2.2.1
  rcases F.color_cases (c z) with ⟨d, hd⟩ | ⟨gamma, hg⟩
  · fin_cases d
    · exact (H.1 (hd.symm.trans (F.center_color 0).symm)).elim
    · exact (H.2.1 (hd.symm.trans (F.center_color 1).symm)).elim
  · by_cases hgamma : gamma ∈ F.commonColors
    · let l : ↥F.commonColors := ⟨gamma, hgamma⟩
      by_cases hli : l = i
      · exact (hni (hg.symm.trans (congrArg (fun t : ↥F.commonColors => (F.pairIndex t.val).val) hli))).elim
      · by_cases hlj : l = j
        · exact (hnj (hg.symm.trans (congrArg (fun t : ↥F.commonColors => (F.pairIndex t.val).val) hlj))).elim
        · have H' := three_common_representatives_outside_color_constraints hr F i j l hij
            (Ne.symm hli) (Ne.symm hlj) z hz hzi hzj
          exact (H'.2.2.2.2 hg.symm).elim
    · exact ⟨gamma, hgamma, hg.symm⟩

noncomputable def multiCommonPool {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (D : Finset V) : Finset V :=
  D.filter (fun z => 2 ≤ (commonPoolHits F z).card)

theorem common_four_multi_color
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfour : F.commonColors.card = 4) :
    ∃ gamma : Fin 5, gamma ∉ F.commonColors ∧
      ∀ z : {x : V // x ≠ v}, z.val ∉ insert v (G.neighborFinset v) →
        2 ≤ (commonPoolHits F z.val).card → c z = (F.pairIndex gamma).val := by
  have hcomp : (F.commonColorsᶜ).card = 1 := by
    have hh := Finset.card_add_card_compl F.commonColors
    rw [hfour] at hh
    norm_num at hh
    omega
  obtain ⟨gamma, hg⟩ := Finset.card_eq_one.mp hcomp
  have hgamma : gamma ∉ F.commonColors := by
    apply Finset.mem_compl.mp
    rw [hg]
    exact Finset.mem_singleton_self gamma
  refine ⟨gamma, hgamma, ?_⟩
  intro z hz hm
  obtain ⟨eta, heta, hcolor⟩ := multi_common_outside_color_is_noncommon
    (equality_rainbowSevenCycles hcrit hc) F (by omega) z hz hm
  have he : eta = gamma := by
    have hi := Finset.mem_compl.mpr heta
    rw [hg] at hi
    exact Finset.mem_singleton.mp hi
  simpa only [he] using hcolor

theorem common_four_multi_card_le_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfour : F.commonColors.card = 4)
    (D : Finset V) (hD : D ⊆ ((insert v (G.neighborFinset v))ᶜ : Finset V)) :
    (multiCommonPool F D).card ≤ 5 := by
  classical
  obtain ⟨gamma, _hg, hcolor⟩ := common_four_multi_color hcrit hc F hfour
  let M := multiCommonPool F D
  let T := (deletedColorClass v c (F.pairIndex gamma).val).image Subtype.val
  let P : Finset V := {(F.leaf gamma 0).val, (F.leaf gamma 1).val}
  have hMsub : M ⊆ T := by
    intro z hz
    have hm := Finset.mem_filter.mp hz
    have hzout := Finset.mem_compl.mp (hD hm.1)
    have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
    refine Finset.mem_image.mpr ⟨⟨z, hzv⟩, ?_, rfl⟩
    exact (mem_deletedColorClass v c _ _).mpr (hcolor ⟨z, hzv⟩ hzout hm.2)
  have hleaf : ∀ e : Fin 2, (F.leaf gamma e).val ∈ T := by
    intro e
    refine Finset.mem_image.mpr ⟨⟨(F.leaf gamma e).val, (F.leaf gamma e).property.ne.symm⟩, ?_, rfl⟩
    exact (mem_deletedColorClass v c _ _).mpr (F.leaf_color gamma e)
  have hPsub : P ⊆ T := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]
      exact hleaf 0
    · rw [Finset.mem_singleton.mp h]
      exact hleaf 1
  have hdis : Disjoint M P := by
    apply Finset.disjoint_left.mpr
    intro z hzM hzP
    have hzout := Finset.mem_compl.mp (hD (Finset.mem_filter.mp hzM).1)
    rcases Finset.mem_insert.mp hzP with h | h
    · exact outside_closed_ne_neighbor z hzout (F.leaf gamma 0) h
    · exact outside_closed_ne_neighbor z hzout (F.leaf gamma 1) (Finset.mem_singleton.mp h)
  have hP : P.card = 2 := Finset.card_pair ((F.leaf_same_pair_injective gamma).ne (by decide : (0 : Fin 2) ≠ 1))
  have hT : T.card ≤ 7 := by
    change ((deletedColorClass v c (F.pairIndex gamma).val).image Subtype.val).card ≤ 7
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact equality_deletedColorClass_card_le_seven hcrit hc hnot v c _
  have hh := Finset.card_le_card (Finset.union_subset hMsub hPsub)
  rw [Finset.card_union_of_disjoint hdis, hP] at hh
  change M.card ≤ 5
  omega

end TaskH.Seven
#print axioms TaskH.Seven.exists_third_common_of_card_ge_three
#print axioms TaskH.Seven.multi_common_outside_color_is_noncommon
#print axioms TaskH.Seven.multiCommonPool
#print axioms TaskH.Seven.common_four_multi_color
#print axioms TaskH.Seven.common_four_multi_card_le_five
