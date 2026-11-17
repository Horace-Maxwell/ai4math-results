import Research.TaskH.Seven.SevenCommonMateSeparation

/-! h5 fails in the original graph: actual representative incidence is at
least33, but a disjoint actual mate pool of at least5 leaves at most28
outside points for that incidence, each of capacity one. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degreeTwelve_commonColors_card_ne_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.commonColors.card ≠ 5 := by
  classical
  intro hfive
  have hcommon : F.commonColors.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hcommon
  let ji : ↥F.commonColors := ⟨j, hj⟩
  let O := ((insert v (G.neighborFinset v))ᶜ : Finset V)
  let Y := (G.neighborFinset (F.commonMate ji).val).filter
    (fun z => z ∉ insert v (G.neighborFinset v))
  let D := O.filter (fun z => z ∉ Y)
  have hY : 5 ≤ Y.card := commonMate_outside_card_ge_five hcrit hc hnot hv F hfive ji
  have hsub : Y ⊆ O := by
    intro z hz
    exact Finset.mem_compl.mpr (Finset.mem_filter.mp hz).2
  have hzero : ∀ z ∈ Y, commonPoolHits F z = ∅ := by
    intro z hz
    have hm := Finset.mem_filter.mp hz
    have hzv : z ≠ v := by intro he; exact hm.2 (Finset.mem_insert.mpr (Or.inl he))
    exact commonPoolHits_empty_at_mate_neighbor (equality_rainbowSevenCycles hcrit hc)
      F (by omega) ji ⟨z, hzv⟩ hm.2
      ((G.mem_neighborFinset (F.commonMate ji).val z).mp hm.1).symm
  have hefilter : O.filter (fun z => z ∈ Y) = Y := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hp := Finset.card_filter_add_card_filter_not (s := O) (p := fun z => z ∈ Y)
  rw [hefilter] at hp
  change Y.card + D.card = O.card at hp
  have hcap : ∀ z ∈ D, (commonPoolHits F z).card ≤ 1 := by
    intro z hz
    have hzout := Finset.mem_compl.mp (Finset.mem_filter.mp hz).1
    have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
    exact commonPoolHits_card_le_one_of_card_five (equality_rainbowSevenCycles hcrit hc)
      F hfive ⟨z, hzv⟩ hzout
  have hsum : (∑ z ∈ O, (commonPoolHits F z).card) =
      ∑ z ∈ D, (commonPoolHits F z).card := by
    change _ = ∑ z ∈ O.filter (fun z => z ∉ Y), (commonPoolHits F z).card
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hzY : z ∈ Y
    · simp only [hzero z hzY, Finset.card_empty, ite_self]
    · rw [ite_eq_left hzY]
  have hhi : (∑ z ∈ O, (commonPoolHits F z).card) ≤ D.card := by
    rw [hsum]
    calc
      _ ≤ ∑ _z ∈ D, 1 := Finset.sum_le_sum hcap
      _ = _ := by simp
  have hlo := commonRep_total_outside_mantel_budget hcrit hc hnot hv F
  rw [hfive, common_outside_incidence_double_count] at hlo
  change 9 * 5 ≤ (∑ z ∈ O, (commonPoolHits F z).card) + 2 * (5 ^ 2 / 4) at hlo
  norm_num at hlo
  have hn := equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  change O.card ≤ 33 at hn
  omega

end TaskH.Seven
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_card_ne_five
