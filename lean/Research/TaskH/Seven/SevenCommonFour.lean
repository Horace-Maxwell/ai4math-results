import Research.TaskH.Seven.SevenCommonFourExcess

/-! Original h4 contradiction. The actual two split-leaf pools contribute
at least20 outside points with zero common incidence; on all remaining
points the actual common incidence is at most cardinality+5. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degreeTwelve_commonColors_card_ne_four
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.commonColors.card ≠ 4 := by
  classical
  intro hfour
  have hcommon : F.commonColors.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨gamma, hgamma, _hcolor⟩ := common_four_multi_color hcrit hc F hfour
  let O := ((insert v (G.neighborFinset v))ᶜ : Finset V)
  let P := (G.neighborFinset (F.leaf gamma 0).val).filter
    (fun z => z ∉ insert v (G.neighborFinset v))
  let Q := (G.neighborFinset (F.leaf gamma 1).val).filter
    (fun z => z ∉ insert v (G.neighborFinset v))
  let Y := P ∪ Q
  let D := O.filter (fun z => z ∉ Y)
  have hP : 10 ≤ P.card := split_leaf_outside_card_ge_ten hcrit hc hnot hv F hcommon gamma hgamma 0
  have hQ : 10 ≤ Q.card := split_leaf_outside_card_ge_ten hcrit hc hnot hv F hcommon gamma hgamma 1
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    have hmP := Finset.mem_filter.mp hzP
    have hmQ := Finset.mem_filter.mp hzQ
    have hzv : z ≠ v := by intro he; exact hmP.2 (Finset.mem_insert.mpr (Or.inl he))
    have ha : (gamma, (0 : Fin 2)) ∈ splitPoolHits F z :=
      (mem_splitPoolHits F z _).mpr ⟨hgamma, ((G.mem_neighborFinset _ z).mp hmP.1).symm⟩
    have hb : (gamma, (1 : Fin 2)) ∈ splitPoolHits F z :=
      (mem_splitPoolHits F z _).mpr ⟨hgamma, ((G.mem_neighborFinset _ z).mp hmQ.1).symm⟩
    have he := splitPoolHits_fst_injective hcrit hc hnot hv F hcommon ⟨z, hzv⟩ hmP.2 ha hb rfl
    have hh := congrArg Prod.snd he
    norm_num at hh
  have hY : 20 ≤ Y.card := by
    have he := Finset.card_union_of_disjoint hdis
    change 20 ≤ (P ∪ Q).card
    omega
  have hsub : Y ⊆ O := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact Finset.mem_compl.mpr (Finset.mem_filter.mp h).2
    · exact Finset.mem_compl.mpr (Finset.mem_filter.mp h).2
  have hzero : ∀ z ∈ Y, commonPoolHits F z = ∅ := by
    intro z hz
    have hzout := Finset.mem_compl.mp (hsub hz)
    have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
    have hhit : ∃ e : Fin 2, (gamma, e) ∈ splitPoolHits F z := by
      rcases Finset.mem_union.mp hz with h | h
      · exact ⟨0, (mem_splitPoolHits F z _).mpr
          ⟨hgamma, ((G.mem_neighborFinset _ z).mp (Finset.mem_filter.mp h).1).symm⟩⟩
      · exact ⟨1, (mem_splitPoolHits F z _).mpr
          ⟨hgamma, ((G.mem_neighborFinset _ z).mp (Finset.mem_filter.mp h).1).symm⟩⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have he := splitPoolHits_empty_at_commonRep_neighbor hcrit hc hnot hv F i
      ⟨z, hzv⟩ hzout ((mem_commonPoolHits F z i).mp hi)
    obtain ⟨e, hm⟩ := hhit
    rw [he] at hm
    exact Finset.notMem_empty (gamma, e) hm
  have hfilter : O.filter (fun z => z ∈ Y) = Y := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hp := Finset.card_filter_add_card_filter_not (s := O) (p := fun z => z ∈ Y)
  rw [hfilter] at hp
  change Y.card + D.card = O.card at hp
  have hsum : (∑ z ∈ O, (commonPoolHits F z).card) =
      ∑ z ∈ D, (commonPoolHits F z).card := by
    change _ = ∑ z ∈ O.filter (fun z => z ∉ Y), (commonPoolHits F z).card
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hzY : z ∈ Y
    · simp only [hzero z hzY, Finset.card_empty, ite_self]
    · rw [ite_eq_left hzY]
  have hDsub : D ⊆ ((insert v (G.neighborFinset v))ᶜ : Finset V) := Finset.filter_subset _ _
  have hhi := common_four_incidence_le_card_add_five hcrit hc hnot F hfour D hDsub
  rw [← hsum] at hhi
  have hlo := commonRep_total_outside_mantel_budget hcrit hc hnot hv F
  rw [hfour, common_outside_incidence_double_count] at hlo
  change 9 * 4 ≤ (∑ z ∈ O, (commonPoolHits F z).card) + 2 * (4 ^ 2 / 4) at hlo
  norm_num at hlo
  have hn := equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  change O.card ≤ 33 at hn
  omega

end TaskH.Seven
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_card_ne_four
