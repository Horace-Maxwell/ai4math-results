import Research.TaskH.Seven.SevenCommonRepOutside

/-! The h=1 and h=2 actual pool budgets. One common representative pool is
removed from the real outside domain; separation gives zero leaf incidence
there, and the remaining vertices have the proved s-1 capacity. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degreeTwelve_commonColors_not_one_or_two
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c)
    (hcase : F.commonColors.card = 1 ∨ F.commonColors.card = 2) : False := by
  classical
  have hcommon : F.commonColors.Nonempty := Finset.card_pos.mp (by rcases hcase with h | h <;> omega)
  obtain ⟨rho, hrho⟩ := hcommon
  have hcommon : F.commonColors.Nonempty := ⟨rho, hrho⟩
  let ri : ↥F.commonColors := ⟨rho, hrho⟩
  let r := F.commonRep ri
  let O := ((insert v (G.neighborFinset v))ᶜ : Finset V)
  let X := (G.neighborFinset r.val).filter (fun z => z ∉ insert v (G.neighborFinset v))
  let D := O.filter (fun z => z ∉ X)
  have hXsub : X ⊆ O := by
    intro z hz
    exact Finset.mem_compl.mpr (Finset.mem_filter.mp hz).2
  have hXlower : 11 ≤ X.card + 2 * F.commonColors.card :=
    commonRep_outside_card_lower hcrit hc hnot hv F ri
  have hXzero : ∀ z ∈ X, splitPoolHits F z = ∅ := by
    intro z hz
    have hm := Finset.mem_filter.mp hz
    have hzv : z ≠ v := by intro he; exact hm.2 (Finset.mem_insert.mpr (Or.inl he))
    exact splitPoolHits_empty_at_commonRep_neighbor hcrit hc hnot hv F ri
      ⟨z, hzv⟩ hm.2 ((G.mem_neighborFinset r.val z).mp hm.1).symm
  have hefilter : O.filter (fun z => z ∈ X) = X := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hXsub h, h⟩⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := O) (p := fun z => z ∈ X)
  rw [hefilter] at hpart
  change X.card + D.card = O.card at hpart
  have hcomp : F.commonColors.card + (F.commonColorsᶜ).card = 5 := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl F.commonColors
  have hsplit : 2 ≤ (F.commonColorsᶜ).card := by rcases hcase with h | h <;> omega
  have hcap : ∀ z ∈ D, (splitPoolHits F z).card ≤ 4 - F.commonColors.card := by
    intro z hz
    have hzO := (Finset.mem_filter.mp hz).1
    have hzout := Finset.mem_compl.mp hzO
    have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
    have hh := splitPoolHits_card_lt_splitColors hcrit hc hnot hv F hcommon hsplit
      ⟨z, hzv⟩ hzout
    change (splitPoolHits F z).card < (F.commonColorsᶜ).card at hh
    rcases hcase with h | h <;> omega
  have hsum : (∑ z ∈ O, (splitPoolHits F z).card) =
      ∑ z ∈ D, (splitPoolHits F z).card := by
    change _ = ∑ z ∈ O.filter (fun z => z ∉ X), (splitPoolHits F z).card
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hzX : z ∈ X
    · simp only [hXzero z hzX, Finset.card_empty, ite_self]
    · rw [ite_eq_left hzX]
  have hhi : (∑ z ∈ O, (splitPoolHits F z).card) ≤ D.card * (4 - F.commonColors.card) := by
    rw [hsum]
    calc
      _ ≤ ∑ _z ∈ D, (4 - F.commonColors.card) := Finset.sum_le_sum hcap
      _ = _ := by simp
  have hlo := split_leaf_outside_incidence_lower hcrit hc hnot hv F hcommon
  change 20 * (F.commonColorsᶜ).card ≤ ∑ z ∈ O, (splitPoolHits F z).card at hlo
  have hn := equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  change O.card ≤ 33 at hn
  rcases hcase with h | h
  · rw [h] at hXlower hhi hcomp
    norm_num only at hXlower hhi hcomp
    omega
  · rw [h] at hXlower hhi hcomp
    norm_num only at hXlower hhi hcomp
    omega

end TaskH.Seven
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_not_one_or_two
