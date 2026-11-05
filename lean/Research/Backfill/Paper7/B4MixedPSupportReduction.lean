import Research.Backfill.Paper7.B4SinglePMixedExclusion

/-! Source-only consequence of the complete one-site and four-site P
exclusions. This is a proved restriction, not a premise of a main check. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem integral_genuinely_mixed_p_support (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hG : IsIntegralGraph (SG 4 p q)) :
    (Kp 4 p).card = 2 ∨ (Kp 4 p).card = 3 := by
  have hne : Kp 4 p ≠ ∅ := by
    intro hh
    have hz : p = (fun _ => 0) := by
      funext i
      have hi : ¬ 0 < p i := by
        intro hpi
        have hm : i ∈ Kp 4 p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpi⟩
        rw [hh] at hm
        exact Finset.notMem_empty i hm
      omega
    rw [hz] at hp
    simp at hp
  have hpos : 0 < (Kp 4 p).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hle : (Kp 4 p).card ≤ 4 := by
    simpa using (Kp 4 p).card_le_univ
  have hnot1 : (Kp 4 p).card ≠ 1 := by
    intro hh
    obtain ⟨i,hK⟩ := Finset.card_eq_one.mp hh
    have hpi : 0 < p i := by
      have hm : i ∈ Kp 4 p := by rw [hK]; simp
      exact (Finset.mem_filter.mp hm).2
    have hother : ∀ j : Fin 4, j ≠ i → p j = 0 := by
      intro j hji
      by_contra hj
      have hposj : 0 < p j := Nat.pos_of_ne_zero hj
      have hm : j ∈ Kp 4 p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hposj⟩
      rw [hK] at hm
      exact hji (Finset.mem_singleton.mp hm)
    exact single_p_site_mixed_nonintegral p q i hpi hother hq hG
  have hnot4 : (Kp 4 p).card ≠ 4 := by
    intro hh
    have hK : Kp 4 p = Finset.univ := (Kp 4 p).eq_univ_of_card (by simpa using hh)
    have hfull : ∀ i, 0 < p i := by
      intro i
      have hm : i ∈ Kp 4 p := by rw [hK]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hm).2
    exact full_p_mixed_sum_nonintegral p q hfull hq hG
  omega
#print axioms Paper7B4Analytic.integral_genuinely_mixed_p_support

theorem original_genuinely_mixed_p_support (L : Fin 4 → List ℕ)
    (hp : 0 < ∑ i, Paper7Normalize.countP1 4 L i)
    (hq : 0 < ∑ i, Paper7Normalize.countP2 4 L i)
    (hG : IsIntegralGraph (sunGraph 4 L)) :
    (Kp 4 (Paper7Normalize.countP1 4 L)).card = 2 ∨
      (Kp 4 (Paper7Normalize.countP1 4 L)).card = 3 := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  exact integral_genuinely_mixed_p_support p q hp hq hI
#print axioms Paper7B4Analytic.original_genuinely_mixed_p_support

end Paper7B4Analytic
