import Research.Backfill.Paper7.Lemma44
import Research.Backfill.Paper7.Corollary43

/-! Source-only rank exclusion of all P₂ arms in the remaining ten- and
 twelve-cycle domains. No finite candidate set or transfer CRT is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem rank0_ten_forces_qzero (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (hn : nOf b p q ≤ 42) (hG : IsIntegralGraph (SG b p q))
    (hr0 : (10 : ℤ) ≤ (b : ℤ)+(Kp b p).card-delta0 b p) : q = (fun _ => 0) := by
  have hK : Kq b q = ∅ := by
    by_contra hh
    have hne := Finset.nonempty_iff_ne_empty.mpr hh
    have hcard : 0 < (Kq b q).card := Finset.card_pos.mpr hne
    have hbound := Paper7Rank.rank_sigma_nonempty b p q hb hG hne
    have hmono := Paper7Rank.sigmaSq_monotone hr0
    rw [Paper7Rank.sigmaSq_ten] at hmono
    have hmonoZ : (84 : ℤ) ≤ sigmaSq ((b : ℤ)+(Kp b p).card-delta0 b p) := by
      exact_mod_cast hmono
    omega
  funext i
  have hi : ¬ 0 < q i := by
    intro hpos
    have hm : i ∈ Kq b q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos⟩
    rw [hK] at hm
    exact Finset.notMem_empty i hm
  omega
#print axioms Paper7MainReduction.rank0_ten_forces_qzero

theorem delta0_le_support_of_not_four_dvd (b : ℕ) (p : Fin b → ℕ) (hb : ¬ 4 ∣ b) :
    delta0 b p ≤ (Kp b p).card := by
  by_cases hK : Kp b p = ∅
  · rw [delta0,ite_eq_left hK,ite_eq_right hb]
    exact Nat.zero_le _
  · exact Paper7Rank.delta0_le_card_of_nonempty b p (Finset.nonempty_iff_ne_empty.mpr hK)
#print axioms Paper7MainReduction.delta0_le_support_of_not_four_dvd

theorem large_nonfour_cycle_qzero (b : ℕ) (p q : Fin b → ℕ)
    (hb : 10 ≤ b) (hfour : ¬ 4 ∣ b) (hn : nOf b p q ≤ 42)
    (hG : IsIntegralGraph (SG b p q)) : q = (fun _ => 0) := by
  have hd := delta0_le_support_of_not_four_dvd b p hfour
  exact rank0_ten_forces_qzero b p q (by omega) hn hG (by omega)
#print axioms Paper7MainReduction.large_nonfour_cycle_qzero

theorem twelve_or_larger_cycle_qzero (b : ℕ) (p q : Fin b → ℕ)
    (hb : 12 ≤ b) (hn : nOf b p q ≤ 42) (hG : IsIntegralGraph (SG b p q)) :
    q = (fun _ => 0) := by
  have hd := Paper7Rank.delta0_le_card_add_two b p
  exact rank0_ten_forces_qzero b p q (by omega) hn hG (by omega)
#print axioms Paper7MainReduction.twelve_or_larger_cycle_qzero

theorem ten_or_twelve_cycle_qzero (b : ℕ) (p q : Fin b → ℕ)
    (hb : b = 10 ∨ b = 12) (hn : nOf b p q ≤ 42)
    (hG : IsIntegralGraph (SG b p q)) : q = (fun _ => 0) := by
  rcases hb with rfl | rfl
  · exact large_nonfour_cycle_qzero 10 p q (by decide) (by decide) hn hG
  · exact twelve_or_larger_cycle_qzero 12 p q (by decide) hn hG
#print axioms Paper7MainReduction.ten_or_twelve_cycle_qzero

theorem original_ten_or_twelve_no_p2 (b : ℕ) (L : Fin b → List ℕ)
    (hb : b = 10 ∨ b = 12) (hn : order b L ≤ 42)
    (hG : IsIntegralGraph (sunGraph b L)) :
    Paper7Normalize.countP2 b L = (fun _ => 0) := by
  have hb3 : 3 ≤ b := by rcases hb with rfl | rfl <;> omega
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 b L hb3 hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 b L
  let q := Paper7Normalize.countP2 b L
  let e : sunGraph b L ≃g SG b p q := Paper7Normalize.sunNormalizeIso b L hb3 hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order b L = order b (pq b p q) at hc
  rw [Paper7Setup.sg_order] at hc
  exact ten_or_twelve_cycle_qzero b p q hb (by omega) hI
#print axioms Paper7MainReduction.original_ten_or_twelve_no_p2

end Paper7MainReduction
