import Research.Backfill.Paper7.TenCycleActualSpectrum
import Research.Backfill.Paper7.TenCycleTransferCongruence

/-! Source-only arithmetic contradiction. The small tuple below is the
actual multiplicity function supplied by the preceding spectrum theorem;
the graph theorem has no profile or congruence premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7TenCycle
open BackfillPaper7.Challenge Paper7C61Profile
open scoped BigOperators Classical

theorem profile_congruences_inconsistent (m : Fin 5 → Fin 3) (u P : ℕ)
    (ha : Admissible m) (hu : u ≤ 2) (hr : 5 ≤ card m+u)
    (hs : square m+u = 10+P) (hn : square m+u ≤ 42)
    (hone : u = 2 → (4 : ℤ) ∣ (P : ℤ))
    (htwo : card m+u = 5 → (m 0).val = 2 → (4 : ℤ) ∣ 15-(P : ℤ))
    (hthree : card m+u = 5 → (m 1).val = 2 → (4 : ℤ) ∣ 40-(P : ℤ)) : False := by
  have h0 := (m 0).isLt
  have h1 := (m 1).isLt
  have h2 := (m 2).isLt
  have h3 := (m 3).isLt
  have h4 := (m 4).isLt
  have hc : card m = (m 0).val+(m 1).val+(m 2).val+(m 3).val+(m 4).val := by
    simp [card,Fin.sum_univ_succ,Nat.add_assoc]
  have hsq : square m = 4*(m 0).val+9*(m 1).val+16*(m 2).val+
      25*(m 3).val+36*(m 4).val := by
    norm_num [square,value,Fin.sum_univ_succ,Nat.mul_comm,Nat.add_assoc]
  have hshape := (admissible_iff_shapes m).mp ha
  rcases hshape with ⟨hm1,hm2,hm3,hm4⟩ | ⟨hm2,hm3,hm4⟩ |
    ⟨hm3,hm4,hh⟩ | ⟨hm4,hm3,hm2,hm1,hm0⟩
  · have hu2 : u = 2 := by omega
    have hm0 : (m 0).val = 2 := by omega
    have hr5 : card m+u = 5 := by omega
    obtain ⟨a,ha⟩ := hone hu2
    obtain ⟨b,hb⟩ := htwo hr5 hm0
    omega
  · by_cases hu2 : u = 2
    · obtain ⟨a,ha⟩ := hone hu2
      have hm1 : (m 1).val = 0 := by omega
      have hm0 : (m 0).val = 2 := by omega
      have hr5 : card m+u = 5 := by omega
      obtain ⟨b,hb⟩ := htwo hr5 hm0
      omega
    · by_cases hu1 : u = 1
      · by_cases hm0 : (m 0).val = 2
        · have hm1 : (m 1).val = 1 := by omega
          have hr5 : card m+u = 5 := by omega
          obtain ⟨b,hb⟩ := htwo hr5 hm0
          omega
        · have hm1 : (m 1).val = 2 := by omega
          have hr5 : card m+u = 5 := by omega
          obtain ⟨b,hb⟩ := hthree hr5 hm1
          omega
      · have hu0 : u = 0 := by omega
        have hm0 : (m 0).val = 2 := by omega
        have hr5 : card m+u = 5 := by omega
        obtain ⟨b,hb⟩ := htwo hr5 hm0
        omega
  · rcases hh with ⟨hm2,hm1⟩ | ⟨hm2,hm1,hm0⟩
    · have hu2 : u = 2 := by omega
      obtain ⟨a,ha⟩ := hone hu2
      omega
    · omega
  · omega
#print axioms Paper7TenCycle.profile_congruences_inconsistent

theorem pure_p_order_le_forty_two_nonintegral (p : Fin 10 → ℕ)
    (hp : 0 < ∑ i, p i) (hn : nOf 10 p (fun _ => 0) ≤ 42) :
    ¬ IsIntegralGraph (SG 10 p (fun _ => 0)) := by
  intro hG
  obtain ⟨hs,hn',hr⟩ := actual_size_rank p hn hG
  apply profile_congruences_inconsistent (actual p) (mult (SG 10 p (fun _ => 0)) 1)
    (∑ i, p i) (actual_admissible p hp hn hG)
    (Paper7MainReduction.qzero_unit_multiplicity_le_two 10 p (by decide)) hr hs hn'
  · exact unit_double_four_dvd_total p
  · intro hr5 hm0
    have hd := rank_five_saturates p hn hG hr5
    have hm : mult (SG 10 p (fun _ => 0)) 2 = 2 := by
      have hh := actual_eq_mult p (0 : Fin 5)
      norm_num [value] at hh
      omega
    have hh := saturated_double_congruence p hp hd 2 (by decide) hm
    norm_num at hh
    exact hh
  · intro hr5 hm1
    have hd := rank_five_saturates p hn hG hr5
    have hm : mult (SG 10 p (fun _ => 0)) 3 = 2 := by
      have hh := actual_eq_mult p (1 : Fin 5)
      norm_num [value] at hh
      omega
    have hh := saturated_double_congruence p hp hd 3 (by decide) hm
    norm_num at hh
    exact hh
#print axioms Paper7TenCycle.pure_p_order_le_forty_two_nonintegral

theorem pure_p_sum_le_thirty_two_nonintegral (p : Fin 10 → ℕ)
    (hp : 0 < ∑ i, p i) (hn : (∑ i, p i) ≤ 32) :
    ¬ IsIntegralGraph (SG 10 p (fun _ => 0)) := by
  apply pure_p_order_le_forty_two_nonintegral p hp
  simpa [nOf] using (show 10+(∑ i, p i) ≤ 42 by omega)
#print axioms Paper7TenCycle.pure_p_sum_le_thirty_two_nonintegral

theorem parameters_order_le_forty_two_nonintegral (p q : Fin 10 → ℕ)
    (hp : 0 < ∑ i, (p i+q i)) (hn : nOf 10 p q ≤ 42) : ¬ IsIntegralGraph (SG 10 p q) := by
  intro hG
  have hq := Paper7MainReduction.large_nonfour_cycle_qzero 10 p q
    (by decide) (by decide) hn hG
  rw [hq] at hp hn hG
  exact pure_p_order_le_forty_two_nonintegral p (by simpa using hp) hn hG
#print axioms Paper7TenCycle.parameters_order_le_forty_two_nonintegral

end Paper7TenCycle
