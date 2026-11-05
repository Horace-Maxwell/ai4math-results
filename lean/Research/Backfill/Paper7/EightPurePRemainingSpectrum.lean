import Research.Backfill.Paper7.EightRootThreeCongruence

/-! Source-only exact remaining pure-P spectrum. This is a proved reduction,
not a complete eight-cycle exclusion or an extra premise on a main check. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge Paper7C61Profile
open scoped BigOperators Classical

theorem simple_unit_profile_shapes (m : Fin 5 → Fin 3) (P : ℕ)
    (ha : Admissible m) (hc : card m = 4) (hs : square m+1 = 8+P)
    (hn : square m+1 ≤ 41) :
    (m = ![2,1,1,0,0] ∧ P = 26) ∨ (m = ![1,2,1,0,0] ∧ P = 31) := by
  have h0 := (m 0).isLt
  have h1 := (m 1).isLt
  have h2 := (m 2).isLt
  have h3 := (m 3).isLt
  have h4 := (m 4).isLt
  have hcard : card m = (m 0).val+(m 1).val+(m 2).val+(m 3).val+(m 4).val := by
    simp [card,Fin.sum_univ_succ,Nat.add_assoc]
  have hsq : square m = 4*(m 0).val+9*(m 1).val+16*(m 2).val+
      25*(m 3).val+36*(m 4).val := by
    norm_num [square,value,Fin.sum_univ_succ,Nat.mul_comm,Nat.add_assoc]
  rcases (admissible_iff_shapes m).mp ha with ⟨hm1,hm2,hm3,hm4⟩ |
    ⟨hm2,hm3,hm4⟩ | ⟨hm3,hm4,hh⟩ | ⟨hm4,hm3,hm2,hm1,hm0⟩
  · omega
  · by_cases hm0 : (m 0).val = 2
    · have hm1 : (m 1).val = 1 := by omega
      apply Or.inl
      refine ⟨?_,by omega⟩
      funext i
      apply Fin.ext
      fin_cases i <;> norm_num <;> first | assumption | exact Fin.ext (by assumption)
    · have hm0' : (m 0).val = 1 := by omega
      have hm1 : (m 1).val = 2 := by omega
      apply Or.inr
      refine ⟨?_,by omega⟩
      funext i
      apply Fin.ext
      fin_cases i <;> norm_num <;> first | assumption | exact Fin.ext (by assumption)
  · rcases hh with hh | hh <;> omega
  · omega
#print axioms Paper7EightCycle.simple_unit_profile_shapes

theorem eight_pure_p_remaining_profile (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    Paper7EightProfile.actual p (fun _ => 0) = ![2,1,1,0,0] ∧
      (∑ i, p i) = 26 ∧ mult (SG 8 p (fun _ => 0)) 1 = 1 ∧
      (Kp 8 p).card = delta0 8 p+2 := by
  have hu := eight_qzero_integral_unit_one p hp hn hG
  have hd := eight_qzero_integral_gap_strict p hp hn hG
  have hr := Paper7MainReduction.qzero_positive_rank_balance 8 p (by decide) (by decide) hG
  have hupper := (eight_big_card_bounds p (fun _ => 0) (by simpa using hp) hn hG).2
  have hc : (Bplus (SG 8 p (fun _ => 0))).card = 4 := by omega
  have hcard := Paper7EightProfile.actual_card p (fun _ => 0) (by omega) hG
  have hsize := Paper7EightProfile.qzero_size p (by omega) hG
  have hPbound : 8+(∑ i, p i) ≤ 41 := by simpa [nOf] using hn
  rw [hu] at hsize
  have ha := Paper7EightProfile.actual_admissible p (fun _ => 0)
    (by simpa using hp) (by omega) hG
  rcases simple_unit_profile_shapes (Paper7EightProfile.actual p (fun _ => 0)) (∑ i, p i)
      ha (by omega) hsize (by omega) with hgood | hbad
  · exact ⟨hgood.1,hgood.2,hu,by omega⟩
  · have hm : mult (SG 8 p (fun _ => 0)) 3 = 2 := by
      have he := Paper7EightProfile.actual_eq_mult p (fun _ => 0) (1 : Fin 5)
      rw [hbad.1] at he
      norm_num [value] at he
      omega
    have hdiv := eight_double_three_four_dvd_total p hm
    rw [hbad.2] at hdiv
    norm_num at hdiv
#print axioms Paper7EightCycle.eight_pure_p_remaining_profile

theorem eight_pure_p_remaining_monodromy (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    Mono 8 p (fun _ => 0) 2 = 1 ∧ Mono 8 p (fun _ => 0) 1 ≠ 1 ∧
      (Mono 8 p (fun _ => 0) 1).trace = 2 := by
  obtain ⟨hprofile,_hP,hu,_hd⟩ := eight_pure_p_remaining_profile p hp hn hG
  have hm2 : mult (SG 8 p (fun _ => 0)) 2 = 2 := by
    have hh := Paper7EightProfile.actual_eq_mult p (fun _ => 0) (0 : Fin 5)
    rw [hprofile] at hh
    norm_num [value] at hh
    omega
  have hid := ((Paper7Lemma22.check_Lemma22 8 p (fun _ => 0) (by decide)).1 2
    (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm2
  have hunit := Paper7MainReduction.qzero_unit_multiplicity_transfer 8 p (by decide)
  have hc := Paper7Lemma22.monodromy_kernel_classification 8 p (fun _ => 0) 1
  exact ⟨hid,hc.2.2.mp (by omega)⟩
#print axioms Paper7EightCycle.eight_pure_p_remaining_monodromy

end Paper7EightCycle
