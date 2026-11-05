import Research.Backfill.Paper7.TransferCentralDeficit
import Research.Backfill.Paper7.EightActualProfile
import Research.Backfill.Paper7.EightCycleRemainingBranches

/-! Source-only exclusion of the complete double-unit-root pure-P branch.
The word descent applies to all nonnegative pendant multiplicities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge Paper7TransferModFour Paper7CentralWords Paper7C61Profile
open scoped BigOperators Matrix Classical

theorem real_word_identity_integer (l : List ℤ)
    (h : ((l.map (Int.castRingHom ℝ)).map transfer).prod = 1) : word l = 1 := by
  have he := transfer_product_map (Int.castRingHom ℝ) l
  rw [h] at he
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) he
  change ((word l i j : ℤ) : ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j at hh
  fin_cases i <;> fin_cases j <;> norm_num at hh ⊢
  all_goals exact_mod_cast hh
#print axioms Paper7EightCycle.real_word_identity_integer

theorem eight_double_unit_constraints (p : Fin 8 → ℕ)
    (hm : mult (SG 8 p (fun _ => 0)) 1 = 2) :
    (∑ i, p i) ≤ 26 ∧ (4 : ℤ) ∣ ((∑ i, p i : ℕ) : ℤ) := by
  have hid := Paper7MainReduction.qzero_unit_transfer_identity 8 p (by decide) hm
  let l : List ℤ := (List.finRange 8).reverse.map (fun i => 1-(p i : ℤ))
  have hprod : ((l.map (Int.castRingHom ℝ)).map transfer).prod = 1 := by
    have he : ((l.map (Int.castRingHom ℝ)).map transfer).prod = Mono 8 p (fun _ => 0) 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [l,transfer,Mono,Tk,fk,List.finRange_succ,Matrix.mul_apply,Fin.sum_univ_two]
    exact he.trans hid
  have hlen : l.length = 8 := by simp [l]
  have hupper : ∀ x ∈ l, x ≤ 1 := by
    intro x hx
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hx
    have hi : (0 : ℤ) ≤ p i := Int.natCast_nonneg _
    omega
  have hsum : l.sum = 8-((∑ i, p i : ℕ) : ℤ) := by
    norm_num [l,List.finRange_succ,Fin.sum_univ_succ]
    ring
  have hbound := central_deficit_bound l (by omega) hupper
    (Or.inl (real_word_identity_integer l hprod))
  rw [hlen,hsum] at hbound
  have hdiv := integer_transfer_identity_div_four l hprod
  have hadd : (l.map (fun x => x+1)).sum = 16-((∑ i, p i : ℕ) : ℤ) := by
    norm_num [l,List.finRange_succ,Fin.sum_univ_succ]
    ring
  rw [hadd] at hdiv
  obtain ⟨z,hz⟩ := hdiv
  exact ⟨by omega,⟨4-z,by omega⟩⟩
#print axioms Paper7EightCycle.eight_double_unit_constraints

theorem small_double_unit_profile_impossible (m : Fin 5 → Fin 3) (P : ℕ)
    (ha : Admissible m) (hc : 3 ≤ card m) (hs : square m+2 = 8+P)
    (hp : P ≤ 26) (hd : (4 : ℤ) ∣ (P : ℤ)) : False := by
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
  obtain ⟨z,hz⟩ := hd
  rcases (admissible_iff_shapes m).mp ha with ⟨hm1,hm2,hm3,hm4⟩ |
    ⟨hm2,hm3,hm4⟩ | ⟨hm3,hm4,hh⟩ | ⟨hm4,hm3,hm2,hm1,hm0⟩
  · omega
  · omega
  · rcases hh with hh | hh <;> omega
  · omega
#print axioms Paper7EightCycle.small_double_unit_profile_impossible

theorem eight_qzero_double_unit_nonintegral (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hm : mult (SG 8 p (fun _ => 0)) 1 = 2) :
    ¬ IsIntegralGraph (SG 8 p (fun _ => 0)) := by
  intro hG
  obtain ⟨hP,hd⟩ := eight_double_unit_constraints p hm
  have hsize := Paper7EightProfile.qzero_size p (by omega) hG
  rw [hm] at hsize
  have hc := (eight_big_card_bounds p (fun _ => 0) (by simpa using hp) hn hG).1
  rw [← Paper7EightProfile.actual_card p (fun _ => 0) (by omega) hG] at hc
  exact small_double_unit_profile_impossible (Paper7EightProfile.actual p (fun _ => 0)) (∑ i, p i)
    (Paper7EightProfile.actual_admissible p (fun _ => 0) (by simpa using hp) (by omega) hG)
    hc hsize hP hd
#print axioms Paper7EightCycle.eight_qzero_double_unit_nonintegral

theorem eight_qzero_integral_unit_one (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    mult (SG 8 p (fun _ => 0)) 1 = 1 := by
  have hpos : 0 < mult (SG 8 p (fun _ => 0)) 1 :=
    Multiset.count_pos.mpr (eight_qzero_integral_unit_required p hp hn hG)
  have hle := Paper7MainReduction.qzero_unit_multiplicity_le_two 8 p (by decide)
  have hne : mult (SG 8 p (fun _ => 0)) 1 ≠ 2 := by
    intro hm
    exact eight_qzero_double_unit_nonintegral p hp hn hm hG
  omega
#print axioms Paper7EightCycle.eight_qzero_integral_unit_one

end Paper7EightCycle
