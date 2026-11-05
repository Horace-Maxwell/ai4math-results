import Research.Backfill.Paper7.EightCycleRank
import Research.Backfill.Paper7.B4MonodromyRigidity
import Research.Backfill.Paper7.B4UnitArithmetic

/-! NEW SOURCE ONLY. Exact compression of an eight-cycle with P support on
the even sites. The transfer identities retain the actual graph monodromy. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7B4Analytic Paper7C61Three
open scoped BigOperators Matrix Classical

theorem eight_alternating_sum (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) :
    (∑ i, p i) = p 0+p 2+p 4+p 6 := by
  have h1 := ho 1 (by decide)
  have h3 := ho 3 (by decide)
  have h5 := ho 5 (by decide)
  have h7 := ho 7 (by decide)
  simp [Fin.sum_univ_succ,h1,h3,h5,h7,Nat.add_assoc]
#print axioms Paper7EightCycle.eight_alternating_sum

theorem eight_alternating_conjugacy (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (m : ℝ) (hm : m ≠ 0) :
    realFourProduct (m^2-p 0-2) (m^2-p 2-2) (m^2-p 4-2) (m^2-p 6-2) =
      (!![1,0;-1,m] : Matrix (Fin 2) (Fin 2) ℝ) * Mono 8 p (fun _ => 0) m *
      (!![1,0;1/m,1/m] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h1 := ho 1 (by decide)
  have h3 := ho 3 (by decide)
  have h5 := ho 5 (by decide)
  have h7 := ho 7 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Mono,Tk,fk,realFourProduct,realTransfer,List.finRange_succ,
      h1,h3,h5,h7,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hm]
  all_goals ring
#print axioms Paper7EightCycle.eight_alternating_conjugacy

theorem eight_alternating_compressed_identity (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (m : ℝ) (hm : m ≠ 0)
    (hid : Mono 8 p (fun _ => 0) m = 1) :
    realFourProduct (m^2-p 0-2) (m^2-p 2-2) (m^2-p 4-2) (m^2-p 6-2) = 1 := by
  rw [eight_alternating_conjugacy p ho m hm,hid,mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hm]
  all_goals ring
#print axioms Paper7EightCycle.eight_alternating_compressed_identity

theorem eight_alternating_identity_order (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (m : ℝ) (hm : m ≠ 0)
    (hid : Mono 8 p (fun _ => 0) m = 1) :
    (nOf 8 p (fun _ => 0) : ℝ) = 4*m^2 := by
  obtain ⟨h02,h13,_⟩ := real_four_identity_data _ _ _ _
    (eight_alternating_compressed_identity p ho m hm hid)
  have hsum := eight_alternating_sum p ho
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,hsum]
  push_cast
  linarith only [h02,h13]
#print axioms Paper7EightCycle.eight_alternating_identity_order

theorem eight_alternating_unit_small (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0)
    (hunit : 1 ∈ spec (SG 8 p (fun _ => 0))) : nOf 8 p (fun _ => 0) ≤ 15 := by
  have hm : 0 < mult (SG 8 p (fun _ => 0)) 1 := Multiset.count_pos.mpr hunit
  have hk := Paper7MainReduction.qzero_unit_multiplicity_transfer 8 p (by decide)
  have hc := Paper7Lemma22.monodromy_kernel_classification 8 p (fun _ => 0) 1
  have htr : (Mono 8 p (fun _ => 0) 1).trace = 2 := by
    by_cases hh : Mono 8 p (fun _ => 0) 1 = 1
    · rw [hh]
      norm_num [Matrix.trace,Fin.sum_univ_two]
    · have hn : matrixNullity (Mono 8 p (fun _ => 0) 1-1) = 1 := by
        have hne := mt hc.2.1.mp hh
        omega
      exact (hc.2.2.mp hn).2
  have he := eight_alternating_conjugacy p ho 1 (by norm_num)
  have htrace : (realFourProduct (1-p 0-2) (1-p 2-2) (1-p 4-2) (1-p 6-2)).trace = 2 := by
    norm_num only [one_pow,div_one] at he
    rw [he,Matrix.trace_mul_cycle]
    have hCC : (!![1,0;1,1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1,0;-1,1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
    rw [hCC,one_mul]
    exact htr
  rw [real_four_trace] at htrace
  have hprodR : ((p 0 : ℝ)+1)*((p 2 : ℝ)+1)*((p 4 : ℝ)+1)*((p 6 : ℝ)+1) =
      (((p 0 : ℝ)+1)+((p 4 : ℝ)+1))*(((p 2 : ℝ)+1)+((p 6 : ℝ)+1)) := by
    nlinarith only [htrace]
  have hprod : (p 0+1)*(p 2+1)*(p 4+1)*(p 6+1) =
      ((p 0+1)+(p 4+1))*((p 2+1)+(p 6+1)) := by exact_mod_cast hprodR
  have hbound := positive_unit_product_sum_le_eleven (p 0+1) (p 2+1)
    (p 4+1) (p 6+1) (by omega) (by omega) (by omega) (by omega) hprod
  have hsum := eight_alternating_sum p ho
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,hsum]
  omega
#print axioms Paper7EightCycle.eight_alternating_unit_small

end Paper7EightCycle
