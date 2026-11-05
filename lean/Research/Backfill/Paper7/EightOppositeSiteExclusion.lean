import Research.Backfill.Paper7.EightCycleRank
import Research.Backfill.Paper7.C61ThreeMonodromy

/-! NEW SOURCE ONLY. A surviving square-root-two eigenvalue excludes all
pendant parameters supported on one antipodal pair, without an order bound. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open Paper7C61Three
open scoped BigOperators Matrix Classical

theorem eight_trace_root (p q : Fin 8 → ℕ) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    (ht : (Mono 8 p q m).trace = 2) : m ∈ spec (SG 8 p q) := by
  have hc := (Paper7Lemma22.check_Lemma22 8 p q (by decide)).1 m hmn hm0 hm1
  have hpos : 0 < mult (SG 8 p q) m := by
    by_cases hid : Mono 8 p q m = 1
    · have hh := hc.2.2.1.mpr hid
      omega
    · have hh := hc.2.2.2.mpr ⟨hid,ht⟩
      omega
  exact Multiset.count_pos.mp hpos
#print axioms Paper7EightCycle.eight_trace_root

theorem quarter_root_two_block (m u : ℝ) (hm : m^2 = 2) :
    realTransfer m*realTransfer m*realTransfer m*realTransfer (m-u) =
      (!![-1,0;-u,-1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hm3 : m^3 = 2*m := by nlinarith only [congrArg (fun x : ℝ => m*x) hm]
  have hm4 : m^4 = 4 := by nlinarith only [congrArg (fun x : ℝ => x^2) hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realTransfer,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  all_goals simp only [hm,hm3,hm4]
  all_goals ring
#print axioms Paper7EightCycle.quarter_root_two_block

theorem eight_opposite_sites_nonintegral (p q : Fin 8 → ℕ)
    (hs : ∀ i : Fin 8, i ≠ 0 → i ≠ 4 → p i = 0 ∧ q i = 0) :
    ¬ IsIntegralGraph (SG 8 p q) := by
  intro hG
  let m : ℝ := Real.sqrt 2
  have hm : m^2 = 2 := Real.sq_sqrt (by norm_num)
  have hm0 : 0 ≤ m := Real.sqrt_nonneg 2
  have hmlo : 1 < m := by nlinarith only [hm,hm0]
  have hmhi : m < 2 := by nlinarith only [hm,hm0]
  have hf (i : Fin 8) (hi0 : i ≠ 0) (hi4 : i ≠ 4) : fk 8 p q m i = 0 := by
    obtain ⟨hp,hq⟩ := hs i hi0 hi4
    simp [fk,hp,hq]
  have hf1 := hf 1 (by decide) (by decide)
  have hf2 := hf 2 (by decide) (by decide)
  have hf3 := hf 3 (by decide) (by decide)
  have hf5 := hf 5 (by decide) (by decide)
  have hf6 := hf 6 (by decide) (by decide)
  have hf7 := hf 7 (by decide) (by decide)
  have hmono : Mono 8 p q m =
      (realTransfer m*realTransfer m*realTransfer m*realTransfer (m-fk 8 p q m 4))*
      (realTransfer m*realTransfer m*realTransfer m*realTransfer (m-fk 8 p q m 0)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Mono,Tk,List.finRange_succ,realTransfer,hf1,hf2,hf3,hf5,hf6,hf7,
        Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have htrace : (Mono 8 p q m).trace = 2 := by
    rw [hmono,quarter_root_two_block m _ hm,quarter_root_two_block m _ hm]
    norm_num [Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  have hmem := eight_trace_root p q m (by linarith) (by linarith) (by linarith) htrace
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG m hmem
  rw [hz] at hmlo hmhi
  have hzlo : (1 : ℤ) < z := by exact_mod_cast hmlo
  have hzhi : z < (2 : ℤ) := by exact_mod_cast hmhi
  omega
#print axioms Paper7EightCycle.eight_opposite_sites_nonintegral

end Paper7EightCycle
