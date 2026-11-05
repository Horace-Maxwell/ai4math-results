import Research.Backfill.Paper7.EightRemainingMoments
import Research.Backfill.Paper7.C61IntegerRootProduct
import Research.Backfill.Paper7.ClearedCharacteristicPolynomial
import Research.Backfill.Paper7.EightCoreCancellation
import Research.Backfill.Paper7.EightCoreMatrixAlgebra
import Research.Backfill.Paper7.EightCoreDeterminantBridge

/-! Source-only characteristic and core polynomial of the actual remaining
eight-cycle case. Every spectral multiplicity is obtained from the graph. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7OddIntegral Paper7C61Profile
open scoped BigOperators Classical

theorem eight_integerSpectrum_neg (p q : Fin 8 → ℕ) (hG : IsIntegralGraph (SG 8 p q)) :
    (integerSpectrum (SG 8 p q)).map (fun z => -z) = integerSpectrum (SG 8 p q) := by
  apply Multiset.ext.mpr
  intro z
  have hs := (Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)).1
  have hc := Multiset.count_map_eq_count' (fun z : ℤ => -z)
    (integerSpectrum (SG 8 p q)) neg_injective (-z)
  have hsym : (integerSpectrum (SG 8 p q)).count (-z) =
      (integerSpectrum (SG 8 p q)).count z := by
    rw [integerSpectrum_count _ hG,integerSpectrum_count _ hG]
    simpa only [Int.cast_neg,neg_neg] using hs (-(z : ℝ))
  simpa only [neg_neg] using hc.trans hsym
#print axioms Paper7EightCycle.eight_integerSpectrum_neg

theorem eight_integer_positive_prod (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) (f : ℤ → Polynomial ℤ) :
    (((integerSpectrum (SG 8 p q)).filter (fun z => 2 ≤ z)).map f).prod =
      ∏ i : Fin 5, f (value i) ^ (Paper7EightProfile.actual p q i).val := by
  have hinj : Function.Injective (fun i : Fin 5 => (value i : ℤ)) := by
    intro i j hij
    change (value i : ℤ) = (value j : ℤ) at hij
    apply value_injective
    change (value i : ℝ) = (value j : ℝ)
    exact_mod_cast hij
  have hcover : ∀ z ∈ (integerSpectrum (SG 8 p q)).filter (fun z => 2 ≤ z),
      ∃ i : Fin 5, (value i : ℤ) = z := by
    intro z hz
    obtain ⟨hzs,hz2⟩ := Multiset.mem_filter.mp hz
    have hreal : (z : ℝ) ∈ spec (SG 8 p q) := by
      rw [← integerSpectrum_cast _ hG]
      exact Multiset.mem_map.mpr ⟨z,hzs,rfl⟩
    have h2 : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    obtain ⟨i,hi⟩ := Paper7EightProfile.bplus_covered p q hn hG z
      (Multiset.mem_filter.mpr ⟨hreal,h2⟩)
    exact ⟨i,by exact_mod_cast hi⟩
  rw [finite_count_prod _ (fun i : Fin 5 => (value i : ℤ)) hinj hcover f]
  apply Finset.prod_congr rfl
  intro i _
  have h2 : (2 : ℤ) ≤ value i := by unfold value; omega
  have hc : ((integerSpectrum (SG 8 p q)).filter (fun z => 2 ≤ z)).count (value i : ℤ) =
      (Paper7EightProfile.actual p q i).val := by
    rw [Multiset.count_filter_of_pos h2,integerSpectrum_count _ hG,
      Paper7EightProfile.actual_eq_mult]
    norm_cast
  rw [hc]
#print axioms Paper7EightCycle.eight_integer_positive_prod

theorem eight_graphPhi_profile (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) :
    graphPhi (SG 8 p q) = X ^ mult (SG 8 p q) 0 *
      (X^2-1) ^ mult (SG 8 p q) 1 * polynomial (Paper7EightProfile.actual p q) := by
  have hs := (Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)).1
  rw [graphPhi_integer_root_product _ hG,integer_product_partition,
    eight_integerSpectrum_neg p q hG,eight_integer_positive_prod p q hn hG,
    eight_integer_positive_prod p q hn hG]
  have hc0 : (integerSpectrum (SG 8 p q)).count 0 = mult (SG 8 p q) 0 := by
    simpa using integerSpectrum_count (SG 8 p q) hG 0
  have hc1 : (integerSpectrum (SG 8 p q)).count 1 = mult (SG 8 p q) 1 := by
    simpa using integerSpectrum_count (SG 8 p q) hG 1
  have hcn : (integerSpectrum (SG 8 p q)).count (-1) = mult (SG 8 p q) 1 := by
    have hc : (integerSpectrum (SG 8 p q)).count (-1) = mult (SG 8 p q) (-1) := by
      simpa using integerSpectrum_count (SG 8 p q) hG (-1)
    exact hc.trans (hs 1).symm
  rw [hc0,hc1,hcn]
  have hunit : (X-1 : Polynomial ℤ)*(X+1) = X^2-1 := by ring
  have hlarge :
      (∏ i : Fin 5, (X-C (value i : ℤ)) ^ (Paper7EightProfile.actual p q i).val)*
      (∏ i : Fin 5, (X+C (value i : ℤ)) ^ (Paper7EightProfile.actual p q i).val) =
        polynomial (Paper7EightProfile.actual p q) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow]
    congr 1
    rw [map_pow]
    ring
  calc
    _ = X ^ mult (SG 8 p q) 0 *
        ((X-1) ^ mult (SG 8 p q) 1*(X+1) ^ mult (SG 8 p q) 1)*
        ((∏ i : Fin 5, (X-C (value i : ℤ)) ^ (Paper7EightProfile.actual p q i).val)*
          (∏ i : Fin 5, (X+C (value i : ℤ)) ^ (Paper7EightProfile.actual p q i).val)) := by ring
    _ = _ := by rw [← mul_pow,hunit,hlarge]
#print axioms Paper7EightCycle.eight_graphPhi_profile

theorem eight_remaining_graphPhi (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    graphPhi (SG 8 p (fun _ => 0)) =
      X^24*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16) := by
  obtain ⟨hprofile,hP,hu,hd⟩ := eight_pure_p_remaining_profile p hp hn hG
  have hzero := (Paper7Lemma22.check_Lemma22 8 p (fun _ => 0) (by decide)).2.1
  have hz : mult (SG 8 p (fun _ => 0)) 0 = 24 := by omega
  rw [eight_graphPhi_profile p (fun _ => 0) (by omega) hG,hz,hu,hprofile]
  norm_num [polynomial,value,Fin.prod_univ_succ]
  ring
#print axioms Paper7EightCycle.eight_remaining_graphPhi

def coreMatrix (p : Fin 8 → ℕ) : Matrix (Fin 8) (Fin 8) (Polynomial ℤ) :=
  fun i j => (if i = j then X^2-C (p i : ℤ) else 0)-X*C (cycleAdjZ 8 i j)
#print axioms Paper7EightCycle.coreMatrix

def coreF (p : Fin 8 → ℕ) : Polynomial ℤ := finCoreDet 8 (coreMatrix p)
#print axioms Paper7EightCycle.coreF

theorem coreF_function_eq :
    coreF = (fun p : Fin 8 → ℕ => finCoreDet 8 (coreMatrix p)) := rfl
#print axioms Paper7EightCycle.coreF_function_eq

theorem coreF_apply_eq (p : Fin 8 → ℕ) :
    coreF p = finCoreDet 8 (coreMatrix p) :=
  congrFun coreF_function_eq p
#print axioms Paper7EightCycle.coreF_apply_eq

theorem eight_cleared_core_entry (p : Fin 8 → ℕ) (i j : Fin 8) :
    clearedMatrix 8 p (fun _ => 0) i j =
      ((X : Polynomial ℤ)^2-(1 : Polynomial ℤ)) * coreMatrix p i j := by
  by_cases hij : i = j
  · subst j
    simpa [clearedMatrix,coreMatrix] using
      eight_core_diag_factor X (C (cycleAdjZ 8 i i)) (C (p i : ℤ))
  · simpa [clearedMatrix,coreMatrix,hij] using
      eight_core_off_factor X (C (cycleAdjZ 8 i j))
#print axioms Paper7EightCycle.eight_cleared_core_entry

theorem eight_cleared_core_matrix (p : Fin 8 → ℕ) :
    clearedMatrix 8 p (fun _ => 0) =
      ((X : Polynomial ℤ)^2-(1 : Polynomial ℤ)) • coreMatrix p := by
  funext i j
  change clearedMatrix 8 p (fun _ => 0) i j =
    ((X : Polynomial ℤ)^2-(1 : Polynomial ℤ)) * coreMatrix p i j
  exact eight_cleared_core_entry p i j
#print axioms Paper7EightCycle.eight_cleared_core_matrix

theorem eight_cleared_core (p : Fin 8 → ℕ) :
    clearedF 8 p (fun _ => 0) = (X^2-1)^8*coreF p := by
  calc
    clearedF 8 p (fun _ => 0) = (X^2-1)^8*finCoreDet 8 (coreMatrix p) :=
      clearedF_of_smul_eq 8 p (fun _ => 0) (coreMatrix p)
        ((X : Polynomial ℤ)^2-(1 : Polynomial ℤ)) (eight_cleared_core_matrix p)
    _ = (X^2-1)^8*coreF p :=
      congrArg (fun f : Polynomial ℤ => (X^2-1)^8*f) (coreF_apply_eq p).symm
#print axioms Paper7EightCycle.eight_cleared_core

theorem eight_remaining_coreF (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    coreF p = X^6*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16) := by
  have hP := (eight_pure_p_remaining_profile p hp hn hG).2.1
  have hid := Paper7Cleared.cleared_identity 8 p (fun _ => 0) (by decide)
  rw [eight_cleared_core,eight_remaining_graphPhi p hp hn hG] at hid
  have hp26 : totalP 8 p = 26 := hP
  have hq0 : totalQ 8 (fun _ => 0) = 0 := by simp [totalQ]
  rw [hp26,hq0,pow_zero,mul_one] at hid
  exact eight_core_cancel_shift (coreF p) hid
#print axioms Paper7EightCycle.eight_remaining_coreF

end Paper7EightCycle
