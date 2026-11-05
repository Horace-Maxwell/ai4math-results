import Research.Backfill.Paper7.C61ProfileShapes
import Research.Backfill.Paper7.TwelveCycleUnitRank

/-! Source-only actual spectrum data for every ten-cycle with P₁ arms and
order at most 42. No root profile is an assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7TenCycle
open BackfillPaper7.Challenge Paper7C61Profile
open scoped BigOperators Classical

def actual (p : Fin 10 → ℕ) : Fin 5 → Fin 3 := fun i =>
  ⟨(Bplus (SG 10 p (fun _ => 0))).count (value i : ℝ),Nat.lt_succ_of_le
    (Paper7Admissible.bplus_count_le_two 10 p (fun _ => 0) (by decide) (value i))⟩
#print axioms Paper7TenCycle.actual

theorem actual_eq_mult (p : Fin 10 → ℕ) (i : Fin 5) :
    (actual p i).val = mult (SG 10 p (fun _ => 0)) (value i) := by
  exact Multiset.count_filter_of_pos (value_lower i)
#print axioms Paper7TenCycle.actual_eq_mult

theorem bplus_entry_le_six (p : Fin 10 → ℕ) (hn : nOf 10 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) (x : ℝ)
    (hx : x ∈ Bplus (SG 10 p (fun _ => 0))) : x ≤ 6 := by
  have hnonneg : ∀ y ∈ (Bplus (SG 10 p (fun _ => 0))).map (fun z => z^2),
      (0 : ℝ) ≤ y := by
    intro y hy
    obtain ⟨z,_hz,rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg z
  have hsq : x^2 ≤ S2 (SG 10 p (fun _ => 0)) :=
    Multiset.single_le_sum hnonneg (x^2) (Multiset.mem_map.mpr ⟨x,hx,rfl⟩)
  have hs := (Paper7Admissible.lemma24_counting_even 10 p (fun _ => 0)
    (by decide) hG (by decide)).2.1
  have hm : (0 : ℝ) ≤ mult (SG 10 p (fun _ => 0)) 1 := Nat.cast_nonneg _
  have hnR : (nOf 10 p (fun _ => 0) : ℝ) ≤ 42 := by exact_mod_cast hn
  obtain ⟨z,rfl⟩ := Paper7Moments.integral_spec_entry (SG 10 p (fun _ => 0))
    hG x (Multiset.mem_filter.mp hx).1
  by_contra hh
  have hz : (6 : ℤ) < z := by exact_mod_cast (lt_of_not_ge hh)
  have hz7 : (7 : ℝ) ≤ z := by exact_mod_cast (show (7 : ℤ) ≤ z by omega)
  nlinarith
#print axioms Paper7TenCycle.bplus_entry_le_six

theorem bplus_covered (p : Fin 10 → ℕ) (hn : nOf 10 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) :
    ∀ x ∈ Bplus (SG 10 p (fun _ => 0)), ∃ i : Fin 5, (value i : ℝ) = x := by
  intro x hx
  have h := Multiset.mem_filter.mp hx
  exact value_rep x (Paper7Moments.integral_spec_entry _ hG x h.1) h.2
    (bplus_entry_le_six p hn hG x hx)
#print axioms Paper7TenCycle.bplus_covered

theorem actual_card (p : Fin 10 → ℕ) (hn : nOf 10 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) :
    card (actual p) = (Bplus (SG 10 p (fun _ => 0))).card := by
  exact (Paper7PruningSpectrum.finite_count_card (Bplus (SG 10 p (fun _ => 0)))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p hn hG)).symm
#print axioms Paper7TenCycle.actual_card

theorem actual_square (p : Fin 10 → ℕ) (hn : nOf 10 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) :
    (square (actual p) : ℝ) = S2 (SG 10 p (fun _ => 0)) := by
  have hh := Paper7PruningSpectrum.finite_count_sum (Bplus (SG 10 p (fun _ => 0)))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p hn hG)
    (fun x => x^2)
  simpa only [square,S2,actual,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,nsmul_eq_mul]
    using hh.symm
#print axioms Paper7TenCycle.actual_square

theorem actual_admissible (p : Fin 10 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 10 p (fun _ => 0) ≤ 42) (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) :
    Admissible (actual p) := by
  have hL := Paper7Admissible.check_Lemma24 10 p (fun _ => 0) (by decide)
    (by simpa using hp) hG
  obtain ⟨r,hr,hsimple,hr3,hmax⟩ := hL.1
  obtain ⟨i,hi⟩ := value_rep r (Paper7Moments.integral_spec_entry _ hG r hr)
    (by linarith) (bplus_entry_le_six p hn hG r (Multiset.mem_filter.mpr ⟨hr,by linarith⟩))
  refine ⟨?_,?_,i,?_,?_,?_⟩
  · rw [actual_card p hn hG]
    exact ((Paper7Admissible.lemma24_small_even_counts 10 p (fun _ => 0)
      (by decide) hG (by decide)).2 hn).1
  · have hs := (Paper7Admissible.lemma24_counting_even 10 p (fun _ => 0)
      (by decide) hG (by decide)).2.1
    have hm : (0 : ℝ) ≤ mult (SG 10 p (fun _ => 0)) 1 := Nat.cast_nonneg _
    have hnR : (nOf 10 p (fun _ => 0) : ℝ) ≤ 42 := by exact_mod_cast hn
    have hh : (square (actual p) : ℝ) ≤ 42 := by
      rw [actual_square p hn hG]
      linarith
    exact_mod_cast hh
  · rw [← hi] at hr3
    exact_mod_cast hr3
  · rw [actual_eq_mult,hi]
    exact hsimple
  · intro j hij
    rw [actual_eq_mult]
    apply Multiset.count_eq_zero_of_notMem
    intro hj
    have hjr : r < (value j : ℝ) := by
      rw [← hi]
      have hh : value i < value j := by unfold value; omega
      exact_mod_cast hh
    have hle := (le_abs_self (value j : ℝ)).trans (hmax (value j) hj).1
    linarith
#print axioms Paper7TenCycle.actual_admissible

theorem actual_size_rank (p : Fin 10 → ℕ) (hn : nOf 10 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 10 p (fun _ => 0))) :
    square (actual p)+mult (SG 10 p (fun _ => 0)) 1 = 10+∑ i, p i ∧
      square (actual p)+mult (SG 10 p (fun _ => 0)) 1 ≤ 42 ∧
      5 ≤ card (actual p)+mult (SG 10 p (fun _ => 0)) 1 := by
  have hs := (Paper7Admissible.lemma24_counting_even 10 p (fun _ => 0)
    (by decide) hG (by decide)).2.1
  rw [← actual_square p hn hG] at hs
  have hh : square (actual p)+mult (SG 10 p (fun _ => 0)) 1 = 10+∑ i, p i := by
    have hR : (square (actual p) : ℝ)+(mult (SG 10 p (fun _ => 0)) 1 : ℝ) =
        (nOf 10 p (fun _ => 0) : ℝ) := by linarith only [hs]
    have hN : square (actual p)+mult (SG 10 p (fun _ => 0)) 1 = nOf 10 p (fun _ => 0) := by
      exact_mod_cast hR
    simpa [nOf] using hN
  have hr := Paper7MainReduction.qzero_positive_rank_balance 10 p (by decide) (by decide) hG
  have hd := Paper7MainReduction.delta0_le_support_of_not_four_dvd 10 p (by decide)
  rw [← actual_card p hn hG] at hr
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero] at hn
  exact ⟨hh,by omega,by omega⟩
#print axioms Paper7TenCycle.actual_size_rank

theorem rank_five_saturates (p : Fin 10 → ℕ)
    (hn : nOf 10 p (fun _ => 0) ≤ 42) (hG : IsIntegralGraph (SG 10 p (fun _ => 0)))
    (hr : card (actual p)+mult (SG 10 p (fun _ => 0)) 1 = 5) :
    delta0 10 p = (Kp 10 p).card := by
  have hh := Paper7MainReduction.qzero_positive_rank_balance 10 p (by decide) (by decide) hG
  rw [← actual_card p hn hG] at hh
  omega
#print axioms Paper7TenCycle.rank_five_saturates

end Paper7TenCycle
