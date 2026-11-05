import Research.Backfill.Paper7.C61ProfileShapes
import Research.Backfill.Paper7.EightCycleRank

/-! Source-only finite encoding of the actual eight-cycle spectrum, with
coverage and Perron shape proved from the original graph assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightProfile
open BackfillPaper7.Challenge Paper7C61Profile
open scoped BigOperators Classical

def actual (p q : Fin 8 → ℕ) : Fin 5 → Fin 3 := fun i =>
  ⟨(Bplus (SG 8 p q)).count (value i : ℝ),Nat.lt_succ_of_le
    (Paper7Admissible.bplus_count_le_two 8 p q (by decide) (value i))⟩
#print axioms Paper7EightProfile.actual

theorem actual_eq_mult (p q : Fin 8 → ℕ) (i : Fin 5) :
    (actual p q i).val = mult (SG 8 p q) (value i) := by
  exact Multiset.count_filter_of_pos (value_lower i)
#print axioms Paper7EightProfile.actual_eq_mult

theorem bplus_entry_le_six (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) (x : ℝ) (hx : x ∈ Bplus (SG 8 p q)) : x ≤ 6 := by
  have hnonneg : ∀ y ∈ (Bplus (SG 8 p q)).map (fun z => z^2), (0 : ℝ) ≤ y := by
    intro y hy
    obtain ⟨z,_hz,rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg z
  have hsq : x^2 ≤ S2 (SG 8 p q) :=
    Multiset.single_le_sum hnonneg (x^2) (Multiset.mem_map.mpr ⟨x,hx,rfl⟩)
  have hs := (Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)).2.1
  have hm : (0 : ℝ) ≤ mult (SG 8 p q) 1 := Nat.cast_nonneg _
  have hnR : (nOf 8 p q : ℝ) ≤ 42 := by exact_mod_cast hn
  obtain ⟨z,rfl⟩ := Paper7Moments.integral_spec_entry _ hG x (Multiset.mem_filter.mp hx).1
  by_contra hh
  have hz : (6 : ℤ) < z := by exact_mod_cast (lt_of_not_ge hh)
  have hz7 : (7 : ℝ) ≤ z := by exact_mod_cast (show (7 : ℤ) ≤ z by omega)
  nlinarith
#print axioms Paper7EightProfile.bplus_entry_le_six

theorem bplus_covered (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) :
    ∀ x ∈ Bplus (SG 8 p q), ∃ i : Fin 5, (value i : ℝ) = x := by
  intro x hx
  have h := Multiset.mem_filter.mp hx
  exact value_rep x (Paper7Moments.integral_spec_entry _ hG x h.1) h.2
    (bplus_entry_le_six p q hn hG x hx)
#print axioms Paper7EightProfile.bplus_covered

theorem actual_card (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) : card (actual p q) = (Bplus (SG 8 p q)).card := by
  exact (Paper7PruningSpectrum.finite_count_card (Bplus (SG 8 p q))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p q hn hG)).symm
#print axioms Paper7EightProfile.actual_card

theorem actual_square (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 42)
    (hG : IsIntegralGraph (SG 8 p q)) : (square (actual p q) : ℝ) = S2 (SG 8 p q) := by
  have hh := Paper7PruningSpectrum.finite_count_sum (Bplus (SG 8 p q))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p q hn hG) (fun x => x^2)
  simpa only [square,S2,actual,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,nsmul_eq_mul] using hh.symm
#print axioms Paper7EightProfile.actual_square

theorem actual_admissible (p q : Fin 8 → ℕ) (hp : 0 < ∑ i, (p i+q i))
    (hn : nOf 8 p q ≤ 42) (hG : IsIntegralGraph (SG 8 p q)) : Admissible (actual p q) := by
  obtain ⟨r,hr,hsimple,hr3,hmax⟩ := (Paper7Admissible.check_Lemma24 8 p q (by decide) hp hG).1
  obtain ⟨i,hi⟩ := value_rep r (Paper7Moments.integral_spec_entry _ hG r hr)
    (by linarith) (bplus_entry_le_six p q hn hG r (Multiset.mem_filter.mpr ⟨hr,by linarith⟩))
  refine ⟨?_,?_,i,?_,?_,?_⟩
  · rw [actual_card p q hn hG]
    exact ((Paper7Admissible.lemma24_small_even_counts 8 p q (by decide) hG (by decide)).2 hn).1
  · have hs := (Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)).2.1
    have hm : (0 : ℝ) ≤ mult (SG 8 p q) 1 := Nat.cast_nonneg _
    have hnR : (nOf 8 p q : ℝ) ≤ 42 := by exact_mod_cast hn
    have hh : (square (actual p q) : ℝ) ≤ 42 := by rw [actual_square p q hn hG]; linarith
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
#print axioms Paper7EightProfile.actual_admissible

theorem qzero_size (p : Fin 8 → ℕ) (hn : nOf 8 p (fun _ => 0) ≤ 42)
    (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    square (actual p (fun _ => 0))+mult (SG 8 p (fun _ => 0)) 1 = 8+∑ i, p i := by
  have hs := (Paper7Admissible.lemma24_counting_even 8 p (fun _ => 0)
    (by decide) hG (by decide)).2.1
  rw [← actual_square p (fun _ => 0) hn hG] at hs
  have hR : (square (actual p (fun _ => 0)) : ℝ)+(mult (SG 8 p (fun _ => 0)) 1 : ℝ) =
      (nOf 8 p (fun _ => 0) : ℝ) := by linarith only [hs]
  have hN : square (actual p (fun _ => 0))+mult (SG 8 p (fun _ => 0)) 1 = nOf 8 p (fun _ => 0) := by
    exact_mod_cast hR
  simpa [nOf] using hN
#print axioms Paper7EightProfile.qzero_size

end Paper7EightProfile
