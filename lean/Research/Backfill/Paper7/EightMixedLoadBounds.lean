import Research.Backfill.Paper7.EightUnitResidual
import Research.Backfill.Paper7.C61PerronDegreeBound

/-! NEW SOURCE ONLY. The actual simple Perron root and square budget force
root four, local load at most thirteen, and total P at least seventeen. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_four_spectral_floor (p q : Fin 8 → ℕ)
    (hp : 0 < ∑ i, (p i+q i)) (hn : nOf 8 p q ≤ 41)
    (hG : IsIntegralGraph (SG 8 p q)) (hc : (Bplus (SG 8 p q)).card = 4) :
    33 ≤ S2 (SG 8 p q) ∧ ∀ x ∈ spec (SG 8 p q), x ≤ 4 := by
  obtain ⟨r,hr,hsimple,hr3,hmax⟩ := Paper7Admissible.lemma24_perron 8 p q (by decide) hp hG
  have hrB : r ∈ Bplus (SG 8 p q) := Multiset.mem_filter.mpr ⟨hr,by linarith⟩
  have hints := Paper7Admissible.bplus_integral_entries 8 p q hG
  have hcounts := Paper7Admissible.bplus_count_le_two 8 p q (by decide)
  have hcountR : (Bplus (SG 8 p q)).count r = 1 := by
    simpa only [Bplus,mult,Multiset.count_filter,show (2 : ℝ) ≤ r from by linarith,ite_true] using hsimple
  have hr4 : 4 ≤ r := by
    by_contra hh
    have hrlt : r < 4 := lt_of_not_ge hh
    have hrval : r = 3 := by
      rcases Paper7Admissible.integer_between_two_four (hints r hrB).2
        (by linarith) hrlt with h2 | h3
      · linarith
      · exact h3
    have h23 : ∀ x ∈ Bplus (SG 8 p q), x = 2 ∨ x = 3 := by
      intro x hx
      have hxmem := (Multiset.mem_filter.mp hx).1
      have hxr := (le_abs_self x).trans (hmax x hxmem).1
      exact Paper7Admissible.integer_between_two_four (hints x hx).2 (hints x hx).1 (by linarith)
    have hcard := Paper7Admissible.card_of_two_three (Bplus (SG 8 p q)) h23
    rw [hrval] at hcountR
    have htwo := hcounts 2
    omega
  have hr2 : (2 : ℝ) ≠ r := by linarith
  have ht := Paper7Admissible.square_floor_sum ((Bplus (SG 8 p q)).erase r)
    (fun x hx => hints x (Multiset.mem_of_mem_erase hx))
  have htc : ((Bplus (SG 8 p q)).erase r).card = 3 := by
    have hh := Multiset.card_erase_add_one hrB
    omega
  have htwo : (((Bplus (SG 8 p q)).erase r).count 2 : ℝ) ≤ 2 := by
    rw [Multiset.count_erase_of_ne hr2]
    exact_mod_cast hcounts 2
  have hsum : r^2+Paper7Admissible.squareSum ((Bplus (SG 8 p q)).erase r) = S2 (SG 8 p q) := by
    simpa only [Paper7Admissible.squareSum,S2,Multiset.map_cons,Multiset.sum_cons] using
      congrArg Paper7Admissible.squareSum (Multiset.cons_erase hrB)
  rw [htc] at ht
  norm_num at ht
  have hfloor : r^2+17 ≤ S2 (SG 8 p q) := by linarith only [ht,htwo,hsum]
  have hs := (Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)).2.1
  have hu : (0 : ℝ) ≤ mult (SG 8 p q) 1 := Nat.cast_nonneg _
  have hnR : (nOf 8 p q : ℝ) ≤ 41 := by exact_mod_cast hn
  have hrval : r = 4 := by
    obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG r hr
    have hz4 : (4 : ℤ) ≤ z := by rw [hz] at hr4; exact_mod_cast hr4
    by_contra hne
    have hz5 : (5 : ℤ) ≤ z := by
      have hzne : z ≠ 4 := by intro he; rw [hz,he] at hne; exact hne rfl
      omega
    have hr5 : 5 ≤ r := by rw [hz]; exact_mod_cast hz5
    nlinarith only [hfloor,hs,hu,hnR,hr5]
  refine ⟨by rw [hrval] at hfloor; norm_num at hfloor; exact hfloor,?_⟩
  intro x hx
  have hh := (le_abs_self x).trans (hmax x hx).1
  rwa [hrval] at hh
#print axioms Paper7EightCycle.eight_four_spectral_floor

theorem eight_local_load_cap (p q : Fin 8 → ℕ)
    (hbound : ∀ x ∈ spec (SG 8 p q), x ≤ 4) (k : Fin 8) : p k+q k ≤ 13 := by
  let : Nonempty (SunV 8 (pq 8 p q)) := ⟨Sum.inl 0⟩
  obtain ⟨r,hr,v,hv,_hnorm,he,hr0,_hsimp,_hupper,_hdom⟩ :=
    Paper7Admissible.connected_perron (SG 8 p q)
      (Paper7Admissible.sun_connected 8 (pq 8 p q) (by decide))
  have hle := hbound r hr
  have hc1 : (SimpleGraph.cycleGraph 8).Adj k (k+1) := by fin_cases k <;> decide
  have hc2 : (SimpleGraph.cycleGraph 8).Adj (k+1) (k+2) := by fin_cases k <;> decide
  have hne : (k+2 : Fin 8) ≠ k := by fin_cases k <;> decide
  have ha := (Paper7Cleared.sun_cycle_adj_iff 8 (pq 8 p q) (by decide) k (k+1)).mpr hc1
  have hb := (Paper7Cleared.sun_cycle_adj_iff 8 (pq 8 p q) (by decide) (k+1) (k+2)).mpr hc2
  have hwi : (Sum.inl (k+2) : SunV 8 (pq 8 p q)) ≠ Sum.inl k := fun hh => hne (Sum.inl.inj hh)
  have hd := Paper7C61Higher.degree_lt_eigenvalue_sq (SG 8 p q) r v hv he _ _ _ ha hb hwi
  rw [Paper7Setup.sg_root_degree 8 p q (by decide) k] at hd
  have hsq : r^2 ≤ (16 : ℝ) := by nlinarith only [hr0,hle]
  have hload : (2+p k+q k : ℕ) < (16 : ℝ) := hd.trans_le hsq
  have hloadN : 2+p k+q k < 16 := by exact_mod_cast hload
  omega
#print axioms Paper7EightCycle.eight_local_load_cap

theorem eight_mixed_load_data (p q : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hn : nOf 8 p q ≤ 41)
    (hG : IsIntegralGraph (SG 8 p q)) :
    17 ≤ ∑ i, p i ∧ ∀ i, p i+q i ≤ 13 := by
  obtain ⟨hc,_hd,_hplus,_hminus,_hu,hS⟩ := eight_mixed_rank_saturated p q hp hq hn hG
  have hpq : 0 < ∑ i, (p i+q i) := by rw [Finset.sum_add_distrib]; omega
  obtain ⟨hfloor,hbound⟩ := eight_four_spectral_floor p q hpq hn hG hc
  have hnR : (nOf 8 p q : ℝ) ≤ 41 := by exact_mod_cast hn
  unfold nOf at hnR
  push_cast at hnR hS
  have hP : (17 : ℝ) ≤ (∑ i, p i : ℕ) := by push_cast; linarith only [hfloor,hS,hnR]
  exact ⟨by exact_mod_cast hP, eight_local_load_cap p q hbound⟩
#print axioms Paper7EightCycle.eight_mixed_load_data

end Paper7EightCycle
