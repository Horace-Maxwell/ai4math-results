import Research.Backfill.Paper7.C61HigherProfileRemainder

/-! Source-only analytic exclusion of the entire {2,2,5} profile.
No parameter-tuple search or executable certificate is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small
open scoped BigOperators Classical

theorem cap22_sum27_square_ge513_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 27) (hS : 513 ≤ squares 6 p)
    (hc : ∀ k, p k ≤ 22) : False := by
  obtain ⟨M, _h0, hhi, hm, hs⟩ :=
    capped_maximum_moment p 27 (squares 6 p) 22 hP rfl hc
  have hSZ : (513 : ℤ) ≤ squares 6 p := by exact_mod_cast hS
  norm_num at hhi hm hs
  have hlo : 19 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum27_square_ge513_impossible

theorem cap22_sum28_square528_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 28) (hS : squares 6 p = 528)
    (hc : ∀ k, p k ≤ 22) : False := by
  obtain ⟨M, _h0, hhi, hm, hs⟩ := capped_maximum_moment p 28 528 22 hP hS hc
  norm_num at hhi hm hs
  have hlo : 19 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum28_square528_impossible

theorem no_sum7_square41 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 7) (hS : squares 6 p = 41) : False := by
  obtain ⟨M, h0, _hMP, hm, hl, hu⟩ := maximum_moment_interval p 7 41 hP hS
  norm_num at hm hl hu
  have hlo : 6 ≤ M := by omega
  have hhi : M ≤ 6 := by
    by_contra h
    have h7 : 7 ≤ M := by omega
    have hp := mul_nonneg (sub_nonneg.mpr h7) h0
    nlinarith
  have heq : M = 6 := by omega
  rw [heq] at hu
  norm_num at hu
#print axioms Paper7C61Higher.no_sum7_square41

theorem cap22_sum29_square525_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 29) (hS : squares 6 p = 525)
    (hc : ∀ k, p k ≤ 22) : False := by
  obtain ⟨k, _hk, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 6)) p Finset.univ_nonempty
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) p (Finset.mem_univ k)
  have hsq := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => p j ^ 2) (Finset.mem_univ k)
  change (∑ j ∈ Finset.univ.erase k, p j) + p k = totalP 6 p at hsum
  change (∑ j ∈ Finset.univ.erase k, p j ^ 2) + p k ^ 2 = squares 6 p at hsq
  rw [hP] at hsum
  rw [hS] at hsq
  have hu := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ.erase k) (fun j _ => Nat.zero_le (p j))
  have hm : squares 6 p ≤ p k * totalP 6 p := by
    change (∑ j, p j ^ 2) ≤ p k * ∑ j, p j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using Nat.mul_le_mul_right (p j) (hmax j hj)
  rw [hP, hS] at hm
  have hklo : 19 ≤ p k := by omega
  have hkhi := hc k
  have hk22 : p k = 22 := by
    have hcases : p k = 19 ∨ p k = 20 ∨ p k = 21 ∨ p k = 22 := by omega
    rcases hcases with h19 | h20 | h21 | h22
    · have hA : (∑ j ∈ Finset.univ.erase k, p j) = 10 := by omega
      rw [hA] at hu
      rw [h19] at hsq
      norm_num at hu hsq
      omega
    · have hA : (∑ j ∈ Finset.univ.erase k, p j) = 9 := by omega
      rw [hA] at hu
      rw [h20] at hsq
      norm_num at hu hsq
      omega
    · have hA : (∑ j ∈ Finset.univ.erase k, p j) = 8 := by omega
      rw [hA] at hu
      rw [h21] at hsq
      norm_num at hu hsq
      omega
    · exact h22
  have hA : (∑ j ∈ Finset.univ.erase k, p j) = 7 := by omega
  have hB : (∑ j ∈ Finset.univ.erase k, p j ^ 2) = 41 := by
    rw [hk22] at hsq
    norm_num at hsq
    omega
  let r : Fin 6 → ℕ := fun j => if j = k then 0 else p j
  have hrk : r k = 0 := by simp [r]
  have hr (j : Fin 6) (hj : j ∈ Finset.univ.erase k) : r j = p j := by
    simp only [r, ite_eq_right (Finset.mem_erase.mp hj).1]
  have hsr := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) r (Finset.mem_univ k)
  have hsqr := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => r j ^ 2) (Finset.mem_univ k)
  have hAr : (∑ j ∈ Finset.univ.erase k, r j) = 7 := by
    calc
      _ = ∑ j ∈ Finset.univ.erase k, p j := Finset.sum_congr rfl hr
      _ = 7 := hA
  have hBr : (∑ j ∈ Finset.univ.erase k, r j ^ 2) = 41 := by
    calc
      _ = ∑ j ∈ Finset.univ.erase k, p j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hr j hj]
      _ = 41 := hB
  have hPr : totalP 6 r = 7 := by
    change (∑ j ∈ Finset.univ.erase k, r j) + r k = totalP 6 r at hsr
    rw [hAr, hrk] at hsr
    omega
  have hSr : squares 6 r = 41 := by
    change (∑ j ∈ Finset.univ.erase k, r j ^ 2) + r k ^ 2 = squares 6 r at hsqr
    rw [hBr, hrk] at hsqr
    norm_num at hsqr
    omega
  exact no_sum7_square41 r hPr hSr
#print axioms Paper7C61Higher.cap22_sum29_square525_impossible

/-- Full exclusion of this profile, for both zero and nonzero q. -/
theorem root_five_two_twos_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 2)
    (h1 : (actual p q 1).val = 0) (h2 : (actual p q 2).val = 0) : False := by
  have hload := no_six_load_le_twenty_two p q hn hG h5.2
  have hcap : ∀ k, p k ≤ 22 := by intro k; have := hload k; omega
  obtain ⟨hc, hs, hf⟩ := root_five_profile (actual p q) h5
  rw [h0, h1, h2] at hc hs hf
  by_cases hK : (Kq 6 q).Nonempty
  · obtain ⟨he, _ha, hsum, _hQ, horder, _hpc, _hqc⟩ :=
      card_three_qpositive_data p q hn hG (by omega) hK
    rw [hs] at hsum
    have hL : totalP 6 p + totalQ 6 q = 27 := by omega
    have hQhi : totalQ 6 q ≤ 9 := by omega
    have hm := profile_parameter_moment p q hn hG
    rw [hf] at hm
    norm_num at hm
    have hLZ : (totalP 6 p : ℤ) + totalQ 6 q = 27 := by exact_mod_cast hL
    have hQZ : (totalQ 6 q : ℤ) ≤ 9 := by exact_mod_cast hQhi
    have hS : 513 ≤ squares 6 (fun k => p k + q k) := by
      exact_mod_cast (by linarith : (513 : ℤ) ≤ squares 6 (fun k => p k + q k))
    have hPload : totalP 6 (fun k => p k + q k) = 27 := by
      simpa only [totalP, totalQ, Finset.sum_add_distrib] using hL
    exact cap22_sum27_square_ge513_impossible (fun k => p k + q k) hPload hS hload
  · have hq := zero_of_totalQ_zero 6 q
      (Paper7Rank.support_sum_zero 6 q (Finset.not_nonempty_iff_eq_empty.mp hK))
    have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
    have hel := qzero_unitExponent_lower p q hq
    have heu := unitExponent_le_eight p q
    have hsum := parameter_sum_eq_profile p q hn hG
    have hm := q_zero_moment p q hn hG hq
    rw [hf] at hm
    have hcases : unitExponent p q = 6 ∨ unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
    rcases hcases with he6 | he7 | he8
    · have hP : totalP 6 p = 27 := by omega
      have hS : 513 ≤ squares 6 p := by
        rw [hP] at hm
        norm_num at hm
        exact_mod_cast (by linarith : (513 : ℤ) ≤ squares 6 p)
      exact cap22_sum27_square_ge513_impossible p hP hS hcap
    · have hP : totalP 6 p = 28 := by omega
      have hS : squares 6 p = 528 := by
        rw [hP] at hm
        norm_num at hm
        exact_mod_cast (by linarith : (squares 6 p : ℤ) = 528)
      exact cap22_sum28_square528_impossible p hP hS hcap
    · have hP : totalP 6 p = 29 := by omega
      have hS : squares 6 p = 525 := by
        rw [hP] at hm
        norm_num at hm
        exact_mod_cast (by linarith : (squares 6 p : ℤ) = 525)
      exact cap22_sum29_square525_impossible p hP hS hcap
#print axioms Paper7C61Higher.root_five_two_twos_impossible

theorem root_five_contains_three (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (h5 : RootFive (actual p q)) :
    (actual p q 2).val = 0 ∧ (actual p q 1).val = 1 ∧
      ((actual p q 0).val = 1 ∨ (actual p q 0).val = 2) := by
  obtain ⟨h2, hs⟩ := root_five_remaining_shapes p q hp hn hG h5
  rcases hs with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact (root_five_two_twos_impossible p q hn hG h5 h0 h1 h2).elim
  · exact ⟨h2, h1, Or.inl h0⟩
  · exact ⟨h2, h1, Or.inr h0⟩
#print axioms Paper7C61Higher.root_five_contains_three

end Paper7C61Higher
