import Research.Backfill.Paper7.C61PerronFiveThreeMoments

/-! Source-only exclusion of the nonempty-q part of the actual {2,3,5}
Perron-five branch. The obstruction uses only the exact load moments and
the proved Perron load cap. No parameter enumeration is used.
This file has not been compiled or formally accepted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61FiveThree
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open scoped BigOperators Classical

/-- Between the one-part square sum 100 and the largest split square sum
82, no partition of 10 can have square sum in the interval 84 through 90. -/
theorem no_sum10_square84_to90 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 10) (hlo : 84 ≤ squares 6 p)
    (hhi : squares 6 p ≤ 90) : False := by
  obtain ⟨M, _h0, hMP, hm, hl, hu⟩ :=
    maximum_moment_interval p 10 (squares 6 p) hP rfl
  have hloZ : (84 : ℤ) ≤ squares 6 p := by exact_mod_cast hlo
  have hhiZ : (squares 6 p : ℤ) ≤ 90 := by exact_mod_cast hhi
  norm_num at hMP hm hl hu
  have hM9 : 9 ≤ M := by omega
  have hcases : M = 9 ∨ M = 10 := by omega
  rcases hcases with hM | hM
  · rw [hM] at hu
    norm_num at hu
    omega
  · rw [hM] at hl
    norm_num at hl
    omega
#print axioms Paper7C61FiveThree.no_sum10_square84_to90

/-- The same six coordinates that satisfy the cap must contain a 22:
if their maximum were at most 21, the remaining-sum bound gives at most
562 for the square sum. -/
theorem sum32_square_ge568_has_coordinate22 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 32) (hS : 568 ≤ squares 6 p)
    (hcap : ∀ k, p k ≤ 22) : ∃ k, p k = 22 := by
  by_contra h
  have hcap21 : ∀ k, p k ≤ 21 := by
    intro k
    have hk := hcap k
    have hne : p k ≠ 22 := by
      intro he
      exact h ⟨k, he⟩
    omega
  obtain ⟨M, _h0, hhi, hm, hs⟩ :=
    capped_maximum_moment p 32 (squares 6 p) 21 hP rfl hcap21
  have hSZ : (568 : ℤ) ≤ squares 6 p := by exact_mod_cast hS
  norm_num at hhi hm hs
  have hlo : 18 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61FiveThree.sum32_square_ge568_has_coordinate22

theorem cap22_sum32_square568_to574_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 32) (hlo : 568 ≤ squares 6 p)
    (hhi : squares 6 p ≤ 574) (hcap : ∀ k, p k ≤ 22) : False := by
  obtain ⟨k, hk⟩ := sum32_square_ge568_has_coordinate22 p hP hlo hcap
  obtain ⟨r, hrP, hrS⟩ := erase_coordinate_moments p k
  rw [hP, hk] at hrP
  rw [hk] at hrS
  norm_num at hrS
  exact no_sum10_square84_to90 r (by omega) (by omega) (by omega)
#print axioms Paper7C61FiveThree.cap22_sum32_square568_to574_impossible

/-- Full exclusion of this actual spectral branch under the original
order and integrality assumptions. The support is only required to be
the actual nonempty q support; there is no supplied coverage premise. -/
theorem root_five_three_qpositive_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0)
    (hK : (Kq 6 q).Nonempty) : False := by
  have hc := (root_five_profile (actual p q) h5).1
  rw [h0, h1, h2] at hc
  obtain ⟨hbeta, _halpha, _hsum, hQlo, horder, _hpSupport, _hqSupport⟩ :=
    card_three_qpositive_data p q hn hG (by omega) hK
  obtain ⟨hL, hm⟩ := root_five_three_parameter_relations p q hn hG h5 h1 h2
  rw [h0, hbeta] at hL
  rw [hbeta] at hm
  have hL32 : totalP 6 p + totalQ 6 q = 32 := by omega
  have hQhi : totalQ 6 q ≤ 4 := by omega
  have hloadP : totalP 6 (fun k => p k + q k) = 32 := by
    simpa only [totalP, totalQ, Finset.sum_add_distrib] using hL32
  have hloadLo : 568 ≤ squares 6 (fun k => p k + q k) := by omega
  have hloadHi : squares 6 (fun k => p k + q k) ≤ 574 := by omega
  exact cap22_sum32_square568_to574_impossible (fun k => p k + q k)
    hloadP hloadLo hloadHi (no_six_load_le_twenty_two p q hn hG h5.2)
#print axioms Paper7C61FiveThree.root_five_three_qpositive_impossible

end Paper7C61FiveThree
