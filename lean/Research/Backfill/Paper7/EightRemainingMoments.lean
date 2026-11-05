import Research.Backfill.Paper7.EightPurePRemainingSpectrum
import Research.Backfill.Paper7.EightMixedLoadBounds
import Research.Backfill.Paper7.C61ParameterMoments

/-! Source-only exact local load and fourth-moment constraints on the one
remaining pure-P spectrum. No finite parameter covering is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge Paper7C61Profile
open scoped BigOperators Classical

theorem eight_pure_p_remaining_card (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    (Bplus (SG 8 p (fun _ => 0))).card = 4 := by
  have hprofile := (eight_pure_p_remaining_profile p hp hn hG).1
  rw [← Paper7EightProfile.actual_card p (fun _ => 0) (by omega) hG,hprofile]
  norm_num [card,Fin.sum_univ_succ]
#print axioms Paper7EightCycle.eight_pure_p_remaining_card

theorem eight_pure_p_load_thirteen (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    ∀ i, p i ≤ 13 := by
  have hbound := (eight_four_spectral_floor p (fun _ => 0) (by simpa using hp)
    hn hG (eight_pure_p_remaining_card p hp hn hG)).2
  intro i
  simpa using eight_local_load_cap p (fun _ => 0) hbound i
#print axioms Paper7EightCycle.eight_pure_p_load_thirteen

theorem eight_pure_p_squares_two_four_two (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    (∑ i, p i^2) = 242 := by
  obtain ⟨hprofile,hP,_hu,_hd⟩ := eight_pure_p_remaining_profile p hp hn hG
  have hsym := (Paper7Admissible.lemma24_counting_even 8 p (fun _ => 0)
    (by decide) hG (by decide)).1
  have hneg := Paper7Admissible.map_neg_eq_of_count (spec (SG 8 p (fun _ => 0))) hsym
  have hsplit := Paper7C61Parameters.large_quartic_split (spec (SG 8 p (fun _ => 0)))
  rw [hneg] at hsplit
  change ((bigEigs (SG 8 p (fun _ => 0))).map (fun x => x^2*(x^2-1))).sum =
    ((Bplus (SG 8 p (fun _ => 0))).map (fun x => x^2*(x^2-1))).sum+
    ((Bplus (SG 8 p (fun _ => 0))).map (fun x => x^2*(x^2-1))).sum at hsplit
  have hf := Paper7PruningSpectrum.finite_count_sum (Bplus (SG 8 p (fun _ => 0)))
    (fun i : Fin 5 => (value i : ℝ)) value_injective
    (Paper7EightProfile.bplus_covered p (fun _ => 0) (by omega) hG) (fun x => x^2*(x^2-1))
  have hsum : ((Bplus (SG 8 p (fun _ => 0))).map (fun x => x^2*(x^2-1))).sum = 336 := by
    have he : ((Bplus (SG 8 p (fun _ => 0))).map (fun x => x^2*(x^2-1))).sum =
        ∑ i, ((Paper7EightProfile.actual p (fun _ => 0) i).val : ℝ)*
          ((value i : ℝ)^2*((value i : ℝ)^2-1)) := by
      simpa only [Paper7EightProfile.actual,nsmul_eq_mul] using hf
    rw [hprofile] at he
    norm_num [value,Fin.sum_univ_succ] at he
    exact he
  have hm := Paper7SunMoments.sg_big_quartic_moment 8 p (fun _ => 0) (by decide) hG
  norm_num at hm
  rw [hsum] at hsplit
  have ht : (Theta (SG 8 p (fun _ => 0)) : ℝ) = 336 := by linarith only [hsplit,hm]
  have htZ : Theta (SG 8 p (fun _ => 0)) = 336 := by exact_mod_cast ht
  have he : Theta (SG 8 p (fun _ => 0)) =
      ((∑ i, p i^2 : ℕ) : ℤ)+3*((∑ i, p i : ℕ) : ℤ)+16 := by
    rw [Paper7Setup.sg_theta 8 p (fun _ => 0) (by decide)]
    have hpoint (i : Fin 8) : thetaV (p i) 0 = (p i : ℤ)^2+3*(p i : ℤ)+2 := by
      norm_num [thetaV]
      ring
    simp_rw [hpoint]
    simp only [Nat.cast_sum,Nat.cast_pow,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rw [htZ,hP] at he
  omega
#print axioms Paper7EightCycle.eight_pure_p_squares_two_four_two

end Paper7EightCycle
