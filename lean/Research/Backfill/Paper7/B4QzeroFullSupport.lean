import Research.Backfill.Paper7.B4QzeroUnitSpectrum
import Research.Backfill.Paper7.B4AdjacentPExclusion
import Research.Backfill.Paper7.AdmissibleMultisetCounts

/-! Source-only rank and moment restrictions for all four P1 sites positive.
The support hypothesis is the actual parameter support, not a coverage table. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem full_support_delta_zero (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    Kp 4 p = Finset.univ ∧ delta0 4 p = 0 := by
  have hK : Kp 4 p = Finset.univ := by ext i; simp [Kp,hp]
  refine ⟨hK,?_⟩
  have hne : (Finset.univ : Finset (Fin 4)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simp only [delta0,hK,hne,ite_false]
  unfold evenGaps
  have hf : (Finset.univ : Finset (Fin 4)).filter
      (fun k => ∃ d ∈ Finset.Icc 1 4, Even d ∧ ((finRotate 4)^d) k ∈ Finset.univ ∧
        ∀ d' ∈ Finset.Ico 1 d, ((finRotate 4)^d') k ∉ Finset.univ) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k _hk
    rintro ⟨d,hd,he,_hend,hinside⟩
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd2 : 2 ≤ d := by
      obtain ⟨e,he⟩ := he
      omega
    exact hinside 1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_univ _)
  rw [hf,Finset.card_empty]
#print axioms Paper7B4Analytic.full_support_delta_zero

theorem qzero_full_support_positive_card (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    (Bplus (SG 4 p (fun _ => 0))).card+mult (SG 4 p (fun _ => 0)) 1 = 4 := by
  obtain ⟨hK,hd⟩ := full_support_delta_zero p hp
  have hzero := (Paper7Lemma22.check_Lemma22 4 p (fun _ => 0) (by decide)).2.1
  rw [hK,hd] at hzero
  norm_num at hzero
  have he := Paper7Admissible.lemma24_counting_even 4 p (fun _ => 0)
    (by decide) hG (by decide)
  have hc := Paper7Counting.symmetric_spectrum_card (SG 4 p (fun _ => 0)) hG he.1
  change order 4 (pq 4 p (fun _ => 0)) = _ at hc
  rw [Paper7Setup.sg_order,← he.1 1] at hc
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero] at hc
  omega
#print axioms Paper7B4Analytic.qzero_full_support_positive_card

theorem qzero_big_count_le_one (p : Fin 4 → ℕ) (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) (x : ℝ) (hx : 2 ≤ x) :
    (Bplus (SG 4 p (fun _ => 0))).count x ≤ 1 := by
  have hh := qzero_ordinary_multiplicity_le_one p hn hG x hx
  simpa only [Bplus,mult,Multiset.count_filter,hx,ite_true] using hh
#print axioms Paper7B4Analytic.qzero_big_count_le_one

theorem integral_square_floor_twenty_five (s : Multiset ℝ)
    (h : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z) :
    25*(s.card : ℝ) ≤ Paper7Admissible.squareSum s+21*(s.count 2 : ℝ)+
      16*(s.count 3 : ℝ)+9*(s.count 4 : ℝ) := by
  classical
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simp [Paper7Admissible.squareSum]
  | @cons x s ih =>
    intro h
    have hi := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx2,hint⟩ := h x (Multiset.mem_cons_self x s)
    have hcard : ((x ::ₘ s).card : ℝ) = (s.card : ℝ)+1 := by simp
    have hsum : Paper7Admissible.squareSum (x ::ₘ s) = x^2+Paper7Admissible.squareSum s := by
      simp [Paper7Admissible.squareSum]
    by_cases h2 : x = 2
    · subst x
      norm_num [hcard,hsum,Multiset.count_cons] at ⊢
      linarith
    by_cases h3 : x = 3
    · subst x
      norm_num [hcard,hsum,Multiset.count_cons] at ⊢
      linarith
    by_cases h4 : x = 4
    · subst x
      norm_num [hcard,hsum,Multiset.count_cons] at ⊢
      linarith
    have hx5 : 5 ≤ x := by
      obtain ⟨z,rfl⟩ := hint
      have hz2 : (2 : ℤ) ≤ z := by exact_mod_cast hx2
      have hz2n : z ≠ 2 := by exact_mod_cast h2
      have hz3n : z ≠ 3 := by exact_mod_cast h3
      have hz4n : z ≠ 4 := by exact_mod_cast h4
      have hz5 : (5 : ℤ) ≤ z := by omega
      exact_mod_cast hz5
    have hc2 : (x ::ₘ s).count 2 = s.count 2 := Multiset.count_cons_of_ne (Ne.symm h2) s
    have hc3 : (x ::ₘ s).count 3 = s.count 3 := Multiset.count_cons_of_ne (Ne.symm h3) s
    have hc4 : (x ::ₘ s).count 4 = s.count 4 := Multiset.count_cons_of_ne (Ne.symm h4) s
    rw [hcard,hsum,hc2,hc3,hc4]
    nlinarith
#print axioms Paper7B4Analytic.integral_square_floor_twenty_five

theorem qzero_full_support_unit_required (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hn : nOf 4 p (fun _ => 0) ≤ 49) (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    1 ∈ spec (SG 4 p (fun _ => 0)) := by
  have hcard := qzero_full_support_positive_card p hp hG
  by_contra hh
  have hm : mult (SG 4 p (fun _ => 0)) 1 = 0 := Multiset.count_eq_zero.mpr hh
  have hc4 : (Bplus (SG 4 p (fun _ => 0))).card = 4 := by omega
  have hints : ∀ x ∈ Bplus (SG 4 p (fun _ => 0)), 2 ≤ x ∧ ∃ z : ℤ, x = z := by
    intro x hx
    obtain ⟨hmem,hx2⟩ := Multiset.mem_filter.mp hx
    exact ⟨hx2,Paper7Moments.integral_spec_entry _ hG x hmem⟩
  have hfloor := integral_square_floor_twenty_five (Bplus (SG 4 p (fun _ => 0))) hints
  have h2N := qzero_big_count_le_one p hn hG 2 (by norm_num)
  have h3N := qzero_big_count_le_one p hn hG 3 (by norm_num)
  have h4N := qzero_big_count_le_one p hn hG 4 (by norm_num)
  have h2 : ((Bplus (SG 4 p (fun _ => 0))).count 2 : ℝ) ≤ 1 := by exact_mod_cast h2N
  have h3 : ((Bplus (SG 4 p (fun _ => 0))).count 3 : ℝ) ≤ 1 := by exact_mod_cast h3N
  have h4 : ((Bplus (SG 4 p (fun _ => 0))).count 4 : ℝ) ≤ 1 := by exact_mod_cast h4N
  have hS := (Paper7Counting.lemma42_bounds 4 p (fun _ => 0) (by decide)
    (by decide) hG).1
  have hnR : (nOf 4 p (fun _ => 0) : ℝ) ≤ 49 := by exact_mod_cast hn
  change 25*((Bplus (SG 4 p (fun _ => 0))).card : ℝ) ≤ S2 (SG 4 p (fun _ => 0))+
    21*((Bplus (SG 4 p (fun _ => 0))).count 2 : ℝ)+
    16*((Bplus (SG 4 p (fun _ => 0))).count 3 : ℝ)+
    9*((Bplus (SG 4 p (fun _ => 0))).count 4 : ℝ) at hfloor
  rw [hc4] at hfloor
  norm_num at hfloor
  linarith
#print axioms Paper7B4Analytic.qzero_full_support_unit_required

theorem qzero_opposite_ones_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hones : (p 0 = 1 ∧ p 2 = 1) ∨ (p 1 = 1 ∧ p 3 = 1)) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  have hfactor : ∃ b d : ℕ, 0 < b ∧ 0 < d ∧
      (∑ i, p i) = b+d+2 ∧ ∀ t : ℝ,
      qzeroQuartic (p 0) (p 1) (p 2) (p 3) t =
        (t-1)*((t-1)*(t-b)*(t-d)-2*t*(2*t-b-d)) := by
    rcases hones with ⟨h0,h2⟩ | ⟨h1,h3⟩
    · refine ⟨p 1,p 3,hp 1,hp 3,?_,?_⟩
      · rw [Fin.sum_univ_four,h0,h2]; omega
      · intro t; rw [h0,h2]; norm_num [qzeroQuartic]; ring
    · refine ⟨p 0,p 2,hp 0,hp 2,?_,?_⟩
      · rw [Fin.sum_univ_four,h1,h3]; omega
      · intro t; rw [h1,h3]; norm_num [qzeroQuartic]; ring
  obtain ⟨b,d,hb,hd,hsum,hfac⟩ := hfactor
  by_cases hsmall : b+d ≤ 2
  · have hpend : 0 < ∑ i, p i := by omega
    have hn : nOf 4 p (fun _ => 0) ≤ 8 := by simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero]; omega
    exact qzero_small_order_nonintegral p hpend hn hG
  have hlarge : (2 : ℝ) < (b : ℝ)+d := by exact_mod_cast (show 2 < b+d by omega)
  let f : ℝ → ℝ := fun t => (t-1)*(t-b)*(t-d)-2*t*(2*t-b-d)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 = -((b : ℝ)*d) := by dsimp [f]; ring
  have hf1 : f 1 = 2*((b : ℝ)+d-2) := by dsimp [f]; ring
  have hbd : 0 < (b : ℝ)*d := mul_pos (by exact_mod_cast hb) (by exact_mod_cast hd)
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by rw [hf0,hf1]; constructor <;> linarith
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht.1
  have hsq : s^2 = t := Real.sq_sqrt ht.1.le
  have hs1 : s < 1 := by nlinarith [ht.2]
  have hpoly : qzeroQuartic (p 0) (p 1) (p 2) (p 3) (s^2) = 0 := by
    rw [hsq,hfac]
    change (t-1)*f t = 0
    rw [hft,mul_zero]
  have hmem := (qzero_ordinary_spec_iff p s (by linarith) (by linarith)
    (by linarith)).mpr hpoly
  exact integral_no_spec_between_zero_one p (fun _ => 0) hG s hs0 hs1 hmem
#print axioms Paper7B4Analytic.qzero_opposite_ones_nonintegral

end Paper7B4Analytic
