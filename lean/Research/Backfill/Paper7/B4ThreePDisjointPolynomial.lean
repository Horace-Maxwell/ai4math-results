import Research.Backfill.Paper7.B4SinglePMixedPolynomial
import Research.Backfill.Paper7.B4ThreePUnitExclusion

/-! Source-only exact scalar polynomial for three positive P sites and Q
at the remaining site. No bounded parameter search is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def threePDisjointP (a b c : ℕ) : Fin 4 → ℕ := ![a,b,c,0]
#print axioms Paper7B4Analytic.threePDisjointP

def threePDisjointQ (d : ℕ) : Fin 4 → ℕ := ![0,0,0,d]
#print axioms Paper7B4Analytic.threePDisjointQ

def threePDisjointQuartic (a b c d t : ℝ) : ℝ :=
  (t-a)*(t-b)*(t-c)*(t-d-1)-
    (2*t-a-c)*((t-1)*(t-b)+t*(t-d-1))
#print axioms Paper7B4Analytic.threePDisjointQuartic

def threePDisjointDelta (a b c : ℝ) : ℝ :=
  (a-1)*(b-1)*(c-1)-a-c+2
#print axioms Paper7B4Analytic.threePDisjointDelta

theorem three_disjoint_mixed_factor (a b c d : ℕ) (t : ℝ) :
    mixedPolynomial (threePDisjointP a b c) (threePDisjointQ d) t =
      t*(t-1)^3*threePDisjointQuartic a b c d t := by
  unfold mixedPolynomial mixedLocalPolynomial threePDisjointQuartic
  norm_num [threePDisjointP,threePDisjointQ]
  ring
#print axioms Paper7B4Analytic.three_disjoint_mixed_factor

theorem three_disjoint_ordinary_spec_iff (a b c d : ℕ) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) ↔
      threePDisjointQuartic a b c d (m^2) = 0 := by
  rw [mixed_ordinary_spec_iff _ _ m hmn hm0 hm1,three_disjoint_mixed_factor]
  have hden : m^2-1 ≠ 0 := by
    intro hh
    have he : (m-1)*(m+1) = 0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp he with h | h
    · exact hm1 (by linarith)
    · exact hmn (by linarith)
  exact mul_eq_zero_iff_left (mul_ne_zero (pow_ne_zero 2 hm0) (pow_ne_zero 3 hden))
#print axioms Paper7B4Analytic.three_disjoint_ordinary_spec_iff

theorem three_disjoint_small_root_excludes (a b c d : ℕ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (ht : threePDisjointQuartic a b c d t = 0) :
    ¬ IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) := by
  apply mixed_small_root_nonintegral _ _ t ht0 ht1
  rw [three_disjoint_mixed_factor,ht,mul_zero]
#print axioms Paper7B4Analytic.three_disjoint_small_root_excludes

theorem three_disjoint_integral_delta_nonneg (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d))) :
    0 ≤ threePDisjointDelta a b c := by
  by_contra hh
  have hdelta : threePDisjointDelta a b c < 0 := lt_of_not_ge hh
  let H : ℝ → ℝ := fun t => threePDisjointQuartic a b c d t
  have h0 : H 0 = (a : ℝ)*b*c*((d : ℝ)+1)+((a : ℝ)+c)*b := by
    dsimp [H,threePDisjointQuartic]
    ring
  have h1 : H 1 = (d : ℝ)*threePDisjointDelta a b c := by
    dsimp [H,threePDisjointQuartic,threePDisjointDelta]
    ring
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH0 : 0 < H 0 := by rw [h0]; positivity
  have hH1 : H 1 < 0 := by rw [h1]; exact mul_neg_of_pos_of_neg hdR hdelta
  have hcont : Continuous H := by dsimp [H,threePDisjointQuartic]; fun_prop
  obtain ⟨t,ht0,ht1,hHt⟩ := open_unit_root_of_factor H H hcont
    (Or.inr ⟨hH0,hH1⟩) (fun _ h => h)
  exact three_disjoint_small_root_excludes a b c d t ht0 ht1 hHt hG
#print axioms Paper7B4Analytic.three_disjoint_integral_delta_nonneg

theorem three_disjoint_opposite_ones_nonintegral (b d : ℕ)
    (hb : 0 < b) (hd : 0 < d) :
    ¬ IsIntegralGraph (SG 4 (threePDisjointP 1 b 1) (threePDisjointQ d)) := by
  let J : ℝ → ℝ := fun t =>
    (t-1)*(t-b)*(t-d-1)-2*((t-1)*(t-b)+t*(t-d-1))
  have hfac (t : ℝ) : threePDisjointQuartic 1 b 1 d t = (t-1)*J t := by
    dsimp [J,threePDisjointQuartic]
    ring
  have h0 : J 0 = -(b : ℝ)*((d : ℝ)+3) := by dsimp [J]; ring
  have h1 : J 1 = 2*(d : ℝ) := by dsimp [J]; ring
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcont : Continuous J := by dsimp [J]; fun_prop
  have hsign : J 0 < 0 ∧ 0 < J 1 := by
    rw [h0,h1]
    constructor
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · positivity
  obtain ⟨t,ht0,ht1,hHt⟩ := open_unit_root_of_factor
    (threePDisjointQuartic 1 b 1 d) J hcont (Or.inl hsign) (by
      intro t ht
      rw [hfac,ht,mul_zero])
  exact three_disjoint_small_root_excludes 1 b 1 d t ht0 ht1
    (by simpa only [Nat.cast_one] using hHt)
#print axioms Paper7B4Analytic.three_disjoint_opposite_ones_nonintegral

theorem three_disjoint_small_equal_nonintegral (a b d : ℕ)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) :
    ¬ IsIntegralGraph (SG 4 (threePDisjointP a b a) (threePDisjointQ d)) := by
  intro hG
  let s : ℝ := Real.sqrt a
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have haR3 : (a : ℝ) ≤ 3 := by exact_mod_cast ha3
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsq : s^2 = (a : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 < s := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ 1-s by linarith) (show 0 ≤ s+1 by linarith)
    nlinarith only [hsq,haR,hp]
  have hs2 : s < 2 := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ s-2 by linarith) (show 0 ≤ s+2 by linarith)
    nlinarith only [hsq,haR3,hp]
  have hH : threePDisjointQuartic a b a d (s^2) = 0 := by
    rw [hsq]
    unfold threePDisjointQuartic
    ring
  have hmem := (three_disjoint_ordinary_spec_iff a b a d s
    (by linarith) (by linarith) (by linarith)).mpr hH
  exact integral_no_spec_between_one_two _ _ hG s hs1 hs2 hmem
#print axioms Paper7B4Analytic.three_disjoint_small_equal_nonintegral

end Paper7B4Analytic
