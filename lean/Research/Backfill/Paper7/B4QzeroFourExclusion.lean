import Research.Backfill.Paper7.B4QzeroFullSupport
import Research.Backfill.Paper7.B4UnitArithmetic

/-! Source-only complete exclusion of q=0 with all four P1 loads positive
in the frozen order range. The exceptional root 1 is included. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem qzero_full_support_unit_order_bound (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (hunit : 1 ∈ spec (SG 4 p (fun _ => 0))) : nOf 4 p (fun _ => 0) ≤ 19 := by
  let a := p 0-1
  let b := p 1-1
  let c := p 2-1
  let d := p 3-1
  have h0 : p 0 = a+1 := by dsimp [a]; have hh := hp 0; omega
  have h1 : p 1 = b+1 := by dsimp [b]; have hh := hp 1; omega
  have h2 : p 2 = c+1 := by dsimp [c]; have hh := hp 2; omega
  have h3 : p 3 = d+1 := by dsimp [d]; have hh := hp 3; omega
  have hpoly := (qzero_unit_spec_iff p).mp hunit
  rw [h0,h1,h2,h3] at hpoly
  push_cast at hpoly
  have heR : (a : ℝ)*b*c*d = ((a : ℝ)+c)*((b : ℝ)+d) := by
    unfold qzeroQuartic at hpoly
    nlinarith only [hpoly]
  have he : a*b*c*d = (a+c)*(b+d) := by exact_mod_cast heR
  have hno02 : ¬ (a = 0 ∧ c = 0) := by
    rintro ⟨ha,hc⟩
    exact qzero_opposite_ones_nonintegral p hp
      (Or.inl ⟨by omega,by omega⟩) hG
  have hno13 : ¬ (b = 0 ∧ d = 0) := by
    rintro ⟨hb,hd⟩
    exact qzero_opposite_ones_nonintegral p hp
      (Or.inr ⟨by omega,by omega⟩) hG
  have hnz : a*b*c*d ≠ 0 := by
    intro hz
    rw [he] at hz
    rcases mul_eq_zero.mp hz with h02 | h13
    · exact hno02 ⟨by omega,by omega⟩
    · exact hno13 ⟨by omega,by omega⟩
  have ha : 0 < a := Nat.pos_of_ne_zero (by intro hz; apply hnz; simp [hz])
  have hb : 0 < b := Nat.pos_of_ne_zero (by intro hz; apply hnz; simp [hz])
  have hc : 0 < c := Nat.pos_of_ne_zero (by intro hz; apply hnz; simp [hz])
  have hd : 0 < d := Nat.pos_of_ne_zero (by intro hz; apply hnz; simp [hz])
  have hsum := positive_unit_product_sum_le_eleven a b c d ha hb hc hd he
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,Fin.sum_univ_four]
  omega
#print axioms Paper7B4Analytic.qzero_full_support_unit_order_bound

theorem qzero_four_positive_nonintegral (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hn : nOf 4 p (fun _ => 0) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  have hunit := qzero_full_support_unit_required p hp hn hG
  have hn19 := qzero_full_support_unit_order_bound p hp hG hunit
  have hmpos : 0 < mult (SG 4 p (fun _ => 0)) 1 := Multiset.count_pos.mpr hunit
  have hmle := qzero_unit_multiplicity_le_one p hG
  have hm : mult (SG 4 p (fun _ => 0)) 1 = 1 := by omega
  have hcard := qzero_full_support_positive_card p hp hG
  have hc3 : (Bplus (SG 4 p (fun _ => 0))).card = 3 := by omega
  have hints : ∀ x ∈ Bplus (SG 4 p (fun _ => 0)), 2 ≤ x ∧ ∃ z : ℤ, x = z := by
    intro x hx
    obtain ⟨hmem,hx2⟩ := Multiset.mem_filter.mp hx
    exact ⟨hx2,Paper7Moments.integral_spec_entry _ hG x hmem⟩
  have hfloor := Paper7Admissible.square_floor_sum (Bplus (SG 4 p (fun _ => 0))) hints
  have h2N := qzero_big_count_le_one p hn hG 2 (by norm_num)
  have h2 : ((Bplus (SG 4 p (fun _ => 0))).count 2 : ℝ) ≤ 1 := by exact_mod_cast h2N
  have hS := (Paper7Counting.lemma42_bounds 4 p (fun _ => 0) (by decide)
    (by decide) hG).1
  have hnR : (nOf 4 p (fun _ => 0) : ℝ) ≤ 19 := by exact_mod_cast hn19
  change 9*((Bplus (SG 4 p (fun _ => 0))).card : ℝ) ≤ S2 (SG 4 p (fun _ => 0))+
    5*((Bplus (SG 4 p (fun _ => 0))).count 2 : ℝ) at hfloor
  rw [hc3] at hfloor
  norm_num at hfloor
  linarith
#print axioms Paper7B4Analytic.qzero_four_positive_nonintegral

end Paper7B4Analytic
