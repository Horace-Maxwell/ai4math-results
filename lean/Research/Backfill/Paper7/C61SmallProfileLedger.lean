import Research.Backfill.Paper7.C61SmallSquareObstructions
import Research.Backfill.Paper7.C61RootSixExclusion

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters
open scoped BigOperators Classical

def RootThree (m : Fin 5 → Fin 3) : Prop :=
  (m 1).val = 1 ∧ (m 2).val = 0 ∧ (m 3).val = 0 ∧ (m 4).val = 0
#print axioms Paper7C61Small.RootThree

def RootFour (m : Fin 5 → Fin 3) : Prop :=
  (m 2).val = 1 ∧ (m 3).val = 0 ∧ (m 4).val = 0
#print axioms Paper7C61Small.RootFour

theorem root_three_profile (m : Fin 5 → Fin 3) (h : RootThree m) :
    card m = (m 0).val + 1 ∧ square m = 4*(m 0).val+9 ∧
      fourth m = 12*((m 0).val : ℤ)+72 := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  constructor
  · norm_num [card, Fin.sum_univ_succ, h1,h2,h3,h4]
  constructor
  · norm_num [square, value, Fin.sum_univ_succ, h1,h2,h3,h4]
    ring
  · norm_num [fourth, value, Fin.sum_univ_succ, h1,h2,h3,h4]
    ring
#print axioms Paper7C61Small.root_three_profile

theorem root_four_profile (m : Fin 5 → Fin 3) (h : RootFour m) :
    card m = (m 0).val+(m 1).val+1 ∧
      square m = 4*(m 0).val+9*(m 1).val+16 ∧
      fourth m = 12*((m 0).val : ℤ)+72*((m 1).val : ℤ)+240 := by
  obtain ⟨h2,h3,h4⟩ := h
  constructor
  · norm_num [card, Fin.sum_univ_succ, h2,h3,h4]
    omega
  constructor
  · norm_num [square, value, Fin.sum_univ_succ, h2,h3,h4]
    ring
  · norm_num [fourth, value, Fin.sum_univ_succ, h2,h3,h4]
    ring
#print axioms Paper7C61Small.root_four_profile

theorem qzero_unitExponent_lower (p q : Fin 6 → ℕ) (hq : q = (fun _ => 0)) :
    6 ≤ unitExponent p q := by
  have hK : Kq 6 q = ∅ := by simp [hq, Kq]
  simp only [unitExponent, hK, Finset.card_empty, Nat.sub_zero]
  omega
#print axioms Paper7C61Small.qzero_unitExponent_lower

theorem alpha_six_support (p : Fin 6 → ℕ) (ha : zeroExponent p = 6) :
    (Kp 6 p).card ≤ 3 := by
  have hs := support_add_delta0_le_six p
  unfold zeroExponent at ha
  omega
#print axioms Paper7C61Small.alpha_six_support

theorem q_support_le_profile (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : (Kq 6 q).card ≤ card (actual p q) := by
  have hr := (Paper7Lemma21.check_Lemma21 6 p q (by decide)).2.2.1
  rw [Paper7Lemma41.integral_Ngt_one_eq_Bplus_card (SG 6 p q) hG,
    ← actual_card p q hn hG] at hr
  omega
#print axioms Paper7C61Small.q_support_le_profile

theorem load_squares_split (p q : Fin 6 → ℕ) :
    squares 6 p + squares 6 q ≤ squares 6 (fun k => p k + q k) := by
  change (∑ k, p k^2)+(∑ k, q k^2) ≤ ∑ k, (p k+q k)^2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _hk
  nlinarith [Nat.zero_le (p k * q k)]
#print axioms Paper7C61Small.load_squares_split

end Paper7C61Small
