import Research.Backfill.Paper7.C61ClearedProfile
import Research.Backfill.Paper7.SunTheta

/-! Source-only parameter moments. The C61 profile dependencies are pending;
the full fourth moment is taken from actual accepted graph identities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Parameters
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile
open scoped BigOperators Classical

def fourth (m : Fin 5 → Fin 3) : ℤ :=
  ∑ i, ((m i).val : ℤ) * (value i : ℤ) ^ 2 * ((value i : ℤ) ^ 2 - 1)
#print axioms Paper7C61Parameters.fourth

def squares (b : ℕ) (p : Fin b → ℕ) : ℕ := ∑ k, p k ^ 2
#print axioms Paper7C61Parameters.squares

theorem large_quartic_split (s : Multiset ℝ) :
    ((s.filter (fun x => 2 ≤ |x|)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
      ((s.filter (fun x => 2 ≤ x)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum +
      (((s.map (fun x => -x)).filter (fun x => 2 ≤ x)).map
        (fun x => x ^ 2 * (x ^ 2 - 1))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    by_cases hp : 2 ≤ x
    · have hn : ¬ 2 ≤ -x := by linarith
      have ha : 2 ≤ |x| := by rw [abs_of_nonneg (by linarith : 0 ≤ x)]; exact hp
      simp [hp, hn, ha, ih]
      ring
    · by_cases hn : 2 ≤ -x
      · have ha : 2 ≤ |x| := by rw [abs_of_nonpos (by linarith : x ≤ 0)]; exact hn
        simp [hp, hn, ha, ih]
        ring
      · have ha : ¬ 2 ≤ |x| := by
          apply not_le.mpr
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        simp [hp, hn, ha, ih]
#print axioms Paper7C61Parameters.large_quartic_split

theorem actual_fourth_eq_theta (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : fourth (actual p q) = Theta (SG 6 p q) := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG (by decide)).1
  have hneg := Paper7Admissible.map_neg_eq_of_count (spec (SG 6 p q)) hs
  have hsplit := large_quartic_split (spec (SG 6 p q))
  rw [hneg] at hsplit
  change ((bigEigs (SG 6 p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
    ((Bplus (SG 6 p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum +
    ((Bplus (SG 6 p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum at hsplit
  have hsum := bplus_sum p q hn hG (fun x => x ^ 2 * (x ^ 2 - 1))
  have hcast : (fourth (actual p q) : ℝ) =
      ((Bplus (SG 6 p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum := by
    simpa only [fourth, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_sub,
      Int.cast_one, Int.cast_natCast, mul_assoc] using hsum.symm
  have hm := Paper7SunMoments.sg_big_quartic_moment 6 p q (by decide) hG
  norm_num at hm
  have hr : (fourth (actual p q) : ℝ) = (Theta (SG 6 p q) : ℝ) := by linarith
  exact_mod_cast hr
#print axioms Paper7C61Parameters.actual_fourth_eq_theta

theorem theta_parameter_expansion (p q : Fin 6 → ℕ) :
    Theta (SG 6 p q) = (squares 6 (fun k => p k + q k) : ℤ) +
      3 * ((totalP 6 p : ℤ) + totalQ 6 q) + 12 + 2 * (totalQ 6 q : ℤ) := by
  have hpoint (k : Fin 6) : thetaV (p k) (q k) =
      ((p k + q k : ℕ) : ℤ) ^ 2 + 3 * ((p k + q k : ℕ) : ℤ) + 2 + 2 * (q k : ℤ) := by
    unfold thetaV
    push_cast
    ring
  rw [Paper7Setup.sg_theta 6 p q (by decide)]
  simp_rw [hpoint]
  simp only [squares, totalP, totalQ, Nat.cast_sum, Nat.cast_pow, Nat.cast_add,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
#print axioms Paper7C61Parameters.theta_parameter_expansion

theorem profile_parameter_moment (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    fourth (actual p q) = (squares 6 (fun k => p k + q k) : ℤ) +
      3 * ((totalP 6 p : ℤ) + totalQ 6 q) + 12 + 2 * (totalQ 6 q : ℤ) := by
  rw [actual_fourth_eq_theta p q hn hG, theta_parameter_expansion]
#print axioms Paper7C61Parameters.profile_parameter_moment

theorem fourth_c61 : fourth c61 = 408 := by
  norm_num [fourth, c61, value, Fin.sum_univ_succ]
#print axioms Paper7C61Parameters.fourth_c61

end Paper7C61Parameters
