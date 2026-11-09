import Research.TaskE.ChallengeF
import Research.TaskE.SUniform
import Research.TaskE.PotentialLower

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma hcell_row_budget {a : ℕ} {q u : ℝ} (hq : 5 ≤ q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {c ζ : ℕ → ℝ} (hζ : ∀ i ≤ a, |ζ i| ≤ 1) (i : ℕ) :
    hcell (q - 1) u (tMulVec a 3 c i) (tMulVec a 3 ζ i) ≤
      2 * u * max 0 (rowAbsSum a 3 i - 2 * |tMulVec a 3 c i|) := by
  have hh := ICGGeneral.hcell_le hu0 hu1 (show u ≤ q - 1 by linarith)
    (tMulVec a 3 c i) (tMulVec a 3 ζ i)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * u)
  apply max_le_max le_rfl
  have hw := CodexPaper1.Prop31.tMulVec_abs_le_rowAbs a 3 ζ hζ i
  nlinarith [abs_nonneg (tMulVec a 3 c i)]

lemma hcell_terminal_nonpos {a : ℕ} (ha : 1 ≤ a) {q u : ℝ} (hq : 5 ≤ q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {c ζ : ℕ → ℝ} (hc : IsSignVec a c)
    (hζ : ∀ i ≤ a, |ζ i| ≤ 1) :
    hcell (q - 1) u (tMulVec a 3 c a) (tMulVec a 3 ζ a) ≤ 0 := by
  apply ICGGeneral.hcell_nonpos hu0 hu1 (by linarith)
  have hh := SProof.terminal_penalty_zero (p := (3 : ℝ)) (K := q - 1) ha
    (by norm_num) (by linarith) (by linarith) hc
  have hn : rowAbsSum a 3 a - (q - 1) * |tMulVec a 3 c a| ≤ 0 := by
    have hx := le_max_right 0 (rowAbsSum a 3 a - (q - 1) * |tMulVec a 3 c a|)
    linarith
  have hw := CodexPaper1.Prop31.tMulVec_abs_le_rowAbs a 3 ζ hζ a
  linarith

lemma psi_row_gain {a i : ℕ} (ha : 1 ≤ a) (hi : i < a) {q u : ℝ}
    (hq : 5 ≤ q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {c ζ : ℕ → ℝ}
    (hc : IsSignVec a c) (hζ : ∀ l ≤ a, |ζ l| ≤ 1) :
    ((q - 1) * (1 + u) - 4 * u) * DeltaC a 3 c +
        (2 * u * max 0 (rowAbsSum a 3 i - 2 * |tMulVec a 3 c i|) -
          hcell (q - 1) u (tMulVec a 3 c i) (tMulVec a 3 ζ i)) ≤ psi a 3 q u c ζ := by
  let pen : ℕ → ℝ := fun l => max 0 (rowAbsSum a 3 l - 2 * |tMulVec a 3 c l|)
  let h : ℕ → ℝ := fun l => hcell (q - 1) u (tMulVec a 3 c l) (tMulVec a 3 ζ l)
  have hgain : 2 * u * pen i - h i ≤ ∑ l ∈ range a, (2 * u * pen l - h l) := by
    apply single_le_sum _ (mem_range.mpr hi)
    intro l _hl
    exact sub_nonneg.mpr (hcell_row_budget hq hu0 hu1 hζ l)
  rw [sum_sub_distrib, ← mul_sum] at hgain
  have hb := SProof.penalty_bound a ha 3 (by norm_num) c hc
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * u by positivity)
  have ht := hcell_terminal_nonpos ha hq hu0 hu1 hc hζ
  change h a ≤ 0 at ht
  change (∑ l ∈ range a, pen l) ≤ 2 * DeltaC a 3 c at hb
  change 2 * u * (∑ l ∈ range a, pen l) ≤ 2 * u * (2 * DeltaC a 3 c) at hm
  unfold psi
  change _ ≤ (q - 1) * (1 + u) * DeltaC a 3 c - ∑ l ∈ range (a + 1), h l
  rw [sum_range_succ]
  change ((q - 1) * (1 + u) - 4 * u) * DeltaC a 3 c + (2 * u * pen i - h i) ≤ _
  nlinarith

lemma hcell_same_small {P u A B : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hAB : A ≤ B) :
    hcell P u A B = 2 * u * B - 2 * P * A := by
  have hB : 0 ≤ B := hA.trans hAB
  unfold hcell
  rw [abs_of_nonpos (by linarith : A - B ≤ 0), abs_of_nonneg (by positivity : 0 ≤ B + P * A),
    abs_of_nonneg hB, abs_of_nonneg hA]
  ring

lemma hcell_same_large {P u A B : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hBA : B ≤ A) :
    hcell P u A B = -2 * (P - u) * B := by
  have hA : 0 ≤ A := hB.trans hBA
  unfold hcell
  rw [abs_of_nonneg (by linarith : 0 ≤ A - B), abs_of_nonneg (by positivity : 0 ≤ B + P * A),
    abs_of_nonneg hB, abs_of_nonneg hA]
  ring

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.psi_row_gain
