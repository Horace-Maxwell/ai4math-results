import Research.TaskE.SPenalty

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.SProof
open Finset BackfillPaper1.Challenge

lemma terminal_penalty_zero {a : ℕ} (ha : 1 ≤ a) {p K : ℝ} (hp : 3 ≤ p)
    (hK : 0 ≤ K) (hparam : p ≤ K * (p - 2))
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    max 0 (rowAbsSum a p a - K * |tMulVec a p c a|) = 0 := by
  have hp0 : 0 < p := by linarith
  have hm := row_abs_mass a ha p hp a le_rfl
  rw [ite_eq_left rfl] at hm
  rw [hm]
  apply max_eq_left
  apply sub_nonpos.mpr
  have hw : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  calc
    p ^ a = p ^ (a - 1) * p := hw
    _ ≤ p ^ (a - 1) * (K * (p - 2)) :=
      mul_le_mul_of_nonneg_left hparam (pow_nonneg hp0.le _)
    _ = K * (p ^ (a - 1) * (p - 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (terminal_lower ha hp hc) hK

lemma condS_two {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 5 ≤ p) : CondS a p 2 := by
  intro c hc hna
  have ht := terminal_penalty_zero (K := 2) ha (by linarith : 3 ≤ p)
    (by norm_num) (by linarith) hc
  rw [sum_range_succ, ht, add_zero]
  exact penalty_strict a ha p hp c hc hna

lemma condS_four {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 3 ≤ p) : CondS a p 4 := by
  intro c hc hna
  have ht := terminal_penalty_zero (K := 4) ha hp (by norm_num) (by linarith) hc
  rw [sum_range_succ, ht, add_zero]
  have hle : (∑ i ∈ range a, max 0 (rowAbsSum a p i - 4 * |tMulVec a p c i|)) ≤
      ∑ i ∈ range a, max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|) := by
    apply sum_le_sum
    intro i _hi
    apply max_le_max le_rfl
    linarith [abs_nonneg (tMulVec a p c i)]
  have hb := penalty_bound a ha p hp c hc
  have hd := deficit_pos ha hp hc hna
  exact lt_of_le_of_lt (hle.trans hb) (by linarith)

end SProof

theorem check_ConditionsSUniform : CodexPaper1.TaskE.Challenge.ConditionsSUniform := by
  intro a ha
  exact ⟨fun p hp => SProof.condS_two ha hp, fun p hp => SProof.condS_four ha hp⟩

end CodexPaper1.TaskE
#print axioms CodexPaper1.TaskE.SProof.terminal_penalty_zero
#print axioms CodexPaper1.TaskE.SProof.condS_two
#print axioms CodexPaper1.TaskE.SProof.condS_four
#print axioms CodexPaper1.TaskE.check_ConditionsSUniform
