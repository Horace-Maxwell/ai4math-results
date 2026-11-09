import Research.TaskE.ChallengeC0
import Research.TaskE.FTail

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma repeat_abs_step {a k : ℕ} {g : ℕ → ℝ} (hg : IsSignVec a g) (hk : k < a)
    (he : g k = g (k + 1)) :
    |ICGGeneral.Zp 3 a g k| = (2 + |ICGGeneral.Zp 3 a g (k + 1)|) / 3 := by
  have hz := ICGGeneral.Zp_abs_eq (by norm_num : (2 : ℝ) ≤ 3) hg hk.le
  have hn := ICGGeneral.Zp_abs_eq (by norm_num : (2 : ℝ) ≤ 3) hg (show k + 1 ≤ a from hk)
  have hs : g k * g k = 1 := by rcases hg k hk.le with h | h <;> norm_num [h]
  rw [ICGGeneral.Zp_rec (by norm_num : (3 : ℝ) ≠ 0) a g hk] at hz ⊢
  rw [← he] at hn
  norm_num at hz
  nlinarith

lemma potential_step_budget {a k : ℕ} {g : ℕ → ℝ} (hg : IsSignVec a g) (hk : k < a) :
    (1 - ICGGeneral.nu 3 (k + 1) + (2 * ICGGeneral.nu 3 (k + 1) - 1) *
        |ICGGeneral.Zp 3 a g (k + 1)|) ≤
      (1 - ICGGeneral.nu 3 k + (2 * ICGGeneral.nu 3 k - 1) * |ICGGeneral.Zp 3 a g k|) +
        (if g k = g (k + 1) then
          2 * ICGGeneral.nu 3 (k + 1) * |ICGGeneral.Zp 3 a g (k + 1)| else 0) := by
  have hn : ICGGeneral.nu 3 (k + 1) = (2 - ICGGeneral.nu 3 k) / 3 := by
    rw [ICGGeneral.nu_succ]; norm_num
  by_cases he : g k = g (k + 1)
  · rw [ite_eq_left he, repeat_abs_step hg hk he]
    have hu := (ICGGeneral.nu_bounds (by norm_num : (2 : ℝ) ≤ 3) (k + 1)).2
    have hm := mul_nonneg (show 0 ≤ 1 - ICGGeneral.nu 3 (k + 1) by linarith)
      (abs_nonneg (ICGGeneral.Zp 3 a g (k + 1)))
    rw [hn] at hm ⊢
    nlinarith only [hm]
  · rw [ite_eq_right he, ICGEqualParity.Zp_step_alt (by norm_num : (2 : ℝ) ≤ 3) hg hk he]
    norm_num
    rw [hn]
    nlinarith

lemma potential_tail_budget {a : ℕ} {g : ℕ → ℝ} (hg : IsSignVec a g) :
    ∀ d k : ℕ, k + d = a →
      ICGGeneral.nu 3 a ≤
        (1 - ICGGeneral.nu 3 k + (2 * ICGGeneral.nu 3 k - 1) * |ICGGeneral.Zp 3 a g k|) +
          ∑ l ∈ Ico k a, (if g l = g (l + 1) then
            2 * ICGGeneral.nu 3 (l + 1) * |ICGGeneral.Zp 3 a g (l + 1)| else 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro k hk
    have hka : k = a := by omega
    subst k
    have hga : |g a| = 1 := by rcases hg a le_rfl with h | h <;> norm_num [h]
    rw [ICGGeneral.Zp_self, hga]
    simp
    ring_nf
    exact le_rfl
  | succ d ih =>
    intro k hk
    have hka : k < a := by omega
    have hi := ih (k + 1) (by omega)
    have hs := potential_step_budget hg hka
    have he : Ico k a = insert k (Ico (k + 1) a) := by
      ext l
      simp only [mem_Ico, mem_insert]
      omega
    rw [he, sum_insert (by simp)]
    linarith

lemma potential_tail_sum {a j : ℕ} {g : ℕ → ℝ} (hj : j < a) :
    (∑ l ∈ Ico (j + 1) a, (if g l = g (l + 1) then
      2 * ICGGeneral.nu 3 (l + 1) * |ICGGeneral.Zp 3 a g (l + 1)| else 0)) =
      2 * ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)| := by
  classical
  have _hj_use : j + 1 ≤ a := Nat.succ_le_of_lt hj
  have he : Ico (j + 1) a = (range a).filter (fun l => j < l) := by
    ext l
    simp only [mem_Ico, mem_filter, mem_range]
    omega
  rw [he, sum_filter, NA, sum_filter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro l hl
  have hla : l < a := mem_range.mp hl
  rw [CodexPaper1.Additional.mu_nat_eq_nu,
    CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a g l hla]
  by_cases hlj : j < l <;> by_cases hr : g l = g (l + 1) <;> simp [hlj, hr, mul_assoc]

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.potential_tail_budget
