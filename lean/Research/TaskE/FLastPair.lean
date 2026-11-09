import Research.TaskE.FTail

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma last_pair_F_lower {a : ℕ} (ha : 3 ≤ a) {q u m : ℝ}
    (hq : 5 ≤ q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hca : c a = sAlt a)
    (hprev : c (a - 1) = sAlt (a - 1)) :
    4 * (q - 1 - u) * m * (3 ^ (a - 1) * (3 - 1)) ≤
      psi a 3 q u c (fun i => m * sAlt i) := by
  have ha1 : 1 ≤ a := by omega
  have hj : a - 1 < a := by omega
  have hi : a - 1 - (a - 1) = 0 := by omega
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hs : sAlt (a - 1) = -sAlt a := by
    have hh := alt_succ (a - 1)
    rw [Nat.sub_add_cancel ha1] at hh
    linarith
  have hA : tMulVec a 3 c 0 = sAlt a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) c
    rw [hi, z_end ha1 c, hca, hprev, hs] at hh
    rw [hh]
    dsimp [L]
    ring
  have hD : tMulVec a 3 sAlt 0 = sAlt a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) sAlt
    rw [hi, z_end ha1 sAlt, hs] at hh
    rw [hh]
    dsimp [L]
    ring
  have hB : tMulVec a 3 (fun i => m * sAlt i) 0 = sAlt a * (2 * m * L) := by
    rw [CodexPaper1.Chain.tMulVec_scale_of_eq a 3 m _ sAlt (by intros; rfl), hD]
    ring
  have hε : sAlt a = 1 ∨ sAlt a = -1 := neg_one_pow_eq_or ℝ a
  have hh : hcell (q - 1) u (tMulVec a 3 c 0)
      (tMulVec a 3 (fun i => m * sAlt i) 0) = -4 * (q - 1 - u) * m * L := by
    rw [hA, hB, hcell_sign _ _ _ _ _ hε]
    have he := hcell_same_large (u := u) (P := q - 1) (A := 2 * L) (B := 2 * m * L)
      (by linarith) (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hm1 hL.le])
    nlinarith
  have hAbs : |tMulVec a 3 c 0| = 2 * L := by
    rw [hA, abs_mul, show |sAlt a| = 1 by simp [sAlt, abs_pow], one_mul,
      abs_of_pos (by positivity : 0 < 2 * L)]
  have hrow := SProof.row_abs_mass a ha1 3 (by norm_num) 0 (by omega)
  rw [ite_eq_right (by omega : (0 : ℕ) ≠ a)] at hrow
  have hpen : max 0 (rowAbsSum a 3 0 - 2 * |tMulVec a 3 c 0|) = 0 := by
    rw [hrow, hAbs]
    apply max_eq_left
    dsimp [L] at hL ⊢
    nlinarith
  have hζ : ∀ i ≤ a, |m * sAlt i| ≤ 1 := by
    intro i _hi
    rw [abs_mul, abs_of_nonneg hm0, show |sAlt i| = 1 by simp [sAlt, abs_pow], mul_one]
    exact hm1
  have hg := psi_row_gain ha1 (i := 0) (by omega) hq hu0 hu1 hc hζ
  rw [hpen, hh] at hg
  have hdc := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hc
  have hK : 0 ≤ (q - 1) * (1 + u) - 4 * u := by
    nlinarith [mul_nonneg (show 0 ≤ q - 1 - 4 by linarith) hu0]
  have hKD := mul_nonneg hK hdc
  change _ * L ≤ _
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.last_pair_F_lower
