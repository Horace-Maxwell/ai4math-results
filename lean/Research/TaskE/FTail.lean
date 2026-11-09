import Research.TaskE.FGain
import Research.TaskE.DeficitLower
import Research.Backfill.Paper1.AlternatingPath
import Research.Backfill.Paper1.ClosedForms
import Research.Backfill.Paper1.Chain

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge ICGGeneral

lemma alt_sign (a : ℕ) : IsSignVec a sAlt := by
  intro i _hi
  exact neg_one_pow_eq_or ℝ i

lemma alt_succ (j : ℕ) : sAlt (j + 1) = -sAlt j := by simp [sAlt, pow_succ]

lemma length_scale {a : ℕ} (ha : 1 ≤ a) :
    (3 : ℝ) ^ a = (3 ^ (a - 1) * (3 - 1)) * (3 / 2) := by
  have he : (3 : ℝ) ^ a = 3 ^ (a - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel ha]
  nlinarith

lemma z_end {a : ℕ} (ha : 1 ≤ a) (c : ℕ → ℝ) :
    z 3 a c ((a - 1 : ℕ) : ℤ) = c a := by
  unfold z
  have he : ((a : ℤ) - 1 - ((a - 1 : ℕ) : ℤ)).toNat = 0 := by omega
  rw [he]
  rfl

lemma terminal_repeat_high {a : ℕ} (ha : 1 ≤ a) {c : ℕ → ℝ}
    (hc : IsSignVec a c) (he : c (a - 1) = c a) :
    2 * deltaK a 3 ≤ DeltaC a 3 c := by
  have hj : a - 1 < a := by omega
  have hj1 : a - 1 + 1 = a := by omega
  have hp := deficit_pays_term ha hc (j := a - 1)
    (by rw [NA, mem_filter, mem_range, hj1]; exact ⟨hj, he⟩)
  have hca : |c a| = 1 := by rcases hc a le_rfl with h | h <;> norm_num [h]
  rw [z_end ha c, hca, mul_one] at hp
  have hi : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  rw [hi] at hp
  have hd := CodexPaper1.ClosedForms.weighted_mu_eq_deltaK (x := (3 : ℝ)) (by norm_num) a
  nlinarith

lemma negative_tail_z {a j : ℕ} (hj : j < a) {c : ℕ → ℝ}
    (htail : ∀ l, j < l → l ≤ a → c l = -sAlt l) :
    z 3 a c (j : ℤ) = -z 3 a sAlt (j : ℤ) := by
  rw [CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a c j hj,
    CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a sAlt j hj]
  unfold Zp Wp
  rw [← neg_div]
  congr 1
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro l hl
  have hmem := mem_Ico.mp hl
  rw [htail l (by omega) (by omega)]
  ring

lemma alt_z_signed {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) :
    z 3 a sAlt (j : ℤ) = -sAlt j * |z 3 a sAlt (j : ℤ)| := by
  have ht := (SProof.path_bounds ha hj (by norm_num : (3 : ℝ) ≤ 3) (alt_sign a)).1
  rw [alt_succ] at ht
  rcases neg_one_pow_eq_or ℝ j with h | h
  · change sAlt j = 1 at h
    rw [h] at ht ⊢
    rw [abs_of_neg (by linarith : z 3 a sAlt (j : ℤ) < 0)]
    ring
  · change sAlt j = -1 at h
    rw [h] at ht ⊢
    rw [abs_of_pos (by linarith : 0 < z 3 a sAlt (j : ℤ))]
    ring

lemma hcell_sign (P u A B ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    BackfillPaper1.Challenge.hcell P u (ε * A) (ε * B) = BackfillPaper1.Challenge.hcell P u A B := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
  · simp only [neg_one_mul]
    exact ICGGeneral.hcell_neg P u A B

lemma tail_gain_algebra {L v q u m D Ψ : ℝ}
    (hL : 0 ≤ L) (hv : v ≤ (5 / 9 : ℝ)) (hcoef : 0 ≤ (q - 1) * (1 - u) + 2 * u * m)
    (hK : 0 ≤ (q - 1) * (1 + u) - 4 * u) (hd : L * v ≤ D)
    (hg : ((q - 1) * (1 + u) - 4 * u) * D +
      (4 * u * L * v - (2 * u * (m * L * (1 + v)) - 2 * (q - 1) * (L * (1 - v)))) ≤ Ψ) :
    L * (2 * (q - 1) - (5 / 9 : ℝ) * (q - 1) * (1 - u) - (28 / 9 : ℝ) * u * m) ≤ Ψ := by
  have hv' := mul_le_mul_of_nonneg_left hv (mul_nonneg hL hcoef)
  have hKD := mul_le_mul_of_nonneg_left hd hK
  calc
    _ ≤ L * (2 * (q - 1) - (q - 1) * (1 - u) * v - 2 * u * m * (1 + v)) := by nlinarith
    _ = ((q - 1) * (1 + u) - 4 * u) * (L * v) +
      (4 * u * L * v - (2 * u * (m * L * (1 + v)) - 2 * (q - 1) * (L * (1 - v)))) := by ring
    _ ≤ ((q - 1) * (1 + u) - 4 * u) * D +
      (4 * u * L * v - (2 * u * (m * L * (1 + v)) - 2 * (q - 1) * (L * (1 - v)))) :=
      by nlinarith only [hKD]
    _ ≤ Ψ := hg

lemma tail_F_lower {a j : ℕ} (ha : 3 ≤ a) (hj : j ≤ a - 2) {q u m : ℝ}
    (hq : 5 ≤ q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hm0 : (3 / 5 : ℝ) ≤ m) (hm1 : m ≤ 1)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hcj : c j = sAlt j)
    (htail : ∀ l, j < l → l ≤ a → c l = -sAlt l) :
    (3 ^ (a - 1) * (3 - 1)) *
      (2 * (q - 1) - (5 / 9 : ℝ) * (q - 1) * (1 - u) - (28 / 9 : ℝ) * u * m) ≤
      psi a 3 q u c (fun i => m * sAlt i) := by
  classical
  have ha1 : 1 ≤ a := by omega
  have hja : j < a := by omega
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  let v : ℝ := |z 3 a sAlt (j : ℤ)|
  have hL : 0 < L := by dsimp [L]; positivity
  have hw := length_scale ha1
  change (3 : ℝ) ^ a = L * (3 / 2) at hw
  have hv_eq := CodexPaper1.check_AlternatingPath 3 (by norm_num) a ha1
    (j : ℤ) (by omega) (by omega)
  have hi : (a : ℤ) - 2 - (j : ℤ) = ((a - 2 - j : ℕ) : ℤ) := by omega
  rw [hi] at hv_eq
  have hmu := (CodexPaper1.check_MuBounds 3 (by norm_num)).2.1 (a - 2 - j)
  have hv0 : (1 / 3 : ℝ) ≤ v := by
    dsimp [v]
    rw [hv_eq]
    have hh := hmu.1
    rw [mu_three_zero] at hh
    exact hh
  have hv1 : v ≤ (5 / 9 : ℝ) := by
    dsimp [v]
    rw [hv_eq]
    have hh := hmu.2
    rw [mu_three_one] at hh
    exact hh
  have hzt := negative_tail_z hja htail
  have hzalt := alt_z_signed ha1 hja
  have hzc : z 3 a c (j : ℤ) = sAlt j * v := by
    change z 3 a sAlt (j : ℤ) = -sAlt j * v at hzalt
    rw [hzt, hzalt]
    ring
  have hε : -sAlt j = 1 ∨ -sAlt j = -1 := by
    rcases neg_one_pow_eq_or ℝ j with hs | hs <;> simp [sAlt, hs]
  have habs_s : |sAlt j| = 1 := by simp [sAlt, abs_pow]
  have hzc_abs : |z 3 a c (j : ℤ)| = v := by
    rw [hzc, abs_mul, habs_s, one_mul, abs_of_nonneg (by linarith : 0 ≤ v)]
  have hrep : c j = c (j + 1) := by
    rw [hcj, htail (j + 1) (by omega) (by omega), alt_succ, neg_neg]
  have hA : tMulVec a 3 c (a - 1 - j) = (-sAlt j) * (L * (1 - v)) := by
    rw [SProof.row_path ha1 hja (by norm_num : (3 : ℝ) ≤ 3) c, hzc, hcj]
    dsimp [L]
    ring
  have hD : tMulVec a 3 sAlt (a - 1 - j) = (-sAlt j) * (L * (1 + v)) := by
    rw [SProof.row_path ha1 hja (by norm_num : (3 : ℝ) ≤ 3) sAlt, hzalt]
    dsimp [L, v]
    ring
  have hB : tMulVec a 3 (fun i => m * sAlt i) (a - 1 - j) =
      (-sAlt j) * (m * L * (1 + v)) := by
    rw [CodexPaper1.Chain.tMulVec_scale_of_eq a 3 m _ sAlt (by intros; rfl), hD]
    ring
  have hAB : L * (1 - v) ≤ m * L * (1 + v) := by
    have hprod := mul_nonneg (by linarith : 0 ≤ m - 3 / 5) (by linarith : 0 ≤ 1 + v)
    have ht : 1 - v ≤ m * (1 + v) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left ht hL.le
    nlinarith
  have hh : BackfillPaper1.Challenge.hcell (q - 1) u (tMulVec a 3 c (a - 1 - j))
      (tMulVec a 3 (fun i => m * sAlt i) (a - 1 - j)) =
      2 * u * (m * L * (1 + v)) - 2 * (q - 1) * (L * (1 - v)) := by
    rw [hA, hB, hcell_sign _ _ _ _ _ hε]
    exact hcell_same_small (by linarith) (mul_nonneg hL.le (by linarith)) hAB
  have hpen := SProof.penalty_row ha1 hja (by norm_num : (3 : ℝ) ≤ 3) hc
  rw [ite_eq_left hrep, hzc_abs] at hpen
  change max 0 (rowAbsSum a 3 (a - 1 - j) - 2 * |tMulVec a 3 c (a - 1 - j)|) =
    2 * L * v at hpen
  have hζ : ∀ i ≤ a, |m * sAlt i| ≤ 1 := by
    intro i _hi
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ m), show |sAlt i| = 1 by simp [sAlt, abs_pow], mul_one]
    exact hm1
  have hg := psi_row_gain ha1 (i := a - 1 - j) (by omega) hq hu0 hu1 hc hζ
  rw [hpen, hh] at hg
  have hp := deficit_pays_term ha1 hc (j := j) (mem_filter.mpr ⟨mem_range.mpr hja, hrep⟩)
  rw [hzc_abs] at hp
  have hmu0 := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) j
  norm_num at hmu0
  have hmt := mul_nonneg (by linarith : 0 ≤ mu 3 (j : ℤ) - 1 / 3) (by linarith : 0 ≤ v)
  have hd : L * v ≤ DeltaC a 3 c := by
    rw [hw] at hp
    have hx := mul_nonneg (show 0 ≤ 3 * L by positivity) hmt
    nlinarith
  have hK : 0 ≤ (q - 1) * (1 + u) - 4 * u := by
    have hx := mul_nonneg (show 0 ≤ q - 1 - 4 by linarith) hu0
    nlinarith
  have hcoef : 0 ≤ (q - 1) * (1 - u) + 2 * u * m := by
    exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by positivity) (by linarith))
  change L * _ ≤ _
  apply tail_gain_algebra hL.le hv1 hcoef hK hd
  convert hg using 1
  ring

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.tail_F_lower
#print axioms CodexPaper1.TaskE.FCProof.terminal_repeat_high
