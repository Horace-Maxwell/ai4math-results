import Research.TaskE.ChallengeC1Alt
import Research.TaskE.FComplete
import Research.TaskE.C1Bounds
import Research.Backfill.Paper1.Prop31FirstDeviation

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma alt_psi_row_lower {a i : ℕ} (ha : 1 ≤ a) (hi : i ≤ a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {ζ : ℕ → ℝ}
    (hζ : ∀ l ≤ a, |ζ l| ≤ 1) :
    -hcell (q - 1) y (tMulVec a 3 sAlt i) (tMulVec a 3 ζ i) ≤ psi a 3 q y sAlt ζ := by
  have h : ∀ j ≤ a, hcell (q - 1) y (tMulVec a 3 sAlt j) (tMulVec a 3 ζ j) ≤ 0 := by
    intro j hj
    by_cases hja : j = a
    · subst j
      exact hcell_terminal_nonpos ha hq hy0 hy1 (alt_sign a) hζ
    · apply ICGGeneral.hcell_nonpos hy0 hy1 (by linarith)
      rw [CodexPaper1.Additional.tMulVec_eq_Tv 3 a ζ j hj,
        CodexPaper1.Additional.tMulVec_eq_Tv 3 a sAlt j hj]
      exact CodexPaper1.OneColumn.alt_row_dominates (Or.inr ⟨rfl, hq⟩) a hζ hj
  have hs := single_le_sum (f := fun j => -hcell (q - 1) y
    (tMulVec a 3 sAlt j) (tMulVec a 3 ζ j))
    (fun j hj => neg_nonneg.mpr (h j (by have := mem_range.mp hj; omega)))
    (mem_range.mpr (by omega : i < a + 1))
  rw [sum_neg_distrib] at hs
  unfold psi
  rw [CodexPaper1.OneColumn.delta_pmAlt (p := (3 : ℝ)) (Or.inl (by intros; rfl)), mul_zero, zero_sub]
  exact hs

lemma scaled_sign_unit {a : ℕ} {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {c : ℕ → ℝ} (hc : IsSignVec a c) : ∀ i ≤ a, |m * c i| ≤ 1 := by
  intro i hi
  have hs : |c i| = 1 := by rcases hc i hi with h | h <;> norm_num [h]
  rw [abs_mul, abs_of_nonneg hm0, hs, mul_one]
  exact hm1

lemma alt_last_pair_gain {a : ℕ} (ha : 3 ≤ a) {q y m : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hca : c a = sAlt a)
    (hprev : c (a - 1) = sAlt (a - 1)) :
    4 * (q - 1 - y) * m * (3 ^ (a - 1) * (3 - 1)) ≤
      psi a 3 q y sAlt (fun i => m * c i) := by
  have ha1 : 1 ≤ a := by omega
  have hj : a - 1 < a := by omega
  have hi : a - 1 - (a - 1) = 0 := by omega
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hs : sAlt (a - 1) = -sAlt a := by
    have hh := alt_succ (a - 1)
    rw [Nat.sub_add_cancel ha1] at hh
    linarith
  have hA : tMulVec a 3 sAlt 0 = sAlt a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) sAlt
    rw [hi, z_end ha1 sAlt, hs] at hh
    rw [hh]
    dsimp [L]
    ring
  have hD : tMulVec a 3 c 0 = sAlt a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) c
    rw [hi, z_end ha1 c, hca, hprev, hs] at hh
    rw [hh]
    dsimp [L]
    ring
  have hB : tMulVec a 3 (fun i => m * c i) 0 = sAlt a * (2 * m * L) := by
    rw [CodexPaper1.Chain.tMulVec_scale_of_eq a 3 m _ c (by intros; rfl), hD]
    ring
  have hh : hcell (q - 1) y (tMulVec a 3 sAlt 0)
      (tMulVec a 3 (fun i => m * c i) 0) = -4 * (q - 1 - y) * m * L := by
    have hε : sAlt a = 1 ∨ sAlt a = -1 := neg_one_pow_eq_or ℝ a
    rw [hA, hB, hcell_sign _ _ _ _ _ hε]
    have he := hcell_same_large (u := y) (P := q - 1) (A := 2 * L) (B := 2 * m * L)
      (by linarith) (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hm1 hL.le])
    nlinarith
  have hg := alt_psi_row_lower ha1 (i := 0) (by omega) hq hy0 hy1 (scaled_sign_unit hm0 hm1 hc)
  rw [hh] at hg
  change 4 * (q - 1 - y) * m * L ≤ _
  nlinarith only [hg]

lemma alt_tail_geometry {a j : ℕ} (ha : 3 ≤ a) (hj : j ≤ a - 2)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hcj : c j = sAlt j)
    (htail : ∀ l, j < l → l ≤ a → c l = -sAlt l) :
    let L : ℝ := 3 ^ (a - 1) * (3 - 1)
    let v : ℝ := |z 3 a sAlt (j : ℤ)|
    (1 / 3 : ℝ) ≤ v ∧ v ≤ (5 / 9 : ℝ) ∧ L * v ≤ DeltaC a 3 c ∧
      tMulVec a 3 c (a - 1 - j) = (-sAlt j) * (L * (1 - v)) ∧
      tMulVec a 3 sAlt (a - 1 - j) = (-sAlt j) * (L * (1 + v)) := by
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
    dsimp [v]; rw [hv_eq]
    have hh := hmu.1; rw [mu_three_zero] at hh; exact hh
  have hv1 : v ≤ (5 / 9 : ℝ) := by
    dsimp [v]; rw [hv_eq]
    have hh := hmu.2; rw [mu_three_one] at hh; exact hh
  have hzt := negative_tail_z hja htail
  have hzalt := alt_z_signed ha1 hja
  change z 3 a sAlt (j : ℤ) = -sAlt j * v at hzalt
  have hzc : z 3 a c (j : ℤ) = sAlt j * v := by rw [hzt, hzalt]; ring
  have hzc_abs : |z 3 a c (j : ℤ)| = v := by
    rw [hzc, abs_mul, show |sAlt j| = 1 by simp [sAlt, abs_pow], one_mul,
      abs_of_nonneg (by linarith : 0 ≤ v)]
  have hrep : c j = c (j + 1) := by
    rw [hcj, htail (j + 1) (by omega) (by omega), alt_succ, neg_neg]
  have hd : L * v ≤ DeltaC a 3 c := by
    have hp := deficit_pays_term ha1 hc (j := j) (mem_filter.mpr ⟨mem_range.mpr hja, hrep⟩)
    rw [hzc_abs, hw] at hp
    have hmu0 := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) j
    norm_num at hmu0
    have hmt := mul_nonneg (by linarith : 0 ≤ mu 3 (j : ℤ) - 1 / 3) (by linarith : 0 ≤ v)
    have hx := mul_nonneg (show 0 ≤ 3 * L by positivity) hmt
    nlinarith
  refine ⟨hv0, hv1, hd, ?_, ?_⟩
  · rw [SProof.row_path ha1 hja (by norm_num : (3 : ℝ) ≤ 3) c, hzc, hcj]
    ring
  · rw [SProof.row_path ha1 hja (by norm_num : (3 : ℝ) ≤ 3) sAlt]
    conv_lhs => rw [hzalt]
    ring

lemma alt_tail_gain {a j : ℕ} (ha : 3 ≤ a) (hj : j ≤ a - 2) {q y m : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hcj : c j = sAlt j)
    (htail : ∀ l, j < l → l ≤ a → c l = -sAlt l) :
    let L : ℝ := 3 ^ (a - 1) * (3 - 1)
    let v : ℝ := |z 3 a sAlt (j : ℤ)|
    (1 / 3 : ℝ) ≤ v ∧ v ≤ (5 / 9 : ℝ) ∧ L * v ≤ DeltaC a 3 c ∧
      2 * (q - 1 - y) * m * L * (1 - v) ≤ psi a 3 q y sAlt (fun i => m * c i) := by
  obtain ⟨hv0, hv1, hd, hC, hA⟩ := alt_tail_geometry ha hj hc hcj htail
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  let v : ℝ := |z 3 a sAlt (j : ℤ)|
  change (1 / 3 : ℝ) ≤ v at hv0
  change v ≤ (5 / 9 : ℝ) at hv1
  have hL : 0 < L := by dsimp [L]; positivity
  have hB : tMulVec a 3 (fun i => m * c i) (a - 1 - j) =
      (-sAlt j) * (m * L * (1 - v)) := by
    rw [CodexPaper1.Chain.tMulVec_scale_of_eq a 3 m _ c (by intros; rfl), hC]
    dsimp [L, v]; ring
  have hh : hcell (q - 1) y (tMulVec a 3 sAlt (a - 1 - j))
      (tMulVec a 3 (fun i => m * c i) (a - 1 - j)) =
      -2 * (q - 1 - y) * m * L * (1 - v) := by
    rw [hA, hB, hcell_sign _ _ _ _ _ (by
      rcases neg_one_pow_eq_or ℝ j with hs | hs <;> simp [sAlt, hs])]
    have hBA : m * L * (1 - v) ≤ L * (1 + v) := by
      have hh := mul_le_mul_of_nonneg_right hm1 (mul_nonneg hL.le (by linarith : 0 ≤ 1 - v))
      nlinarith
    have he := hcell_same_large (P := q - 1) (u := y)
      (A := L * (1 + v)) (B := m * L * (1 - v)) (by linarith)
      (mul_nonneg (mul_nonneg hm0 hL.le) (by linarith)) hBA
    nlinarith
  have hg := alt_psi_row_lower (by omega : 1 ≤ a) (i := a - 1 - j) (by omega)
    hq hy0 hy1 (scaled_sign_unit hm0 hm1 hc)
  rw [hh] at hg
  refine ⟨hv0, hv1, hd, ?_⟩
  change 2 * (q - 1 - y) * m * L * (1 - v) ≤ _
  nlinarith only [hg]

lemma c1_alt_scalar {q y m e v : ℝ} (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hm0 : (3 / 5 : ℝ) ≤ m) (hm1 : m ≤ 1) (he0 : (3 / 5 : ℝ) ≤ e)
    (hv0 : (1 / 3 : ℝ) ≤ v) (hv1 : v ≤ (5 / 9 : ℝ)) :
    (41 / 27 : ℝ) * (q - 1 - e) <
      (2 * (q - 1) + (q - 2) * e) * v + 2 * (q - 1 - y) * m * (1 - v) := by
  have hvlt : v < 1 := by linarith only [hv1]
  have hP : 0 ≤ q - 1 := by linarith
  have hM : 0 ≤ m := by linarith
  have hC : 0 ≤ 2 * (q - 1) + (q - 2) * e - 2 * (q - 1 - y) * m := by
    have h1 := mul_nonneg hP (show 0 ≤ 1 - m by linarith)
    have h2 := mul_nonneg (show 0 ≤ q - 2 by linarith) (show 0 ≤ e by linarith)
    have h3 := mul_nonneg hy0 hM
    nlinarith
  have hv := mul_le_mul_of_nonneg_left hv0 hC
  have he := mul_le_mul_of_nonneg_left he0 (show 0 ≤ q - 2 by linarith)
  have hm := mul_le_mul_of_nonneg_left hm0 (show 0 ≤ q - 1 - y by linarith)
  have hy := mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ (3 / 5 : ℝ) by norm_num)
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.alt_tail_gain
#print axioms CodexPaper1.TaskE.FCProof.alt_last_pair_gain
#print axioms CodexPaper1.TaskE.FCProof.c1_alt_scalar
