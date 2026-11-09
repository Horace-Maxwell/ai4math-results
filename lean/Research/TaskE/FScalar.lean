import Research.TaskE.ChallengeF
import Research.TaskE.C1Bounds

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma affine_pos {x l r A B : ℝ} (hl : l ≤ x) (hr : x ≤ r)
    (hAl : 0 < A + B * l) (hAr : 0 < A + B * r) : 0 < A + B * x := by
  by_cases hb : 0 ≤ B
  · nlinarith [mul_le_mul_of_nonneg_left hl hb]
  · nlinarith [mul_le_mul_of_nonpos_left hr (by linarith : B ≤ 0)]

lemma bilinear_pos (A B C D ul uh ml mh u m : ℝ)
    (hul : ul ≤ u) (huh : u ≤ uh) (hml : ml ≤ m) (hmh : m ≤ mh)
    (h00 : 0 < A + B * ul + C * ml + D * ul * ml)
    (h10 : 0 < A + B * uh + C * ml + D * uh * ml)
    (h01 : 0 < A + B * ul + C * mh + D * ul * mh)
    (h11 : 0 < A + B * uh + C * mh + D * uh * mh) :
    0 < A + B * u + C * m + D * u * m := by
  have hl : 0 < (A + B * u) + (C + D * u) * ml := by
    have hh := affine_pos (A := A + C * ml) (B := B + D * ml) hul huh
      (by nlinarith) (by nlinarith)
    nlinarith
  have hr : 0 < (A + B * u) + (C + D * u) * mh := by
    have hh := affine_pos (A := A + C * mh) (B := B + D * mh) hul huh
      (by nlinarith) (by nlinarith)
    nlinarith
  have hh := affine_pos (A := A + B * u) (B := C + D * u) hml hmh hl hr
  nlinarith

lemma family_min {a : ℕ} {q : ℝ} (hq : 5 ≤ q) {t : ℝ × ℝ × ℝ}
    (ht : FamF a q t) : mu q 0 ≤ t.1 ∧ mu q 0 ≤ t.2.1 := by
  obtain ⟨hm0, h0L, hL1, hm1⟩ := q_parameters hq
  unfold FamF at ht
  dsimp only at ht
  split_ifs at ht with he
  · rcases ht with ⟨hu, hm0', hmL, hr⟩ | ⟨hm, hu0, huL, hr⟩ |
      ⟨huL, hu1, hm0', hmL, hr⟩ | ⟨hu0, huL, hmL, hm1', hr⟩ <;>
      constructor <;> linarith
  · rcases ht with ⟨hu, hm, hr⟩ | ⟨hu, hmL, hm1', hr⟩ | ⟨hm, huL, hu1, hr⟩ |
      ⟨hbox, hr⟩
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
    · rcases hbox with ⟨hu0, huL, hm0', hmL⟩ | ⟨huL, hu1, hmL, hm1'⟩ <;>
        constructor <;> linarith

lemma scalar_5 (a : ℕ) (t : ℝ × ℝ × ℝ) (ht : FamF a 5 t) :
    (41 / 27 : ℝ) * 5 * t.2.2 <
      2 * (5 - 1) - (5 / 9 : ℝ) * (5 - 1) * (1 - t.1) - (28 / 9 : ℝ) * t.1 * t.2.1 := by
  classical
  unfold FamF at ht
  norm_num [mu, muSeq, muInf] at ht
  split_ifs at ht with he
  · rcases ht with ⟨hu, hm0, hm1, hr⟩ | ⟨hm, hu0, hu1, hr⟩ |
      ⟨hu0, hu1, hm0, hm1, hr⟩ | ⟨hu0, hu1, hm0, hm1, hr⟩
    · rw [hu, hr]
      nlinarith
    · rw [hm, hr]
      nlinarith
    · rw [hr]
      have hp := bilinear_pos (52 / 9 : ℝ) (-145 / 27 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (2 / 3 : ℝ) (17 / 25 : ℝ) (3 / 5 : ℝ) (2 / 3 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nlinarith
    · rw [hr]
      have hp := bilinear_pos (52 / 9 : ℝ) (20 / 9 : ℝ) (-205 / 27 : ℝ) (-28 / 9 : ℝ) (3 / 5 : ℝ) (2 / 3 : ℝ) (2 / 3 : ℝ) (17 / 25 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nlinarith
  · rcases ht with ⟨hu, hm, hr⟩ | ⟨hu, hm0, hm1, hr⟩ |
      ⟨hm, hu0, hu1, hr⟩ | ⟨hbox, hr⟩
    · rw [hu, hm, hr]
      norm_num
    · rw [hu, hr]
      nlinarith
    · rw [hm, hr]
      nlinarith
    · rw [hr]
      rcases hbox with ⟨hu0, hu1, hm0, hm1⟩ | ⟨hu0, hu1, hm0, hm1⟩
      · have hp := bilinear_pos (58 / 81 : ℝ) (20 / 9 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (3 / 5 : ℝ) (2 / 3 : ℝ) (3 / 5 : ℝ) (2 / 3 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith
      · have hp := bilinear_pos (58 / 81 : ℝ) (20 / 9 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (2 / 3 : ℝ) (17 / 25 : ℝ) (2 / 3 : ℝ) (17 / 25 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith

lemma scalar_7 (a : ℕ) (t : ℝ × ℝ × ℝ) (ht : FamF a 7 t) :
    (41 / 27 : ℝ) * 7 * t.2.2 <
      2 * (7 - 1) - (5 / 9 : ℝ) * (7 - 1) * (1 - t.1) - (28 / 9 : ℝ) * t.1 * t.2.1 := by
  classical
  unfold FamF at ht
  norm_num [mu, muSeq, muInf] at ht
  split_ifs at ht with he
  · rcases ht with ⟨hu, hm0, hm1, hr⟩ | ⟨hm, hu0, hu1, hr⟩ |
      ⟨hu0, hu1, hm0, hm1, hr⟩ | ⟨hu0, hu1, hm0, hm1, hr⟩
    · rw [hu, hr]
      nlinarith
    · rw [hm, hr]
      nlinarith
    · rw [hr]
      have hp := bilinear_pos (26 / 3 : ℝ) (-197 / 27 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (3 / 4 : ℝ) (37 / 49 : ℝ) (5 / 7 : ℝ) (3 / 4 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nlinarith
    · rw [hr]
      have hp := bilinear_pos (26 / 3 : ℝ) (10 / 3 : ℝ) (-287 / 27 : ℝ) (-28 / 9 : ℝ) (5 / 7 : ℝ) (3 / 4 : ℝ) (3 / 4 : ℝ) (37 / 49 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nlinarith
  · rcases ht with ⟨hu, hm, hr⟩ | ⟨hu, hm0, hm1, hr⟩ |
      ⟨hm, hu0, hu1, hr⟩ | ⟨hbox, hr⟩
    · rw [hu, hm, hr]
      norm_num
    · rw [hu, hr]
      nlinarith
    · rw [hm, hr]
      nlinarith
    · rw [hr]
      rcases hbox with ⟨hu0, hu1, hm0, hm1⟩ | ⟨hu0, hu1, hm0, hm1⟩
      · have hp := bilinear_pos (25 / 36 : ℝ) (10 / 3 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (5 / 7 : ℝ) (3 / 4 : ℝ) (5 / 7 : ℝ) (3 / 4 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith
      · have hp := bilinear_pos (25 / 36 : ℝ) (10 / 3 : ℝ) (0 / 1 : ℝ) (-28 / 9 : ℝ) (3 / 4 : ℝ) (37 / 49 : ℝ) (3 / 4 : ℝ) (37 / 49 : ℝ) t.1 t.2.1
          hu0 hu1 hm0 hm1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith

lemma scalar_large {a : ℕ} {q : ℝ} (hq : 8 ≤ q) {t : ℝ × ℝ × ℝ}
    (ht : FamF a q t) :
    (41 / 27 : ℝ) * q * t.2.2 <
      2 * (q - 1) - (5 / 9 : ℝ) * (q - 1) * (1 - t.1) - (28 / 9 : ℝ) * t.1 * t.2.1 := by
  have hq5 : 5 ≤ q := by linarith
  obtain ⟨hu, hm, hr⟩ := family_bounds hq5 ht
  have hmin := (family_min hq5 ht).1
  have h0 : (3 / 4 : ℝ) ≤ mu q 0 := by
    rw [(CodexPaper1.check_MuBounds q (by linarith)).2.2.1]
    rw [le_div_iff₀ (show 0 < q by linarith)]
    linarith
  have hulo : (3 / 4 : ℝ) ≤ t.1 := h0.trans hmin
  have hprod := mul_nonneg hu.1 (show 0 ≤ 1 - t.2.1 by linarith [hm.2])
  have hcoeff := mul_nonneg (show 0 ≤ 5 * (q - 1) - 28 by linarith)
    (show 0 ≤ t.1 - 3 / 4 by linarith)
  have hR := mul_lt_mul_of_pos_left hr (show 0 < (41 / 27 : ℝ) by norm_num)
  nlinarith

lemma scalar_F : CodexPaper1.TaskE.Challenge.FScalarPrimeDomain := by
  intro a q hq t ht
  rcases hq with h5 | h7 | h8
  · subst q; exact scalar_5 a t ht
  · subst q; exact scalar_7 a t ht
  · exact scalar_large h8 ht

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.scalar_F
