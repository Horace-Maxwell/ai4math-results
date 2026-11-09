import Research.TaskE.C1AltBasis

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c1_one_alt_positive {a : ℕ} (ha : 3 ≤ a) {q y : ℝ} (hq : 5 ≤ q)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {w : ℕ → ℝ} (hw : IsSignVec a w)
    (hna : ¬ (∀ i ≤ a, w i = -sAlt i)) :
    (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 w +
        psi a 3 q y sAlt (fun i => mu q 0 * w i) >
      q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 w) := by
  classical
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hm := q_parameters hq
  have hmlo := mu_zero_lower hq
  have hmhi : mu q 0 ≤ 1 := hm.2.1.trans (hm.2.2.1.trans hm.2.2.2)
  have helo := eta_lower_mu hq ⟨hy0, hy1⟩ (n := 1) (by omega)
  have he0 : 0 < etaMap q 1 y := hm.1.trans_le helo
  have heq : q * etaMap q 2 y = q - 1 - etaMap q 1 y := by
    change q * ((q - 1 - etaMap q 1 y) / q) = _
    field_simp
  have hη := eta_times_q hq ⟨hy0, hy1⟩ (n := 2) (by omega)
  have hD0 := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hw
  have hC : 0 ≤ 2 * (q - 1) + (q - 2) * etaMap q 1 y := by
    exact add_nonneg (by linarith) (mul_nonneg (by linarith) he0.le)
  have hζ := scaled_sign_unit hm.1.le hmhi hw
  have hpot : 0 ≤ psi a 3 q y sAlt (fun i => mu q 0 * w i) :=
    ((CodexPaper1.check_Lemma22 a (by omega) 3 q (Or.inr ⟨rfl, hq⟩) y hy0 hy1
      sAlt _ (alt_sign a) hζ).2 (Or.inl (by intros; rfl))).2.1
  have hchain : 0 ≤ (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 w :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hD0
  by_cases hhigh : 2 * deltaK a 3 ≤ DeltaC a 3 w
  · have hδp := delta_three_pos ha
    have hDp : 0 < DeltaC a 3 w := by linarith
    have hchainp : 0 < (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 w :=
      mul_pos (mul_pos (by linarith) (by linarith)) hDp
    have hR : q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hη.1.le (by linarith)
    linarith
  have hδ := delta_ratio a ha
  change 2 * deltaK a 3 ≤ (41 / 27 : ℝ) * L at hδ
  have hδr := mul_le_mul_of_nonneg_left hδ hη.1.le
  rcases sign_vs_alt hw (i := a) le_rfl with hwa | hwa
  · rcases sign_vs_alt hw (i := a - 1) (by omega) with hp | hp
    · have hh := alt_last_pair_gain ha hq hy0 hy1 hm.1.le hmhi hw hwa hp
      have hr : q * etaMap q 2 y < q - 1 := by rw [heq]; linarith
      have hn := last_pair_scalar hq hy1 hmlo hr
      have hs := mul_lt_mul_of_pos_left hn hL
      change 4 * (q - 1 - y) * mu q 0 * L ≤ _ at hh
      nlinarith
    · have hs : sAlt (a - 1) = -sAlt a := by
        have hh := alt_succ (a - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
        linarith
      have hrep : w (a - 1) = w a := by rw [hp, hs, neg_neg, hwa]
      exact False.elim (hhigh (terminal_repeat_high (by omega) hw hrep))
  · have hne : ((range (a + 1)).filter (fun i => w i = sAlt i)).Nonempty := by
      by_contra hn
      apply hna
      intro i hi
      rcases sign_vs_alt hw hi with hp | hp
      · exact False.elim (hn ⟨i, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩⟩)
      · exact hp
    let S := (range (a + 1)).filter (fun i => w i = sAlt i)
    let J := S.max' hne
    have hJ : J ∈ S := max'_mem _ _
    have hJa : J ≤ a := by have hh := mem_range.mp (mem_filter.mp hJ).1; omega
    have hJplus : w J = sAlt J := (mem_filter.mp hJ).2
    have hJlt : J < a := by
      by_contra hn
      have he : J = a := by omega
      have hplus : w a = sAlt a := by simpa only [he] using hJplus
      have hs : sAlt a = 1 ∨ sAlt a = -1 := neg_one_pow_eq_or ℝ a
      rcases hs with hs | hs <;> rw [hs] at hwa hplus <;> linarith
    have htail : ∀ l, J < l → l ≤ a → w l = -sAlt l := by
      intro l hl hla
      rcases sign_vs_alt hw hla with hp | hp
      · have hm : l ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩
        have hh := le_max' S l hm
        change l ≤ J at hh
        omega
      · exact hp
    by_cases hJlast : J = a - 1
    · have hs : sAlt (a - 1) = -sAlt a := by
        have hh := alt_succ (a - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
        linarith
      have hrep : w (a - 1) = w a := by
        calc
          w (a - 1) = sAlt (a - 1) := by simpa only [hJlast] using hJplus
          _ = -sAlt a := hs
          _ = w a := hwa.symm
      exact False.elim (hhigh (terminal_repeat_high (by omega) hw hrep))
    · have hj : J ≤ a - 2 := by omega
      obtain ⟨hv0, hv1, hd, hp⟩ := alt_tail_gain ha hj hq hy0 hy1 hm.1.le hmhi hw hJplus htail
      have hn := c1_alt_scalar hq hy0 hy1 hmlo hmhi (hmlo.trans helo) hv0 hv1
      have hs := mul_lt_mul_of_pos_left hn hL
      have hCD := mul_le_mul_of_nonneg_left hd hC
      change L * |z 3 a sAlt (J : ℤ)| ≤ _ at hd
      change 2 * (q - 1 - y) * mu q 0 * L * (1 - |z 3 a sAlt (J : ℤ)|) ≤ _ at hp
      rw [heq] at hδr ⊢
      nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c1_one_alt_positive
