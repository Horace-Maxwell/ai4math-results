import Research.TaskE.FLastPair
import Research.TaskE.FScalar
import Research.TaskE.FDeltaRatio
import Research.TaskE.FHigh

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma domain_ge_five {q : ℝ} (hq : CodexPaper1.TaskE.Challenge.FPrimeDomain q) : 5 ≤ q := by
  rcases hq with h | h | h
  · linarith
  · linarith
  · linarith

lemma sign_vs_alt {a i : ℕ} {c : ℕ → ℝ} (hc : IsSignVec a c) (hi : i ≤ a) :
    c i = sAlt i ∨ c i = -sAlt i := by
  rcases hc i hi with h | h <;>
    rcases neg_one_pow_eq_or ℝ i with hs | hs <;> simp [h, sAlt, hs]

lemma last_pair_scalar {q u m r : ℝ} (hq : 5 ≤ q) (hu : u ≤ 1)
    (hm : (3 / 5 : ℝ) ≤ m) (hr : q * r < q - 1) :
    (41 / 27 : ℝ) * q * r < 4 * (q - 1 - u) * m := by
  have h1 := mul_nonneg (show 0 ≤ q - 1 - u by linarith)
    (show 0 ≤ m - 3 / 5 by linarith)
  have h2 := mul_nonneg (show 0 ≤ 1 - u by linarith) (show 0 ≤ (3 / 5 : ℝ) by norm_num)
  have h3 := mul_lt_mul_of_pos_left hr (show 0 < (41 / 27 : ℝ) by norm_num)
  nlinarith

lemma full_F : CodexPaper1.TaskE.Challenge.ConditionsFThreePrimeDomain := by
  classical
  intro a ha q hdom c hc hna t ht
  have hq := domain_ge_five hdom
  obtain ⟨hu, hm, hr⟩ := family_bounds hq ht
  have hmin := family_min hq ht
  have hmlo : (3 / 5 : ℝ) ≤ t.2.1 := (mu_zero_lower hq).trans hmin.2
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ := delta_ratio a ha
  change 2 * deltaK a 3 ≤ (41 / 27 : ℝ) * L at hδ
  have hζ : ∀ i ≤ a, |t.2.1 * sAlt i| ≤ 1 := by
    intro i _hi
    rw [abs_mul, abs_of_nonneg hm.1, show |sAlt i| = 1 by simp [sAlt, abs_pow], mul_one]
    exact hm.2
  have hnon : 0 ≤ psi a 3 q t.1 c (fun i => t.2.1 * sAlt i) := by
    have hp := potential_lower a (by omega) q t.1 hq hu.1 hu.2 c _ hc hζ
    have hd := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hc
    exact (mul_nonneg (by linarith) hd).trans hp
  by_cases hqr : 0 ≤ q * t.2.2
  · have hδr := mul_le_mul_of_nonneg_left hδ hqr
    rcases sign_vs_alt hc (i := a) le_rfl with hca | hca
    · rcases sign_vs_alt hc (i := a - 1) (by omega) with hp | hp
      · have hh := last_pair_F_lower ha hq hu.1 hu.2 hm.1 hm.2 hc hca hp
        have hn := last_pair_scalar hq hu.2 hmlo hr
        have hs := mul_lt_mul_of_pos_left hn hL
        change 4 * (q - 1 - t.1) * t.2.1 * L ≤ _ at hh
        nlinarith
      · have hs : sAlt (a - 1) = -sAlt a := by
          have hh := alt_succ (a - 1)
          rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
          linarith
        have hrep : c (a - 1) = c a := by rw [hp, hs, neg_neg, hca]
        exact high_deficit_F a ha q hq c hc (terminal_repeat_high (by omega) hc hrep) t ht
    · have hne : ((range (a + 1)).filter (fun i => c i = sAlt i)).Nonempty := by
        by_contra hn
        apply hna
        intro i hi
        rcases sign_vs_alt hc hi with hp | hp
        · exact False.elim (hn ⟨i, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩⟩)
        · exact hp
      let S := (range (a + 1)).filter (fun i => c i = sAlt i)
      let J := S.max' hne
      have hJ : J ∈ S := max'_mem _ _
      have hJa : J ≤ a := by have hh := mem_range.mp (mem_filter.mp hJ).1; omega
      have hJplus : c J = sAlt J := (mem_filter.mp hJ).2
      have hJlt : J < a := by
        by_contra hn
        have he : J = a := by omega
        have hplus : c a = sAlt a := by simpa only [he] using hJplus
        have hs : sAlt a = 1 ∨ sAlt a = -1 := neg_one_pow_eq_or ℝ a
        rcases hs with hs | hs <;> rw [hs] at hca hplus <;> linarith
      have htail : ∀ l, J < l → l ≤ a → c l = -sAlt l := by
        intro l hl hla
        rcases sign_vs_alt hc hla with hp | hp
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
        have hrep : c (a - 1) = c a := by
          calc
            c (a - 1) = sAlt (a - 1) := by simpa only [hJlast] using hJplus
            _ = -sAlt a := hs
            _ = c a := hca.symm
        exact high_deficit_F a ha q hq c hc (terminal_repeat_high (by omega) hc hrep) t ht
      · have hj : J ≤ a - 2 := by omega
        have hh := tail_F_lower ha hj hq hu.1 hu.2 hmlo hm.2 hc hJplus htail
        have hn := scalar_F a q hdom t ht
        have hs := mul_lt_mul_of_pos_left hn hL
        change L * _ ≤ _ at hh
        nlinarith
  · have hqr' : q * t.2.2 < 0 := by linarith
    have hδp := delta_three_pos ha
    have hn := mul_neg_of_pos_of_neg (show 0 < 2 * deltaK a 3 by positivity) hqr'
    nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.full_F
