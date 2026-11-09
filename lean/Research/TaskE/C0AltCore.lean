import Research.TaskE.C0AltTerminal
import Research.TaskE.C0NonaltCore

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c0_alt_positive {a : ℕ} (ha : 3 ≤ a) {q y : ℝ} (hq : 5 ≤ q)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {g : ℕ → ℝ} (hg : IsSignVec a g)
    (hprev : g (a - 1) ≠ g a) (hna : ¬ (∀ i ≤ a, g i = -sAlt i)) :
    psi a 3 q y sAlt g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  classical
  rcases sign_vs_alt hg (i := a) le_rfl with hga | hga
  · have hs : sAlt (a - 1) = -sAlt a := by
      have hh := alt_succ (a - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
      linarith
    have hp : g (a - 1) = -g a := by
      rcases hg (a - 1) (by omega) with h | h
      · rcases hg a le_rfl with h' | h'
        · exact False.elim (hprev (h.trans h'.symm))
        · norm_num [h, h']
      · rcases hg a le_rfl with h' | h'
        · norm_num [h, h']
        · exact False.elim (hprev (h.trans h'.symm))
    exact c0_common_last_pair ha hq hy0 hy1 (alt_sign a) hg hga.symm hs hp
  · have hne : ((range (a + 1)).filter (fun i => g i = sAlt i)).Nonempty := by
      by_contra hn
      apply hna
      intro i hi
      rcases sign_vs_alt hg hi with hp | hp
      · exact False.elim (hn ⟨i, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩⟩)
      · exact hp
    let S := (range (a + 1)).filter (fun i => g i = sAlt i)
    let J := S.max' hne
    have hJ : J ∈ S := max'_mem _ _
    have hJa : J ≤ a := by have hh := mem_range.mp (mem_filter.mp hJ).1; omega
    have hJplus : g J = sAlt J := (mem_filter.mp hJ).2
    have hJlt : J < a := by
      by_contra hn
      have he : J = a := by omega
      have hplus : g a = sAlt a := by simpa only [he] using hJplus
      have hs : sAlt a = 1 ∨ sAlt a = -1 := neg_one_pow_eq_or ℝ a
      rcases hs with hs | hs <;> rw [hs] at hga hplus <;> linarith
    have htail : ∀ l, J < l → l ≤ a → g l = -sAlt l := by
      intro l hl hla
      rcases sign_vs_alt hg hla with hp | hp
      · have hm : l ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩
        have hh := le_max' S l hm
        change l ≤ J at hh
        omega
      · exact hp
    have hJlast : J ≠ a - 1 := by
      intro he
      apply hprev
      have hs : sAlt (a - 1) = -sAlt a := by
        have hh := alt_succ (a - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
        linarith
      calc
        g (a - 1) = sAlt (a - 1) := by simpa only [he] using hJplus
        _ = -sAlt a := hs
        _ = g a := hga.symm
    have hj : J ≤ a - 2 := by omega
    by_cases hj0 : J = 0
    · have hg0 : g 0 = sAlt 0 := by simpa only [hj0] using hJplus
      have ht : ∀ l, 0 < l → l ≤ a → g l = -sAlt l := by
        intro l hl hla
        exact htail l (by omega) hla
      exact c0_alt_tail_zero ha hq hy0 hy1 hg hg0 ht
    · exact c0_alt_tail_strict ha hj (by omega) hq hy0 hy1 hg hJplus htail

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c0_alt_positive
