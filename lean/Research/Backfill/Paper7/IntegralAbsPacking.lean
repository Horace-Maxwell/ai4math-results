import Research.Backfill.Paper7.SigmaSqPacking
import Research.Backfill.Paper7.Lemma22
import Research.Backfill.Paper7.IntegralSquareCounts
import Research.Backfill.Paper7.Identities12

/-! Multiplicity-preserving passage from integral real eigenvalues to natural
absolute values. No symmetry of the full spectrum is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Rank
open BackfillPaper7.Challenge

def absNat (x : ℝ) : ℕ := ⌊|x|⌋₊
#print axioms Paper7Rank.absNat

theorem cast_absNat (x : ℝ) (hx : ∃ z : ℤ, x = (z : ℝ)) :
    (absNat x : ℝ) = |x| := by
  obtain ⟨z, rfl⟩ := hx
  have hz : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  unfold absNat
  rw [← hz, Nat.floor_natCast]
#print axioms Paper7Rank.cast_absNat

theorem count_absNat (s : Multiset ℝ)
    (hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ)) (n : ℕ) (hn : 0 < n) :
    (s.map absNat).count n = s.count (n : ℝ) + s.count (-(n : ℝ)) := by
  classical
  revert hint
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x s ih =>
    intro hint
    have hi := ih (fun y hy => hint y (Multiset.mem_cons_of_mem hy))
    have hc := cast_absNat x (hint x (Multiset.mem_cons_self x s))
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hx : x = (n : ℝ)
    · subst x
      have hf : absNat (n : ℝ) = n := by
        apply Nat.cast_injective (R := ℝ)
        simpa only [abs_of_pos hnp] using hc
      have hne : -(n : ℝ) ≠ (n : ℝ) := by linarith
      simp only [Multiset.map_cons, hf, Multiset.count_cons_self,
        Multiset.count_cons_of_ne hne]
      omega
    · by_cases hnx : x = -(n : ℝ)
      · subst x
        have hf : absNat (-(n : ℝ)) = n := by
          apply Nat.cast_injective (R := ℝ)
          simpa only [abs_neg, abs_of_pos hnp] using hc
        have hne : (n : ℝ) ≠ -(n : ℝ) := by linarith
        simp only [Multiset.map_cons, hf, Multiset.count_cons_self,
          Multiset.count_cons_of_ne hne]
        omega
      · have hf : n ≠ absNat x := by
          intro he
          have hab : |x| = (n : ℝ) := by rw [← hc, ← he]
          rcases le_total 0 x with hpos | hneg
          · rw [abs_of_nonneg hpos] at hab
            exact hx hab
          · rw [abs_of_nonpos hneg] at hab
            exact hnx (by linarith)
        simp only [Multiset.map_cons, Multiset.count_cons_of_ne hf,
          Multiset.count_cons_of_ne (Ne.symm hx), Multiset.count_cons_of_ne (Ne.symm hnx)]
        exact hi
#print axioms Paper7Rank.count_absNat

theorem absNat_square_sum (s : Multiset ℝ)
    (hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ)) :
    ((((s.map absNat).map (fun n : ℕ => n ^ 2)).sum : ℕ) : ℝ) =
      (s.map (fun x => x ^ 2)).sum := by
  rw [Nat.cast_multiset_sum, Multiset.map_map, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro x hx
  change ((absNat x ^ 2 : ℕ) : ℝ) = x ^ 2
  rw [Nat.cast_pow, cast_absNat x (hint x hx), sq_abs]
#print axioms Paper7Rank.absNat_square_sum

theorem large_absNat_count_le_four (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (n : ℕ) :
    ((bigEigs (SG b p q)).map absNat).count n ≤ 4 := by
  classical
  let s := bigEigs (SG b p q)
  have hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ) := by
    intro x hx
    exact Paper7Moments.integral_spec_entry _ hG x (Multiset.mem_filter.mp hx).1
  by_cases hn : 2 ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := ((Paper7Lemma22.check_Lemma22 b p q hb).1 (n : ℝ)
      (by linarith) (by linarith) (by linarith)).2.1
    have hm := ((Paper7Lemma22.check_Lemma22 b p q hb).1 (-(n : ℝ))
      (by linarith) (by linarith) (by linarith)).2.1
    have hc := count_absNat s hint n (by omega)
    have h1 : s.count (n : ℝ) = mult (SG b p q) (n : ℝ) := by
      exact Multiset.count_filter_of_pos (by simpa only [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] using hnR)
    have h2 : s.count (-(n : ℝ)) = mult (SG b p q) (-(n : ℝ)) := by
      exact Multiset.count_filter_of_pos (by simpa only [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] using hnR)
    change (s.map absNat).count n ≤ 4
    omega
  · have hnot : n ∉ s.map absNat := by
      rintro hmem
      obtain ⟨x, hx, hxn⟩ := Multiset.mem_map.mp hmem
      have hc := cast_absNat x (hint x hx)
      have hx2 := (Multiset.mem_filter.mp hx).2
      have hnR : (n : ℝ) < 2 := by exact_mod_cast (by omega : n < 2)
      rw [hxn] at hc
      linarith
    change (s.map absNat).count n ≤ 4
    rw [Multiset.count_eq_zero_of_notMem hnot]
    omega
#print axioms Paper7Rank.large_absNat_count_le_four

/-- The strengthened square budget keeps the two exceptional multiplicities. -/
theorem rank_square_budget (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    (sigmaSq ((bigEigs (SG b p q)).card : ℤ) : ℤ) +
      mult (SG b p q) 1 + mult (SG b p q) (-1) ≤ 2 * (nOf b p q : ℤ) := by
  classical
  let s := bigEigs (SG b p q)
  have hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ) := by
    intro x hx
    exact Paper7Moments.integral_spec_entry _ hG x (Multiset.mem_filter.mp hx).1
  have hmin : ∀ a ∈ s.map absNat, 2 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    have hc := cast_absNat x (hint x hx)
    have hm := (Multiset.mem_filter.mp hx).2
    have : (2 : ℝ) ≤ absNat x := by linarith
    exact_mod_cast this
  have hpack := sigmaSq_packing (s.map absNat) hmin
    (large_absNat_count_le_four b p q hb hG)
  rw [Multiset.card_map] at hpack
  have hpackR : (sigmaSq (s.card : ℤ) : ℝ) ≤
      ((((s.map absNat).map (fun n : ℕ => n ^ 2)).sum : ℕ) : ℝ) := by exact_mod_cast hpack
  rw [absNat_square_sum s hint] at hpackR
  have hbudget := Paper7Admissible.graph_square_partition (SG b p q) hG
  rw [Paper7SunMoments.sg_second_moment b p q hb] at hbudget
  have hR : (sigmaSq (s.card : ℤ) : ℝ) + (mult (SG b p q) 1 : ℝ) +
      (mult (SG b p q) (-1) : ℝ) ≤ 2 * (nOf b p q : ℝ) := by
    change (sigmaSq (s.card : ℤ) : ℝ) ≤ (s.map (fun x => x ^ 2)).sum at hpackR
    linarith
  exact_mod_cast hR
#print axioms Paper7Rank.rank_square_budget

end Paper7Rank
