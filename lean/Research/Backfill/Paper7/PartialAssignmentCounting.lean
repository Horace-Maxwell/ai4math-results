import Research.Backfill.Paper7.Lemma42

/-! Complete frozen partial-assignment counting inequality. The finite sums on
I stay genuinely partial; the spectrum and budget concern the completed graph. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PartialCounting
open BackfillPaper7.Challenge

theorem partial_sum_le_total (b : ℕ) (I : Finset (Fin b)) (f : Fin b → ℕ) :
    (∑ k ∈ I, f k) ≤ ∑ k, f k :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ I)
#print axioms Paper7PartialCounting.partial_sum_le_total

/-- The counting argument works for any actual finite subset, including empty
and full subsets. No positive-pendant or lower-budget premise is added. -/
theorem partial_counting_on_subset (b N : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (he : Even b) (hG : IsIntegralGraph (SG b p q))
    (hN : nOf b p q ≤ N) (I : Finset (Fin b)) (hP : 2 ≤ ∑ k ∈ I, p k) :
    2 * ((∑ k ∈ I, q k : ℕ) : ℝ) ≤
      2 * min (N : ℝ)
        (2 * S2 (SG b p q) - 2 * ((Bplus (SG b p q)).card : ℝ)) -
      b - 2 * S2 (SG b p q) + 2 * ((Bplus (SG b p q)).card : ℝ) := by
  have hPtotal : 2 ≤ ∑ k, p k := hP.trans (partial_sum_le_total b I p)
  have hmax : max (∑ k, p k) 2 = ∑ k, p k := max_eq_left hPtotal
  have hc := Paper7Counting.lemma42_bounds b p q hb he hG
  have hzero := hc.2.2
  rw [hmax] at hzero
  have hnmax : (nOf b p q : ℝ) ≤ min (N : ℝ)
      (2 * S2 (SG b p q) - 2 * ((Bplus (SG b p q)).card : ℝ)) :=
    le_min (by exact_mod_cast hN) hc.2.1
  have hQ : ((∑ k ∈ I, q k : ℕ) : ℝ) ≤ ((∑ k, q k : ℕ) : ℝ) := by
    exact_mod_cast partial_sum_le_total b I q
  have hn : (nOf b p q : ℝ) = (b : ℝ) + ((∑ k, p k : ℕ) : ℝ) +
      2 * ((∑ k, q k : ℕ) : ℝ) := by
    simp only [nOf, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith
#print axioms Paper7PartialCounting.partial_counting_on_subset

theorem check_PartialAssignmentCounting :
    BackfillPaper7.Challenge.PartialAssignmentCounting := by
  intro b d N p q hb he _hd hG hN
  dsimp only
  intro hP
  exact partial_counting_on_subset b N p q hb he hG hN
    (Finset.univ.filter (fun k : Fin b => k.val < d)) hP
#print axioms Paper7PartialCounting.check_PartialAssignmentCounting

end Paper7PartialCounting
