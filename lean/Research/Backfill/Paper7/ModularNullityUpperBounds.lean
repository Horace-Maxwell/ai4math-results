import Research.Backfill.Paper7.RankReductionAndNullity
import Research.Backfill.Paper7.ReducedMultiplicityExactness

/-! Complete frozen MIN-05. No invertibility modulo the prime is assumed. -/
set_option autoImplicit false

namespace Paper7ModularNullity
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem check_ModularNullityUpperBounds :
    BackfillPaper7.Challenge.Legacy.Algebra.ModularNullityUpperBounds := by
  intro ℓ hℓ b p q hb m
  classical
  rcases Paper7Reduced.check_ReducedMultiplicityExactness b p q hb with
    ⟨_, _, _, _, hord, hzero, hsign⟩
  have hn (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n ℤ) :
      matrixNullity (overQ M) ≤ matrixNullity (overMod ℓ M) :=
    (Paper7Rank.check_RankReductionAndNullity n M ℓ hℓ).2.1
  by_cases h0 : m = 0
  · subst m
    simp only [modularMultiplicityBound, Int.cast_zero, ↓reduceIte]
    rw [hzero]
    exact Nat.add_le_add_left (hn _ (zeroSystem b p)) _
  · by_cases hs : m = 1 ∨ m = -1
    · simp only [modularMultiplicityBound, h0, hs, ↓reduceIte]
      rw [hsign m hs]
      exact Nat.add_le_add_left (hn _ (signSystem b p q m)) _
    · simp only [modularMultiplicityBound, h0, hs, ↓reduceIte]
      rw [hord m (fun h => hs (Or.inr h)) h0 (fun h => hs (Or.inl h))]
      exact hn _ (scaledSchur b p q m)

#print axioms Paper7ModularNullity.check_ModularNullityUpperBounds
end Paper7ModularNullity
