import Research.Backfill.Paper7.ChallengeV3
import Research.Backfill.Paper7.IntegerRankBaseChange

/-! The exact six-part frozen integer-matrix contract, including empty index types. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Rank

open BackfillPaper7.Challenge.Legacy.Algebra

theorem rank_add_matrixNullity {K : Type} [Field K] {n : Type}
    [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    A.rank + matrixNullity A = Fintype.card n := by
  rw [Matrix.rank, matrixNullity, ← Matrix.toLin'_apply']
  simpa only [Module.finrank_fintype_fun_eq_card] using!
    (Matrix.toLin' A).finrank_range_add_finrank_ker

#print axioms Paper7Rank.rank_add_matrixNullity

theorem check_RankReductionAndNullity :
    BackfillPaper7.Challenge.Legacy.Algebra.RankReductionAndNullity := by
  intro n _ _ M ℓ hℓ
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hm : (overMod ℓ M).rank ≤ M.rank := by
    simpa only [overMod, Int.coe_castRingHom] using intCast_rank_le (ZMod ℓ) M
  have hq : (overQ M).rank = M.rank := by
    simpa only [overQ, Int.coe_castRingHom] using intCast_rank_eq ℚ M
  have hr : (overR M).rank = M.rank := by
    simpa only [overR, Int.coe_castRingHom] using intCast_rank_eq ℝ M
  have hmnull := rank_add_matrixNullity (overMod ℓ M)
  have hqnull := rank_add_matrixNullity (overQ M)
  have hrnull := rank_add_matrixNullity (overR M)
  exact ⟨by omega, by omega, hq.trans hr.symm, by omega, hmnull, hqnull⟩

#print axioms Paper7Rank.check_RankReductionAndNullity

end Paper7Rank
