import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem pq_sum_lengths (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) :
    (∑ j : Fin ((pq b p q k).length), (pq b p q k).get j) = p k + 2 * q k := by
  change (∑ j : Fin ((pq b p q k).length), (pq b p q k)[j.val]) = _
  rw [Fin.sum_univ_getElem]
  simp [pq, Nat.mul_comm]

#print axioms Paper7Cleared.pq_sum_lengths

theorem card_sun_pq (b : ℕ) (p q : Fin b → ℕ) :
    Fintype.card (SunV b (pq b p q)) = b + totalP b p + 2 * totalQ b q := by
  simp only [SunV, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [pq_sum_lengths]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold totalP totalQ
  omega

#print axioms Paper7Cleared.card_sun_pq

end Paper7Cleared
