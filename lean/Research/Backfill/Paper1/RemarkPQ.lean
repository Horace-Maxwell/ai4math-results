import Research.Backfill.Paper1.RemarkPQFinite

/-! All clauses of the frozen Remark16. Acceptance status is recorded separately.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1

theorem check_Remark16 : Challenge.Remark16 := by
  refine ⟨?_,RemarkPQ.maximum_135,RemarkPQ.maximum_375,
    RemarkPQ.mult_maximum_135,RemarkPQ.mult_maximum_375,?_,?_,?_,?_⟩
  · intro p q hpq
    obtain ⟨e1,epq,ep,e1p,eq,e1q,eall⟩ := RemarkPQ.energy_table hpq
    refine ⟨RemarkPQ.maximum_pq hpq,RemarkPQ.mult_maximum_pq hpq,
      ?_,?_,ep,e1p,eq,e1q,eall⟩
    · rw [e1,RemarkPQ.totient_pq hpq]
      ring
    · rw [epq,RemarkPQ.totient_pq hpq]
      ring
  · exact RemarkPQ.not_mult_maximizer_135 _ (by simp)
  · exact RemarkPQ.not_mult_maximizer_135 _ (by simp)
  · exact RemarkPQ.not_mult_maximizer_375 _ (by simp)
  · exact RemarkPQ.not_mult_maximizer_375 _ (by simp)

#print axioms check_Remark16
end CodexPaper1
