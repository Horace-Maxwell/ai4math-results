import Research.Backfill.Paper7.ZeroGapDimension
import Research.Backfill.Paper7.Lemma22ZeroEmpty

/-! Exact original even-gap count and the complete frozen zero-offset clause.
No component-dimension or gap-cover hypothesis is added. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem zero_deltaE_eq_evenGaps (b : ℕ) (q : Fin b → ℕ) (hb : 3 ≤ b)
    (hK : (Kq b q).Nonempty) :
    deltaE b (fun _ => 0) q 0 = evenGaps b (Kq b q) := by
  classical
  calc
    deltaE b (fun _ => 0) q 0 = ∑ k ∈ Kq b q, gapDim b (fun _ => 0) q 0 k :=
      deltaE_eq_sum_gapDim b (fun _ => 0) q 0 hK
    _ = ∑ k : {k : Fin b // k ∈ Kq b q}, gapDim b (fun _ => 0) q 0 k.1 :=
      (Finset.sum_coe_sort (Kq b q) (fun k => gapDim b (fun _ => 0) q 0 k)).symm
    _ = ∑ k : {k : Fin b // k ∈ Kq b q},
        if Even (firstHitLength b (Kq b q) k.1 k.2) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      exact zero_gapDim_eq b q hb k.1 k.2
    _ = evenGaps b (Kq b q) := (evenGaps_eq_sum_firstHit b (Kq b q)).symm
#print axioms Paper7Lemma22Gaps.zero_deltaE_eq_evenGaps

theorem zero_nullity_eq_delta0 (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    matrixNullity (overQ (zeroSystem b p)) = delta0 b p := by
  classical
  by_cases hK : Kp b p = ∅
  · rw [delta0, ite_eq_left hK]
    exact zero_nullity_empty_support b p hb hK
  · have hKq : (Kq b p).Nonempty := Finset.nonempty_iff_ne_empty.mpr hK
    calc
      matrixNullity (overQ (zeroSystem b p)) = deltaE b (fun _ => 0) p 0 :=
        zero_nullity_eq_deltaE_zero b p hb
      _ = evenGaps b (Kq b p) := zero_deltaE_eq_evenGaps b p hb hKq
      _ = delta0 b p := by rw [delta0, ite_eq_right hK]; rfl
#print axioms Paper7Lemma22Gaps.zero_nullity_eq_delta0

/-- The entire original zero-offset clause, including both support cases. -/
theorem lemma22_zero_clause (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 + (Kp b p).card = ∑ k, p k + delta0 b p := by
  have h := Paper7Lemma22.zero_offset_reduced b p q hb
  rw [zero_nullity_eq_delta0 b p hb] at h
  exact h
#print axioms Paper7Lemma22Gaps.lemma22_zero_clause

end Paper7Lemma22Gaps
