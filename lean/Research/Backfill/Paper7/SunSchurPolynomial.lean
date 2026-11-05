import Research.Backfill.Paper7.SunAttachmentCoupling
import Research.Backfill.Paper7.SunGraphBlocks
import Research.Backfill.Paper7.SchurClearing

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem graphPhi_eval_det_shift {K : Type*} [CommRing K]
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : K) :
    Polynomial.eval₂RingHom (Int.castRingHom K) x (graphPhi G) =
      (x • (1 : Matrix V V K) - G.adjMatrix K).det := by
  classical
  unfold graphPhi Matrix.charpoly
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;>
    simp [Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      SimpleGraph.adjMatrix_apply, hij, hadj]

#print axioms Paper7Cleared.graphPhi_eval_det_shift

theorem eval_clearedMatrix {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    (clearedMatrix b p q).map (Polynomial.eval₂RingHom (Int.castRingHom K) x) =
      (x * (x ^ 2 - 1)) •
        (cycleShift b x - Matrix.diagonal (fun k =>
          (p k : K) / x + (q k : K) * x / (x ^ 2 - 1))) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [clearedMatrix, cycleShift, cycleAdjZ, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply,
       SimpleGraph.adjMatrix_apply]
    all_goals field_simp [hx, hquad]
  · by_cases hadj : (SimpleGraph.cycleGraph b).Adj i j <;>
      simp [clearedMatrix, cycleShift, cycleAdjZ, Matrix.map_apply,
        Matrix.sub_apply, Matrix.smul_apply,
         SimpleGraph.adjMatrix_apply, hij, hadj]

#print axioms Paper7Cleared.eval_clearedMatrix

theorem eval_cleared_identity {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    x ^ totalP b p * (x ^ 2 - 1) ^ totalQ b q *
        Polynomial.eval₂RingHom (Int.castRingHom K) x (clearedF b p q) =
      x ^ b * (x ^ 2 - 1) ^ b *
        Polynomial.eval₂RingHom (Int.castRingHom K) x (graphPhi (SG b p q)) := by
  classical
  let : Invertible (pendantShift b (pq b p q) x) :=
    Matrix.invertibleOfIsUnitDet _ (pendantShift_isUnit_det b p q x hx hquad)
  have hs := scaled_schur_det (cycleShift b x) (attachment b (pq b p q))
    (attachment b (pq b p q)).transpose (pendantShift b (pq b p q) x) (x * (x ^ 2 - 1))
  rw [Matrix.invOf_eq_nonsing_inv, attachment_inverse_coupling b p q x hx hquad] at hs
  have hF : Polynomial.eval₂RingHom (Int.castRingHom K) x (clearedF b p q) =
      ((x * (x ^ 2 - 1)) •
        (cycleShift b x - Matrix.diagonal (fun k =>
          (p k : K) / x + (q k : K) * x / (x ^ 2 - 1)))).det := by
    unfold clearedF
    rw [RingHom.map_det]
    simpa only [RingHom.mapMatrix_apply] using!
      (congrArg (fun M : Matrix (Fin b) (Fin b) K => M.det)
        (eval_clearedMatrix b p q x hx hquad))
  have hG : Polynomial.eval₂RingHom (Int.castRingHom K) x (graphPhi (SG b p q)) =
      (Matrix.fromBlocks (cycleShift b x) (attachment b (pq b p q))
        (attachment b (pq b p q)).transpose (pendantShift b (pq b p q) x)).det := by
    rw [graphPhi_eval_det_shift, sun_shift_fromBlocks b (pq b p q) hb x]
  rw [pendantShift_det, ← hF, ← hG, Fintype.card_fin, mul_pow] at hs
  exact hs

#print axioms Paper7Cleared.eval_cleared_identity

end Paper7Cleared
