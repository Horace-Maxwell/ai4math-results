import Research.Backfill.Paper7.SchurKernelEquivalence
import Research.Backfill.Paper7.SpectrumNullity
import Research.Backfill.Paper7.SunAttachmentCoupling
import Research.Backfill.Paper7.SunGraphBlocks

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Reduced

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Matrix

theorem overQ_adjacency_shift {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℤ) :
    overQ ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ)) =
      G.adjMatrix ℚ - (m : ℚ) • (1 : Matrix V V ℚ) := by
  ext i j
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;>
    simp [overQ, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.intCast_apply, SimpleGraph.adjMatrix_apply, hij, hadj]

#print axioms Paper7Reduced.overQ_adjacency_shift

theorem mult_eq_shift_nullity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℤ) :
    mult G (m : ℝ) =
      matrixNullity ((m : ℚ) • (1 : Matrix V V ℚ) - G.adjMatrix ℚ) := by
  rw [Paper7Spectrum.mult_eq_rational_nullity, overQ_adjacency_shift]
  have hneg : G.adjMatrix ℚ - (m : ℚ) • (1 : Matrix V V ℚ) =
      (-1 : ℚ) • ((m : ℚ) • (1 : Matrix V V ℚ) - G.adjMatrix ℚ) := by
    simp only [neg_one_smul, neg_sub]
  rw [hneg]
  exact nullity_smul_of_ne_zero _ (-1 : ℚ) (by norm_num)

#print axioms Paper7Reduced.mult_eq_shift_nullity

theorem scaledSchur_overQ (b : ℕ) (p q : Fin b → ℕ) (m : ℤ)
    (hx : (m : ℚ) ≠ 0) (hquad : (m : ℚ) ^ 2 - 1 ≠ 0) :
    overQ (scaledSchur b p q m) =
      (-((m : ℚ) * ((m : ℚ) ^ 2 - 1))) •
        (cycleShift b (m : ℚ) - Matrix.diagonal (fun k =>
          (p k : ℚ) / (m : ℚ) + (q k : ℚ) * (m : ℚ) / ((m : ℚ) ^ 2 - 1))) := by
  classical
  ext i j
  -- First expose every matrix action at its scalar entry, before the scalar
  -- simplifier can turn integer matrix smul into multiplication by a cast matrix.
  simp only [overQ, scaledSchur, cycleShift, cycleAdjZ, Matrix.map_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.adjMatrix_apply]
    field_simp [hx, hquad]
    ring
  · by_cases hadj : (SimpleGraph.cycleGraph b).Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, hij, hadj]

#print axioms Paper7Reduced.scaledSchur_overQ

theorem ordinary_reduced_multiplicity (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (m : ℤ) (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    mult (SG b p q) (m : ℝ) = matrixNullity (overQ (scaledSchur b p q m)) := by
  classical
  have hx : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hquad : (m : ℚ) ^ 2 - 1 ≠ 0 := by
    intro heq
    have hfac : ((m : ℚ) - 1) * ((m : ℚ) + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · have hcast : (m : ℚ) = 1 := by linarith
      exact hm1 (by exact_mod_cast hcast)
    · have hcast : (m : ℚ) = -1 := by linarith
      exact hmn (by exact_mod_cast hcast)
  let : Invertible (pendantShift (K := ℚ) b (pq b p q) (m : ℚ)) :=
    Matrix.invertibleOfIsUnitDet _
      (pendantShift_isUnit_det b p q (m : ℚ) hx hquad)
  calc
    mult (SG b p q) (m : ℝ) =
        matrixNullity ((m : ℚ) • (1 : Matrix (SunV b (pq b p q))
          (SunV b (pq b p q)) ℚ) - (SG b p q).adjMatrix ℚ) :=
      mult_eq_shift_nullity (SG b p q) m
    _ = matrixNullity (Matrix.fromBlocks (cycleShift b (m : ℚ))
        (attachment (K := ℚ) b (pq b p q))
        (attachment (K := ℚ) b (pq b p q)).transpose
        (pendantShift (K := ℚ) b (pq b p q) (m : ℚ))) := by
      rw [sun_shift_fromBlocks b (pq b p q) hb (m : ℚ)]
    _ = matrixNullity (cycleShift b (m : ℚ) - Matrix.diagonal (fun k =>
        (p k : ℚ) / (m : ℚ) + (q k : ℚ) * (m : ℚ) / ((m : ℚ) ^ 2 - 1))) := by
      rw [nullity_fromBlocks_eq_schur,
        attachment_inverse_coupling b p q (m : ℚ) hx hquad]
    _ = matrixNullity (overQ (scaledSchur b p q m)) := by
      rw [scaledSchur_overQ b p q m hx hquad]
      exact (nullity_smul_of_ne_zero _ _ (neg_ne_zero.mpr (mul_ne_zero hx hquad))).symm

#print axioms Paper7Reduced.ordinary_reduced_multiplicity

end Paper7Reduced
