import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.TridiagonalComparison
import Research.Backfill.Paper7.SunAttachmentCoupling
import Research.Backfill.Paper7.SunGraphBlocks

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Inertia Paper7Cleared
open scoped Matrix

theorem smat_isHermitian (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    (Smat b p q m).IsHermitian := by
  rw [smat_as_cycle_diagonal]
  exact ((SimpleGraph.cycleGraph b).isHermitian_adjMatrix ℝ).add
    (Matrix.isHermitian_diagonal _)
#print axioms Paper7Comparison.smat_isHermitian

theorem shifted_adj_isHermitian {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    (G.adjMatrix ℝ - Matrix.scalar V m).IsHermitian := by
  rw [Matrix.scalar_apply]
  exact (G.isHermitian_adjMatrix ℝ).sub (Matrix.isHermitian_diagonal _)
#print axioms Paper7Comparison.shifted_adj_isHermitian

/-- This is an actual map into the original frozen dependent SunV coordinates. -/
def sunSchurLift (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    (Fin b → ℝ) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) :=
  schurLift ((pendantShift (K := ℝ) b (pq b p q) m)⁻¹ *
    (attachment (K := ℝ) b (pq b p q)).transpose)
#print axioms Paper7Comparison.sunSchurLift

theorem sunSchurLift_injective (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    Function.Injective (sunSchurLift b p q m) := schurLift_injective _
#print axioms Paper7Comparison.sunSchurLift_injective

/-- The original graph's shifted form agrees exactly with Smat on the Schur lift.
No integrality, spectral symmetry, or extra inertia hypothesis is used. -/
theorem sunSchurLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (m : ℝ) (hm0 : m ≠ 0) (hmq : m ^ 2 - 1 ≠ 0) (x : Fin b → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m).toQuadraticForm'
        (sunSchurLift b p q m x) =
      (Smat b p q m).toQuadraticForm' x := by
  let A : Matrix (Fin b) (Fin b) ℝ := cycleShift b m
  let B : Matrix (Fin b) (ArmV b (pq b p q)) ℝ := attachment b (pq b p q)
  let D : Matrix (ArmV b (pq b p q)) (ArmV b (pq b p q)) ℝ :=
    pendantShift b (pq b p q) m
  let R : Matrix (ArmV b (pq b p q)) (Fin b) ℝ := D⁻¹ * Bᵀ
  have hDR : D * R = Bᵀ := by
    exact Matrix.mul_nonsing_inv_cancel_left D Bᵀ
      (pendantShift_isUnit_det b p q m hm0 hmq)
  have hS : A - B * R = -(Smat b p q m) := by
    change cycleShift b m -
        attachment b (pq b p q) *
          ((pendantShift (K := ℝ) b (pq b p q) m)⁻¹ *
            (attachment b (pq b p q)).transpose) = _
    rw [← Matrix.mul_assoc, attachment_inverse_coupling b p q m hm0 hmq]
    unfold cycleShift Smat Cyc fk
    abel
  have hM : (SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m =
      -(Matrix.fromBlocks A B Bᵀ D) := by
    change (sunGraph b (pq b p q)).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m = _
    rw [show Matrix.fromBlocks A B Bᵀ D =
        m • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℝ) -
          (sunGraph b (pq b p q)).adjMatrix ℝ from
      (sun_shift_fromBlocks b (pq b p q) hb m).symm]
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    abel
  change ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m).toQuadraticForm'
      (schurLift R x) = _
  rw [hM, quadratic_neg_apply, schurLift_quadratic A B Bᵀ D R hDR x,
    hS, quadratic_neg_apply, neg_neg]
#print axioms Paper7Comparison.sunSchurLift_quadratic

/-- All four inertia comparisons for the ordinary real Schur reduction. -/
theorem sunSchur_inertia_bounds (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (m : ℝ) (hm0 : m ≠ 0) (hmq : m ^ 2 - 1 ≠ 0) :
    nPos (Smat b p q m) ≤ Ngt (SG b p q) m ∧
      nNeg (Smat b p q m) ≤ Nlt (SG b p q) m ∧
      nPos (Smat b p q m) + nZero (Smat b p q m) ≤ Nge (SG b p q) m ∧
      nNeg (Smat b p q m) + nZero (Smat b p q m) ≤ Nle (SG b p q) m := by
  let M := (SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m
  have hM : M.IsHermitian := shifted_adj_isHermitian (SG b p q) m
  have hS := smat_isHermitian b p q m
  have hf := sunSchurLift_injective b p q m
  have hq := sunSchurLift_quadratic b p q hb m hm0 hmq
  have hp := nPos_map_le (Smat b p q m) M hS hM (sunSchurLift b p q m) hf
    (fun x => (hq x).symm.le)
  have hn := nNeg_map_le (Smat b p q m) M hS hM (sunSchurLift b p q m) hf
    (fun x => (hq x).le)
  have hpn := nonneg_map_le (Smat b p q m) M hS hM (sunSchurLift b p q m) hf
    (fun x => (hq x).symm.le)
  have hnn := nonpos_map_le (Smat b p q m) M hS hM (sunSchurLift b p q m) hf
    (fun x => (hq x).le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [M, nPos_shift_eq_Ngt] using hp
  · simpa only [M, nNeg_shift_eq_Nlt] using hn
  · simpa only [M, nonneg_shift_eq_Nge] using hpn
  · simpa only [M, nonpos_shift_eq_Nle] using hnn
#print axioms Paper7Comparison.sunSchur_inertia_bounds

/-- Restricting to any subset of Xset removes exactly the cycle wrap edge. -/
theorem sunSchur_compressed_bounds (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Xset b)
    (m : ℝ) (hm0 : m ≠ 0) (hmq : m ^ 2 - 1 ≠ 0) :
    nPos (tridiag Y (fun k => fk b p q m k - m)) ≤ Ngt (SG b p q) m ∧
      nNeg (tridiag Y (fun k => fk b p q m k - m)) ≤ Nlt (SG b p q) m ∧
      nPos (tridiag Y (fun k => fk b p q m k - m)) +
        nZero (tridiag Y (fun k => fk b p q m k - m)) ≤ Nge (SG b p q) m ∧
      nNeg (tridiag Y (fun k => fk b p q m k - m)) +
        nZero (tridiag Y (fun k => fk b p q m k - m)) ≤ Nle (SG b p q) m := by
  have hp := principal_inertia_bounds (Smat b p q m) (smat_isHermitian b p q m)
    (fun i : Y => i.val) Subtype.val_injective
  have hn := principal_negative_inertia_bounds (Smat b p q m) (smat_isHermitian b p q m)
    (fun i : Y => i.val) Subtype.val_injective
  have hc : (Smat b p q m).submatrix (fun i : Y => i.val) (fun i : Y => i.val) =
      tridiag Y (fun k => fk b p q m k - m) := by
    rw [smat_as_cycle_diagonal]
    exact cycle_diagonal_compression b hb Y hY _
  rw [hc] at hp hn
  have hs := sunSchur_inertia_bounds b p q hb m hm0 hmq
  exact ⟨hp.1.trans hs.1, hn.1.trans hs.2.1,
    hp.2.trans hs.2.2.1, hn.2.trans hs.2.2.2⟩
#print axioms Paper7Comparison.sunSchur_compressed_bounds

end Paper7Comparison
