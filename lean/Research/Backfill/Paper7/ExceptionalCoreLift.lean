import Research.Backfill.Paper7.ExceptionalArmLift
import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.TridiagonalComparison

/-! A simultaneous Y-positive block and residual-core embedding. The amplitudes
are explicit linear functions; the form identity is proved, never assumed. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Exceptional
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

def subsetExtension (b : ℕ) (S : Finset (Fin b)) : (S → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  (coordinateInclusion (fun i : S => i.1)).mulVecLin
#print axioms Paper7Exceptional.subsetExtension

theorem subsetExtension_mem (b : ℕ) (S : Finset (Fin b)) (x : S → ℝ) (i : S) :
    subsetExtension b S x i.1 = x i :=
  coordinateInclusion_apply _ Subtype.val_injective x i
#print axioms Paper7Exceptional.subsetExtension_mem

theorem subsetExtension_not_mem (b : ℕ) (S : Finset (Fin b)) (x : S → ℝ)
    (j : Fin b) (hj : j ∉ S) : subsetExtension b S x j = 0 := by
  classical
  change ∑ i : S, (coordinateInclusion (fun i : S => i.1)) j i * x i = 0
  apply Finset.sum_eq_zero
  intro i _
  have hne : j ≠ i.1 := fun h => hj (h.symm ▸ i.2)
  simp [coordinateInclusion, hne]
#print axioms Paper7Exceptional.subsetExtension_not_mem

theorem subsetExtension_dot (b : ℕ) (S : Finset (Fin b)) (x : S → ℝ) (y : Fin b → ℝ) :
    subsetExtension b S x ⬝ᵥ y = ∑ i : S, x i * y i.1 := by
  classical
  calc
    _ = ∑ j : Fin b, if hj : j ∈ S then x ⟨j, hj⟩ * y j else 0 := by
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · rw [dite_eq_left hj, subsetExtension_mem b S x ⟨j, hj⟩]
      · rw [dite_eq_right hj, subsetExtension_not_mem b S x j hj, zero_mul]
    _ = _ := by
      have hu := sum_subtype_extend_real (fun j : Fin b => j ∈ S)
        (fun i => x i * y i.1)
      rw [Subsingleton.elim (Subtype.fintype (fun j : Fin b => j ∈ S))
        (Finset.Subtype.fintype S)] at hu
      exact hu
#print axioms Paper7Exceptional.subsetExtension_dot

def coreYMap (b : ℕ) (Y : Finset (Fin b)) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  (subsetExtension b Y).comp (LinearMap.funLeft ℝ ℝ Sum.inl)
#print axioms Paper7Exceptional.coreYMap

def coreResidualMap (b : ℕ) (Y : Finset (Fin b)) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  (subsetExtension b (Xset b \ Y)).comp (LinearMap.funLeft ℝ ℝ Sum.inr)
#print axioms Paper7Exceptional.coreResidualMap

def coreRootMap (b : ℕ) (Y : Finset (Fin b)) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  coreYMap b Y + coreResidualMap b Y
#print axioms Paper7Exceptional.coreRootMap

theorem coreRootMap_inl (b : ℕ) (Y : Finset (Fin b))
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) (k : Y) : coreRootMap b Y v k.1 = v (Sum.inl k) := by
  have hn : k.1 ∉ Xset b \ Y := fun h => (Finset.mem_sdiff.mp h).2 k.2
  change subsetExtension b Y (fun i => v (Sum.inl i)) k.1 +
    subsetExtension b (Xset b \ Y) (fun i => v (Sum.inr i)) k.1 = _
  rw [subsetExtension_mem, subsetExtension_not_mem b _ _ k.1 hn, add_zero]
#print axioms Paper7Exceptional.coreRootMap_inl

theorem coreRootMap_inr (b : ℕ) (Y : Finset (Fin b))
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) (k : ↥(Xset b \ Y)) :
    coreRootMap b Y v k.1 = v (Sum.inr k) := by
  have hn : k.1 ∉ Y := (Finset.mem_sdiff.mp k.2).2
  change subsetExtension b Y (fun i => v (Sum.inl i)) k.1 +
    subsetExtension b (Xset b \ Y) (fun i => v (Sum.inr i)) k.1 = _
  rw [subsetExtension_not_mem b _ _ k.1 hn, subsetExtension_mem, zero_add]
#print axioms Paper7Exceptional.coreRootMap_inr

theorem coreRootMap_injective (b : ℕ) (Y : Finset (Fin b)) :
    Function.Injective (coreRootMap b Y) := by
  intro v w h
  funext i
  rcases i with k | k
  · simpa only [coreRootMap_inl] using congrFun h k.1
  · simpa only [coreRootMap_inr] using congrFun h k.1
#print axioms Paper7Exceptional.coreRootMap_injective

theorem coreRootMap_support (b : ℕ) (Y : Finset (Fin b)) (hY : Y ⊆ Xset b)
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) (k : Fin b) (hk : k ∉ Xset b) :
    coreRootMap b Y v k = 0 := by
  have hy : k ∉ Y := fun h => hk (hY h)
  have hz : k ∉ Xset b \ Y := fun h => hk (Finset.mem_sdiff.mp h).1
  change subsetExtension b Y _ k + subsetExtension b (Xset b \ Y) _ k = 0
  rw [subsetExtension_not_mem b _ _ k hy, subsetExtension_not_mem b _ _ k hz, zero_add]
#print axioms Paper7Exceptional.coreRootMap_support

def coreAmplitudeMap (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b)) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (Y → ℝ) :=
  (2 : ℝ)⁻¹ • (LinearMap.funLeft ℝ ℝ Sum.inl -
    (2 : ℝ) • ((LinearMap.funLeft ℝ ℝ (fun k : Y => k.1)).comp
      ((unitCoreMatrix b p).mulVecLin.comp (coreRootMap b Y))) +
    ((LinearMap.funLeft ℝ ℝ (fun k : Y => k.1)).comp
      ((unitCoreMatrix b p).mulVecLin.comp (coreYMap b Y))))
#print axioms Paper7Exceptional.coreAmplitudeMap

theorem coreAmplitudeMap_apply (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b))
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) (k : Y) :
    coreAmplitudeMap b p Y v k = (2 : ℝ)⁻¹ *
      (v (Sum.inl k) - 2 * (unitCoreMatrix b p *ᵥ coreRootMap b Y v) k.1 +
        (unitCoreMatrix b p *ᵥ coreYMap b Y v) k.1) := rfl
#print axioms Paper7Exceptional.coreAmplitudeMap_apply

def exceptionalDomainMatrix (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b)) :
    Matrix (Y ⊕ ↥(Xset b \ Y)) (Y ⊕ ↥(Xset b \ Y)) ℝ :=
  Matrix.fromBlocks (1 : Matrix Y Y ℝ) 0 0
    (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1))
#print axioms Paper7Exceptional.exceptionalDomainMatrix

theorem exceptionalDomainMatrix_isHermitian (b : ℕ) (p : Fin b → ℕ)
    (Y : Finset (Fin b)) : (exceptionalDomainMatrix b p Y).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp)
    (tridiag_isHermitian _ _)
#print axioms Paper7Exceptional.exceptionalDomainMatrix_isHermitian

theorem exceptionalDomainMatrix_nPos (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b)) :
    nPos (exceptionalDomainMatrix b p Y) =
      Y.card + nPos (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1)) := by
  classical
  have hi : nPos (1 : Matrix Y Y ℝ) = Y.card := by
    have hdiag : (1 : Matrix Y Y ℝ) = Matrix.diagonal (fun _ : Y => (1 : ℝ)) := by
      apply Matrix.ext
      intro i j
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    rw [hdiag, (inertia_diagonal _).1]
    simp
  rw [exceptionalDomainMatrix, (inertia_block_diagonal _ _).1, hi]
#print axioms Paper7Exceptional.exceptionalDomainMatrix_nPos

theorem coreResidual_quadratic (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b))
    (hb : 3 ≤ b) (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    (unitCoreMatrix b p).toQuadraticForm' (coreResidualMap b Y v) =
      (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1)).toQuadraticForm'
        (fun k => v (Sum.inr k)) := by
  have hZ : Xset b \ Y ⊆ Xset b := fun _ h => (Finset.mem_sdiff.mp h).1
  have hc := cycle_diagonal_compression b hb (Xset b \ Y) hZ (fun k => (p k : ℝ) - 1)
  calc
    _ = ((unitCoreMatrix b p).submatrix
        (fun i : ↥(Xset b \ Y) => i.1) (fun i : ↥(Xset b \ Y) => i.1)).toQuadraticForm'
          (fun k => v (Sum.inr k)) := by
      rw [← coordinateInclusion_congruence]
      exact (quadratic_rectangular_congruence _ _ _).symm
    _ = _ := congrArg (fun M => M.toQuadraticForm' (fun k => v (Sum.inr k))) hc
#print axioms Paper7Exceptional.coreResidual_quadratic

theorem exceptionalDomainMatrix_quadratic (b : ℕ) (p : Fin b → ℕ)
    (Y : Finset (Fin b)) (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    (exceptionalDomainMatrix b p Y).toQuadraticForm' v =
      (∑ k : Y, v (Sum.inl k) ^ 2) +
      (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1)).toQuadraticForm'
        (fun k => v (Sum.inr k)) := by
  have hv : v = Sum.elim (fun k => v (Sum.inl k)) (fun k => v (Sum.inr k)) := by
    funext i
    cases i <;> rfl
  conv_lhs => rw [hv]
  simp only [exceptionalDomainMatrix, quadratic_apply, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pow_two]
#print axioms Paper7Exceptional.exceptionalDomainMatrix_quadratic

/-- Every Y direction is present simultaneously. The explicit amplitude cancels
all Y/core cross terms and leaves the original residual tridiagonal form. -/
theorem core_amplitude_identity (b : ℕ) (p : Fin b → ℕ) (Y : Finset (Fin b))
    (hb : 3 ≤ b) (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    (unitCoreMatrix b p).toQuadraticForm' (coreRootMap b Y v) +
        2 * ∑ k : Y, coreRootMap b Y v k.1 * coreAmplitudeMap b p Y v k =
      (exceptionalDomainMatrix b p Y).toQuadraticForm' v := by
  classical
  let s := coreYMap b Y v
  let x := coreResidualMap b Y v
  let r := coreRootMap b Y v
  let A := unitCoreMatrix b p
  have hr : r = s + x := rfl
  have hsym : A.IsSymm := by
    exact (SimpleGraph.cycleGraph b).isSymm_adjMatrix.add (Matrix.isSymm_diagonal _)
  have hs (w : Fin b → ℝ) : s ⬝ᵥ w = ∑ k : Y, v (Sum.inl k) * w k.1 :=
    subsetExtension_dot b Y _ w
  have ha : 2 * (∑ k : Y, r k.1 * coreAmplitudeMap b p Y v k) =
      (∑ k : Y, v (Sum.inl k) ^ 2) - 2 * (s ⬝ᵥ (A *ᵥ r)) + s ⬝ᵥ (A *ᵥ s) := by
    simp only [hs]
    calc
      _ = ∑ k : Y, (v (Sum.inl k) ^ 2 -
          2 * (v (Sum.inl k) * (A *ᵥ r) k.1) + v (Sum.inl k) * (A *ᵥ s) k.1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [coreAmplitudeMap_apply]
        change 2 * (coreRootMap b Y v k.1 * ((2 : ℝ)⁻¹ * _)) = _
        rw [coreRootMap_inl]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hcancel : A.toQuadraticForm' r - 2 * (s ⬝ᵥ (A *ᵥ r)) +
      s ⬝ᵥ (A *ᵥ s) = A.toQuadraticForm' x := by
    have hcross : s ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ s) := hsym.dotProduct_mulVec_comm
    simp only [hr, quadratic_apply, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    linarith
  rw [exceptionalDomainMatrix_quadratic]
  have hx := coreResidual_quadratic b p Y hb v
  change A.toQuadraticForm' r + 2 * (∑ k : Y, r k.1 * coreAmplitudeMap b p Y v k) = _
  rw [ha]
  change A.toQuadraticForm' x = _ at hx
  linarith
#print axioms Paper7Exceptional.core_amplitude_identity

end Paper7Exceptional
