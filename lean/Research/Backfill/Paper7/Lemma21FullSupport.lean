import Research.Backfill.Paper7.Lemma21SignedArms
import Research.Backfill.Paper7.ExceptionalCoreLift

/-! The full Kq / original Zq decomposition. No cycle vertex is discarded. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators
namespace Paper7Lemma21
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison Paper7Exceptional

abbrev FullCoreV (b : ℕ) (q : Fin b → ℕ) := QSupport b q ⊕ Zq b q
#print axioms Paper7Lemma21.FullCoreV

def fullYMap (b : ℕ) (q : Fin b → ℕ) :
    (FullCoreV b q → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  (subsetExtension b (Kq b q)).comp (LinearMap.funLeft ℝ ℝ Sum.inl)
#print axioms Paper7Lemma21.fullYMap

def fullZMap (b : ℕ) (q : Fin b → ℕ) :
    (FullCoreV b q → ℝ) →ₗ[ℝ] (Fin b → ℝ) :=
  (coordinateInclusion (fun k : Zq b q => k.1)).mulVecLin.comp
    (LinearMap.funLeft ℝ ℝ Sum.inr)
#print axioms Paper7Lemma21.fullZMap

def fullRootMap (b : ℕ) (q : Fin b → ℕ) :
    (FullCoreV b q → ℝ) →ₗ[ℝ] (Fin b → ℝ) := fullYMap b q + fullZMap b q
#print axioms Paper7Lemma21.fullRootMap

theorem fullZMap_at_support (b : ℕ) (q : Fin b → ℕ)
    (v : FullCoreV b q → ℝ) (k : QSupport b q) : fullZMap b q v k.1 = 0 := by
  classical
  change ∑ i : Zq b q, (coordinateInclusion (fun j : Zq b q => j.1)) k.1 i *
    v (Sum.inr i) = 0
  apply Finset.sum_eq_zero
  intro i _
  have hpos := (Finset.mem_filter.mp k.2).2
  have hne : k.1 ≠ i.1 := by
    intro h
    rw [h, i.2] at hpos
    omega
  simp [coordinateInclusion, hne]
#print axioms Paper7Lemma21.fullZMap_at_support

theorem fullRootMap_inl (b : ℕ) (q : Fin b → ℕ)
    (v : FullCoreV b q → ℝ) (k : QSupport b q) :
    fullRootMap b q v k.1 = v (Sum.inl k) := by
  change subsetExtension b (Kq b q) (fun i => v (Sum.inl i)) k.1 + fullZMap b q v k.1 = _
  rw [subsetExtension_mem, fullZMap_at_support, add_zero]
#print axioms Paper7Lemma21.fullRootMap_inl

theorem fullRootMap_inr (b : ℕ) (q : Fin b → ℕ)
    (v : FullCoreV b q → ℝ) (k : Zq b q) :
    fullRootMap b q v k.1 = v (Sum.inr k) := by
  have hn : k.1 ∉ Kq b q := by simp [Kq, k.2]
  change subsetExtension b (Kq b q) (fun i => v (Sum.inl i)) k.1 +
    (coordinateInclusion (fun i : Zq b q => i.1) *ᵥ (fun i => v (Sum.inr i))) k.1 = _
  rw [subsetExtension_not_mem b _ _ k.1 hn,
    coordinateInclusion_apply _ Subtype.val_injective, zero_add]
#print axioms Paper7Lemma21.fullRootMap_inr

theorem fullRootMap_injective (b : ℕ) (q : Fin b → ℕ) :
    Function.Injective (fullRootMap b q) := by
  intro v w h
  funext i
  rcases i with k | k
  · simpa only [fullRootMap_inl] using congrFun h k.1
  · simpa only [fullRootMap_inr] using congrFun h k.1
#print axioms Paper7Lemma21.fullRootMap_injective

def fullAmplitude (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    (FullCoreV b q → ℝ) →ₗ[ℝ] (QSupport b q → ℝ) :=
  (2 : ℝ)⁻¹ • (ε • LinearMap.funLeft ℝ ℝ Sum.inl -
    (2 : ℝ) • ((LinearMap.funLeft ℝ ℝ (fun k : QSupport b q => k.1)).comp
      ((signedCore b p ε).mulVecLin.comp (fullRootMap b q))) +
    ((LinearMap.funLeft ℝ ℝ (fun k : QSupport b q => k.1)).comp
      ((signedCore b p ε).mulVecLin.comp (fullYMap b q))))
#print axioms Paper7Lemma21.fullAmplitude

theorem fullAmplitude_apply (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : FullCoreV b q → ℝ) (k : QSupport b q) :
    fullAmplitude b p q ε v k = (2 : ℝ)⁻¹ *
      (ε * v (Sum.inl k) - 2 * (signedCore b p ε *ᵥ fullRootMap b q v) k.1 +
        (signedCore b p ε *ᵥ fullYMap b q v) k.1) := rfl
#print axioms Paper7Lemma21.fullAmplitude_apply

def fullDomain (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    Matrix (FullCoreV b q) (FullCoreV b q) ℝ :=
  Matrix.fromBlocks (Matrix.scalar (QSupport b q) ε) 0 0
    ((signedCore b p ε).submatrix (fun k : Zq b q => k.1) (fun k : Zq b q => k.1))
#print axioms Paper7Lemma21.fullDomain

theorem fullDomain_isHermitian (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    (fullDomain b p q ε).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · rw [Matrix.scalar_apply]
    exact Matrix.isHermitian_diagonal _
  · simp
  · exact (signedCore_isHermitian b p ε).submatrix _
#print axioms Paper7Lemma21.fullDomain_isHermitian

theorem fullZ_quadratic (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : FullCoreV b q → ℝ) :
    (signedCore b p ε).toQuadraticForm' (fullZMap b q v) =
      ((signedCore b p ε).submatrix (fun k : Zq b q => k.1)
        (fun k : Zq b q => k.1)).toQuadraticForm' (fun k => v (Sum.inr k)) := by
  change (signedCore b p ε).toQuadraticForm'
    (coordinateInclusion (fun k : Zq b q => k.1) *ᵥ
      (fun k : Zq b q => v (Sum.inr k))) = _
  have h := quadratic_rectangular_congruence (signedCore b p ε)
    (coordinateInclusion (fun k : Zq b q => k.1))
    (fun k : Zq b q => v (Sum.inr k))
  rw [coordinateInclusion_congruence (signedCore b p ε)
    (fun k : Zq b q => k.1)] at h
  exact h.symm
#print axioms Paper7Lemma21.fullZ_quadratic

theorem fullDomain_quadratic (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : FullCoreV b q → ℝ) :
    (fullDomain b p q ε).toQuadraticForm' v =
      ε * (∑ k : QSupport b q, v (Sum.inl k) ^ 2) +
      ((signedCore b p ε).submatrix (fun k : Zq b q => k.1)
        (fun k : Zq b q => k.1)).toQuadraticForm' (fun k => v (Sum.inr k)) := by
  have hv : v = Sum.elim (fun k => v (Sum.inl k)) (fun k => v (Sum.inr k)) := by
    funext i
    cases i <;> rfl
  conv_lhs => rw [hv]
  simp only [fullDomain, quadratic_apply, Matrix.fromBlocks_mulVec,
    Matrix.scalar_apply, Matrix.zero_mulVec, add_zero, zero_add,
    sumElim_dotProduct_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr]
  congr 1
  rw [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mulVec_diagonal]
  ring
#print axioms Paper7Lemma21.fullDomain_quadratic

theorem fullAmplitude_identity (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : FullCoreV b q → ℝ) :
    (signedCore b p ε).toQuadraticForm' (fullRootMap b q v) +
      2 * ∑ k : QSupport b q, fullRootMap b q v k.1 * fullAmplitude b p q ε v k =
      (fullDomain b p q ε).toQuadraticForm' v := by
  classical
  let s := fullYMap b q v
  let x := fullZMap b q v
  let r := fullRootMap b q v
  let A := signedCore b p ε
  have hr : r = s + x := rfl
  have hsym : A.IsSymm := by
    exact (SimpleGraph.cycleGraph b).isSymm_adjMatrix.add (Matrix.isSymm_diagonal _)
  have hs (w : Fin b → ℝ) : s ⬝ᵥ w = ∑ k : QSupport b q, v (Sum.inl k) * w k.1 :=
    subsetExtension_dot b (Kq b q) _ w
  have ha : 2 * (∑ k : QSupport b q, r k.1 * fullAmplitude b p q ε v k) =
      ε * (∑ k : QSupport b q, v (Sum.inl k) ^ 2) -
        2 * (s ⬝ᵥ (A *ᵥ r)) + s ⬝ᵥ (A *ᵥ s) := by
    simp only [hs]
    calc
      _ = ∑ k : QSupport b q, (ε * v (Sum.inl k) ^ 2 -
          2 * (v (Sum.inl k) * (A *ᵥ r) k.1) + v (Sum.inl k) * (A *ᵥ s) k.1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [fullAmplitude_apply]
        change 2 * (fullRootMap b q v k.1 * ((2 : ℝ)⁻¹ * _)) = _
        rw [fullRootMap_inl]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hc : A.toQuadraticForm' r - 2 * (s ⬝ᵥ (A *ᵥ r)) +
      s ⬝ᵥ (A *ᵥ s) = A.toQuadraticForm' x := by
    have hcross : s ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ s) := hsym.dotProduct_mulVec_comm
    simp only [hr, quadratic_apply, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    linarith
  rw [fullDomain_quadratic]
  have hx := fullZ_quadratic b p q ε v
  change A.toQuadraticForm' r + 2 * (∑ k : QSupport b q,
    r k.1 * fullAmplitude b p q ε v k) = _
  rw [ha]
  change A.toQuadraticForm' x = _ at hx
  linarith
#print axioms Paper7Lemma21.fullAmplitude_identity

theorem signedCore_R (b : ℕ) (p q : Fin b → ℕ) :
    (signedCore b p 1).submatrix (fun k : Zq b q => k.1) (fun k : Zq b q => k.1) =
      Rmat b p q := by
  apply Matrix.ext
  intro i j
  by_cases hij : i.1 = j.1 <;>
    simp [signedCore, Rmat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply, hij]
  ring
#print axioms Paper7Lemma21.signedCore_R

theorem signedCore_R' (b : ℕ) (p q : Fin b → ℕ) :
    (signedCore b p (-1)).submatrix (fun k : Zq b q => k.1) (fun k : Zq b q => k.1) =
      R'mat b p q := by
  apply Matrix.ext
  intro i j
  by_cases hij : i.1 = j.1 <;>
    simp [signedCore, R'mat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply, hij]
  ring
#print axioms Paper7Lemma21.signedCore_R'

theorem fullDomain_inertia (b : ℕ) (p q : Fin b → ℕ) :
    nPos (fullDomain b p q 1) = (Kq b q).card + nPos (Rmat b p q) ∧
    nNeg (fullDomain b p q (-1)) = (Kq b q).card + nNeg (R'mat b p q) := by
  have hp : nPos (Matrix.scalar (QSupport b q) (1 : ℝ)) = (Kq b q).card := by
    rw [Matrix.scalar_apply, (inertia_diagonal _).1]
    simp [QSupport]
  have hn : nNeg (Matrix.scalar (QSupport b q) (-1 : ℝ)) = (Kq b q).card := by
    rw [Matrix.scalar_apply, (inertia_diagonal _).2]
    simp [QSupport]
  constructor
  · rw [fullDomain, (inertia_block_diagonal _ _).1, hp, signedCore_R]
  · rw [fullDomain, (inertia_block_diagonal _ _).2, hn, signedCore_R']
#print axioms Paper7Lemma21.fullDomain_inertia

end Paper7Lemma21
