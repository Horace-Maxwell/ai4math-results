import Research.Backfill.Paper7.PQArmCoordinates
import Research.Backfill.Paper7.InertiaQuadraticBridge

/-! Simultaneous selection of one actual P2 arm at each vertex of Y and its
threshold-one quadratic contribution in the original dependent SunV indices. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Exceptional
open BackfillPaper7.Challenge Paper7Cleared Paper7Reduced Paper7Inertia

def chosenTwoArm (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) (hq : 0 < q k) :
    PQArmIndex b p q 2 k :=
  Classical.choice (Fintype.card_pos_iff.mp (by
    rw [card_PQArmIndex_two]
    exact hq))
#print axioms Paper7Exceptional.chosenTwoArm

theorem q_pos_of_mem_Y (b : ℕ) (q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (k : Y) : 0 < q k.1 :=
  (Finset.mem_filter.mp (Finset.mem_inter.mp (hY k.2)).1).2
#print axioms Paper7Exceptional.q_pos_of_mem_Y

def selectedArm (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (k : Y) : PQArmIndex b p q 2 k.1 :=
  chosenTwoArm b p q k.1 (q_pos_of_mem_Y b q Y hY k)
#print axioms Paper7Exceptional.selectedArm

def unitArmValue (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) : ℝ :=
  if (pq b p q k).get j = 1 then r k
  else if hk : k ∈ Y then
    if j = (selectedArm b p q Y hY ⟨k, hk⟩).1 then a ⟨k, hk⟩ else 0
  else 0
#print axioms Paper7Exceptional.unitArmValue

def unitArmVector (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ) :
    ArmV b (pq b p q) → ℝ :=
  fun v => unitArmValue b p q Y hY r a v.1 v.2.1
#print axioms Paper7Exceptional.unitArmVector

def unitLift (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) :
    ((Fin b → ℝ) × (Y → ℝ)) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) where
  toFun z := Sum.elim z.1 (unitArmVector b p q Y hY z.1 z.2)
  map_add' z w := by
    funext v
    rcases v with k | ⟨k, j, i⟩
    · rfl
    · change unitArmValue b p q Y hY (z.1 + w.1) (z.2 + w.2) k j =
        unitArmValue b p q Y hY z.1 z.2 k j + unitArmValue b p q Y hY w.1 w.2 k j
      unfold unitArmValue
      split_ifs <;> simp
  map_smul' c z := by
    funext v
    rcases v with k | ⟨k, j, i⟩
    · rfl
    · change unitArmValue b p q Y hY (c • z.1) (c • z.2) k j =
        c * unitArmValue b p q Y hY z.1 z.2 k j
      unfold unitArmValue
      split_ifs <;> simp
#print axioms Paper7Exceptional.unitLift

theorem unitLift_root (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ) (k : Fin b) :
    unitLift b p q Y hY (r, a) (Sum.inl k) = r k := rfl
#print axioms Paper7Exceptional.unitLift_root

theorem unitArmValue_split (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) :
    unitArmValue b p q Y hY r a k j =
      (if (pq b p q k).get j = 1 then r k else 0) +
      (if hk : k ∈ Y then
        if j = (selectedArm b p q Y hY ⟨k, hk⟩).1 then a ⟨k, hk⟩ else 0
       else 0) := by
  classical
  by_cases h1 : (pq b p q k).get j = 1
  · by_cases hk : k ∈ Y
    · have hne : j ≠ (selectedArm b p q Y hY ⟨k, hk⟩).1 := by
        intro he
        have h2 := (selectedArm b p q Y hY ⟨k, hk⟩).2
        rw [← he, h1] at h2
        norm_num at h2
      simp only [List.get_eq_getElem] at h1
      simp [unitArmValue, h1, hk, hne]
    · simp only [List.get_eq_getElem] at h1
      simp [unitArmValue, h1, hk]
  · simp only [List.get_eq_getElem] at h1
    simp [unitArmValue, h1]
#print axioms Paper7Exceptional.unitArmValue_split

theorem unitArmValue_sum (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ) (k : Fin b) :
    (∑ j : Fin (pq b p q k).length, unitArmValue b p q Y hY r a k j) =
      (p k : ℝ) * r k + if hk : k ∈ Y then a ⟨k, hk⟩ else 0 := by
  classical
  simp_rw [unitArmValue_split]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ j : Fin (pq b p q k).length,
      if (pq b p q k).get j = 1 then r k else 0) = (p k : ℝ) * r k := by
    have h21 : (2 : ℕ) ≠ 1 := by decide
    simpa only [ite_true, ite_eq_right h21, mul_zero, add_zero] using
      pq_sum_lengths_apply b p q k (fun t => if t = 1 then r k else 0)
  rw [h1]
  by_cases hk : k ∈ Y <;> simp [hk]
#print axioms Paper7Exceptional.unitArmValue_sum

theorem pathShift_one_constant (t : ℕ) (ht : t = 1 ∨ t = 2) (c : ℝ) (i : Fin t) :
    (pathShift 1 t *ᵥ (fun _ => c)) i = if t = 1 then c else 0 := by
  rcases ht with rfl | rfl
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    norm_num [pathShift, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · fin_cases i <;>
      norm_num [pathShift, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
#print axioms Paper7Exceptional.pathShift_one_constant

theorem unitArm_pendant_mulVec (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) (i : Fin ((pq b p q k).get j)) :
    (pendantShift b (pq b p q) (1 : ℝ) *ᵥ unitArmVector b p q Y hY r a) ⟨k, j, i⟩ =
      if (pq b p q k).get j = 1 then r k else 0 := by
  unfold pendantShift
  rw [blockDiagonal_mulVec, blockDiagonal_mulVec]
  change (pathShift 1 ((pq b p q k).get j) *ᵥ
    (fun _ => unitArmValue b p q Y hY r a k j)) i = _
  rw [pathShift_one_constant _ (pq_length_one_or_two b p q k j)]
  by_cases h1 : (pq b p q k).get j = 1
  · simp only [List.get_eq_getElem] at h1
    simp [unitArmValue, h1]
  · simp only [List.get_eq_getElem] at h1
    simp [h1]
#print axioms Paper7Exceptional.unitArm_pendant_mulVec


theorem sum_subtype_extend_real {ι : Type*} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (u : {i // P i} → ℝ) :
    (∑ i, if h : P i then u ⟨i, h⟩ else 0) = ∑ i, u i := by
  classical
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    have hn : ¬ P i := by
      intro hp
      exact hi ⟨⟨i, hp⟩, rfl⟩
    simp [hn]
  · intro i
    simp [i.property]
#print axioms Paper7Exceptional.sum_subtype_extend_real

theorem attachment_mulVec_real (b : ℕ) (p q : Fin b → ℕ)
    (z : ArmV b (pq b p q) → ℝ) (k : Fin b) :
    (attachment b (pq b p q) *ᵥ z) k =
      -(∑ j : Fin (pq b p q k).length, z ⟨k, j, armFirst b p q k j⟩) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single k, ← Finset.sum_neg_distrib]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.sum_eq_single (armFirst b p q k j)]
    · simp [attachment, armFirst]
    · intro i hi
      have hn : i.val ≠ 0 := by
        intro h
        apply hi
        exact Fin.ext h
      simp [attachment, hn]
  · intro l hl
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    simp [attachment, hl]
#print axioms Paper7Exceptional.attachment_mulVec_real

theorem unitArm_attachment_dot (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ) :
    r ⬝ᵥ (attachment b (pq b p q) *ᵥ unitArmVector b p q Y hY r a) =
      -((∑ k, (p k : ℝ) * r k ^ 2) + ∑ k : Y, r k.1 * a k) := by
  classical
  calc
    _ = -(∑ k, ((p k : ℝ) * r k ^ 2 +
        if hk : k ∈ Y then r k * a ⟨k, hk⟩ else 0)) := by
      rw [dotProduct, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [attachment_mulVec_real]
      change r k * -(∑ j, unitArmValue b p q Y hY r a k j) = _
      rw [unitArmValue_sum]
      by_cases hk : k ∈ Y <;> simp [hk] <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_subtype_extend_real (fun k : Fin b => k ∈ Y)
        (fun k => r k.1 * a k)]
      rw [Subsingleton.elim (Subtype.fintype (fun k : Fin b => k ∈ Y))
        (Finset.Subtype.fintype Y)]
#print axioms Paper7Exceptional.unitArm_attachment_dot

theorem unitArm_pendant_quadratic (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (r : Fin b → ℝ) (a : Y → ℝ) :
    (unitArmVector b p q Y hY r a) ⬝ᵥ
      (pendantShift b (pq b p q) (1 : ℝ) *ᵥ unitArmVector b p q Y hY r a) =
      ∑ k, (p k : ℝ) * r k ^ 2 := by
  classical
  simp only [dotProduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ j : Fin (pq b p q k).length,
        if (pq b p q k).get j = 1 then r k ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [unitArm_pendant_mulVec]
      by_cases h1 : (pq b p q k).get j = 1
      · simp only [List.get_eq_getElem] at h1
        simp [unitArmVector, unitArmValue, h1, pow_two]
      · simp only [List.get_eq_getElem] at h1
        simp [h1]
    _ = (p k : ℝ) * r k ^ 2 := by
      have h21 : (2 : ℕ) ≠ 1 := by decide
      simpa only [ite_true, ite_eq_right h21, mul_zero, add_zero] using
        pq_sum_lengths_apply b p q k (fun t => if t = 1 then r k ^ 2 else 0)
#print axioms Paper7Exceptional.unitArm_pendant_quadratic

def unitCoreMatrix (b : ℕ) (p : Fin b → ℕ) : Matrix (Fin b) (Fin b) ℝ :=
  Cyc b + Matrix.diagonal (fun k => (p k : ℝ) - 1)
#print axioms Paper7Exceptional.unitCoreMatrix

/-- Complete simultaneous arm identity on the original graph: one independent
selected P2 amplitude for every k in Y, all remaining P2 arms zero. -/
theorem unitLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Kq b q ∩ Xset b)
    (r : Fin b → ℝ) (a : Y → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) 1).toQuadraticForm'
        (unitLift b p q Y hY (r, a)) =
      (unitCoreMatrix b p).toQuadraticForm' r + 2 * ∑ k : Y, r k.1 * a k := by
  classical
  let u := unitArmVector b p q Y hY r a
  have hm : (SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) 1 =
      -((1 : ℝ) • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℝ) -
        (SG b p q).adjMatrix ℝ) := by simp
  have hc : r ⬝ᵥ (cycleShift b (1 : ℝ) *ᵥ r) = r ⬝ᵥ r - r ⬝ᵥ (Cyc b *ᵥ r) := by
    simp only [cycleShift, Cyc, one_smul, Matrix.sub_mulVec,
      Matrix.one_mulVec, dotProduct_sub]
  have hd : r ⬝ᵥ (Matrix.diagonal (fun k => (p k : ℝ) - 1) *ᵥ r) =
      (∑ k, (p k : ℝ) * r k ^ 2) - r ⬝ᵥ r := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hm]
  simp only [quadratic_apply, Matrix.neg_mulVec, dotProduct_neg]
  rw [sun_shift_fromBlocks b (pq b p q) hb 1]
  change -(Sum.elim r u ⬝ᵥ
      (Matrix.fromBlocks (cycleShift b (1 : ℝ)) (attachment b (pq b p q))
        (attachment b (pq b p q)).transpose (pendantShift b (pq b p q) (1 : ℝ)) *ᵥ
          Sum.elim r u)) = _
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim, dotProduct_add,
    dotProduct_add, Matrix.dotProduct_transpose_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hc, unitArm_attachment_dot b p q Y hY r a,
    unitArm_pendant_quadratic b p q Y hY r a]
  simp only [unitCoreMatrix, Matrix.add_mulVec, dotProduct_add]
  rw [hd]
  ring
#print axioms Paper7Exceptional.unitLift_quadratic

end Paper7Exceptional
