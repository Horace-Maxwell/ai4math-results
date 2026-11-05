import Research.Backfill.Paper7.ExceptionalArmLift

/-! Full-support exceptional lifts in the original SunV coordinates.
The sign changes are confined to pendant paths, never to the cycle. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma21
open BackfillPaper7.Challenge Paper7Cleared Paper7Reduced Paper7Inertia
open Paper7Exceptional

abbrev QSupport (b : ℕ) (q : Fin b → ℕ) := ↥(Kq b q)
#print axioms Paper7Lemma21.QSupport

def fullSelectedArm (b : ℕ) (p q : Fin b → ℕ) (k : QSupport b q) :
    PQArmIndex b p q 2 k.1 :=
  chosenTwoArm b p q k.1 (Finset.mem_filter.mp k.2).2
#print axioms Paper7Lemma21.fullSelectedArm

def signedEndpoint (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) : ℝ :=
  if (pq b p q k).get j = 1 then ε * r k
  else if hk : k ∈ Kq b q then
    if j = (fullSelectedArm b p q ⟨k, hk⟩).1 then a ⟨k, hk⟩ else 0
  else 0
#print axioms Paper7Lemma21.signedEndpoint

def signedPath (ε c : ℝ) (t : ℕ) : Fin t → ℝ :=
  fun i => if i.val = 0 then c else ε * c
#print axioms Paper7Lemma21.signedPath

def signedArms (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ) : ArmV b (pq b p q) → ℝ :=
  fun v => signedPath ε (signedEndpoint b p q ε r a v.1 v.2.1)
    ((pq b p q v.1).get v.2.1) v.2.2
#print axioms Paper7Lemma21.signedArms

def signedLift (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    ((Fin b → ℝ) × (QSupport b q → ℝ)) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) where
  toFun z := Sum.elim z.1 (signedArms b p q ε z.1 z.2)
  map_add' z w := by
    funext v
    rcases v with k | ⟨k, j, i⟩
    · rfl
    · change signedArms b p q ε (z.1 + w.1) (z.2 + w.2) ⟨k,j,i⟩ =
        signedArms b p q ε z.1 z.2 ⟨k,j,i⟩ + signedArms b p q ε w.1 w.2 ⟨k,j,i⟩
      simp only [signedArms, signedPath, signedEndpoint]
      split_ifs <;> simp [mul_add]
  map_smul' c z := by
    funext v
    rcases v with k | ⟨k, j, i⟩
    · rfl
    · change signedArms b p q ε (c • z.1) (c • z.2) ⟨k,j,i⟩ =
        c * signedArms b p q ε z.1 z.2 ⟨k,j,i⟩
      simp only [signedArms, signedPath, signedEndpoint]
      split_ifs <;> simp [mul_left_comm]
#print axioms Paper7Lemma21.signedLift

theorem signedLift_root (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ) (k : Fin b) :
    signedLift b p q ε (r,a) (Sum.inl k) = r k := rfl
#print axioms Paper7Lemma21.signedLift_root

theorem signedEndpoint_split (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) :
    signedEndpoint b p q ε r a k j =
      (if (pq b p q k).get j = 1 then ε * r k else 0) +
      (if hk : k ∈ Kq b q then
        if j = (fullSelectedArm b p q ⟨k,hk⟩).1 then a ⟨k,hk⟩ else 0 else 0) := by
  classical
  by_cases h1 : (pq b p q k).get j = 1
  · by_cases hk : k ∈ Kq b q
    · have hn : j ≠ (fullSelectedArm b p q ⟨k,hk⟩).1 := by
        intro h
        have ht := (fullSelectedArm b p q ⟨k,hk⟩).2
        rw [← h, h1] at ht
        norm_num at ht
      simp only [List.get_eq_getElem] at h1
      simp [signedEndpoint, h1, hk, hn]
    · simp only [List.get_eq_getElem] at h1
      simp [signedEndpoint, h1, hk]
  · simp only [List.get_eq_getElem] at h1
    simp [signedEndpoint, h1]
#print axioms Paper7Lemma21.signedEndpoint_split

theorem signedEndpoint_sum (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ) (k : Fin b) :
    (∑ j : Fin (pq b p q k).length, signedEndpoint b p q ε r a k j) =
      (p k : ℝ) * (ε * r k) + if hk : k ∈ Kq b q then a ⟨k,hk⟩ else 0 := by
  classical
  simp_rw [signedEndpoint_split]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ j : Fin (pq b p q k).length,
      if (pq b p q k).get j = 1 then ε * r k else 0) = (p k : ℝ) * (ε * r k) := by
    have h21 : (2 : ℕ) ≠ 1 := by decide
    simpa only [ite_true, ite_eq_right h21, mul_zero, add_zero] using
      pq_sum_lengths_apply b p q k (fun t => if t = 1 then ε * r k else 0)
  rw [h1]
  by_cases hk : k ∈ Kq b q <;> simp [hk]
#print axioms Paper7Lemma21.signedEndpoint_sum

theorem pathShift_signed (ε c : ℝ) (hε : ε ^ 2 = 1)
    (t : ℕ) (ht : t = 1 ∨ t = 2) (i : Fin t) :
    (pathShift ε t *ᵥ signedPath ε c t) i = if t = 1 then ε * c else 0 := by
  rcases ht with rfl | rfl
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [pathShift, signedPath, Matrix.mulVec, dotProduct]
  · fin_cases i <;>
      simp [pathShift, signedPath, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [congrArg (fun z : ℝ => z * c) hε]
#print axioms Paper7Lemma21.pathShift_signed

theorem signedArms_pendant_entry (b : ℕ) (p q : Fin b → ℕ)
    (ε : ℝ) (hε : ε ^ 2 = 1) (r : Fin b → ℝ) (a : QSupport b q → ℝ)
    (k : Fin b) (j : Fin (pq b p q k).length) (i : Fin ((pq b p q k).get j)) :
    (pendantShift b (pq b p q) ε *ᵥ signedArms b p q ε r a) ⟨k,j,i⟩ =
      if (pq b p q k).get j = 1 then r k else 0 := by
  unfold pendantShift
  rw [blockDiagonal_mulVec, blockDiagonal_mulVec]
  change (pathShift ε ((pq b p q k).get j) *ᵥ
      signedPath ε (signedEndpoint b p q ε r a k j) _) i = _
  rw [pathShift_signed ε _ hε _ (pq_length_one_or_two b p q k j)]
  by_cases h1 : (pq b p q k).get j = 1
  · simp only [h1, ite_true, signedEndpoint]
    nlinarith [congrArg (fun z : ℝ => z * r k) hε]
  · simp only [List.get_eq_getElem] at h1
    simp [h1]
#print axioms Paper7Lemma21.signedArms_pendant_entry

theorem signedArms_attachment_dot (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (r : Fin b → ℝ) (a : QSupport b q → ℝ) :
    r ⬝ᵥ (attachment b (pq b p q) *ᵥ signedArms b p q ε r a) =
      -(ε * (∑ k, (p k : ℝ) * r k ^ 2) + ∑ k : QSupport b q, r k.1 * a k) := by
  classical
  calc
    _ = -(∑ k, (ε * ((p k : ℝ) * r k ^ 2) +
        if hk : k ∈ Kq b q then r k * a ⟨k,hk⟩ else 0)) := by
      rw [dotProduct, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [attachment_mulVec_real]
      simp only [signedArms, signedPath, armFirst, ite_true]
      rw [signedEndpoint_sum]
      by_cases hk : k ∈ Kq b q <;> simp [hk] <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_subtype_extend_real (fun k : Fin b => k ∈ Kq b q)
          (fun k => r k.1 * a k)]
      rw [Subsingleton.elim (Subtype.fintype (fun k : Fin b => k ∈ Kq b q))
        (Finset.Subtype.fintype (Kq b q))]
#print axioms Paper7Lemma21.signedArms_attachment_dot

theorem signedArms_pendant_quadratic (b : ℕ) (p q : Fin b → ℕ)
    (ε : ℝ) (hε : ε ^ 2 = 1) (r : Fin b → ℝ) (a : QSupport b q → ℝ) :
    signedArms b p q ε r a ⬝ᵥ
      (pendantShift b (pq b p q) ε *ᵥ signedArms b p q ε r a) =
      ε * ∑ k, (p k : ℝ) * r k ^ 2 := by
  classical
  simp only [dotProduct, Fintype.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ j : Fin (pq b p q k).length,
        if (pq b p q k).get j = 1 then ε * r k ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [signedArms_pendant_entry b p q ε hε]
      by_cases h1 : (pq b p q k).get j = 1
      · have hi (i : Fin ((pq b p q k).get j)) : i.val = 0 := by
          have := i.isLt
          omega
        simp only [List.get_eq_getElem] at h1
        simp [signedArms, signedPath, signedEndpoint, h1, hi, pow_two, mul_assoc]
      · simp only [List.get_eq_getElem] at h1
        simp [h1]
    _ = ε * ((p k : ℝ) * r k ^ 2) := by
      have hh := pq_sum_lengths_apply b p q k
        (fun t => if t = 1 then ε * r k ^ 2 else 0)
      have h21 : (2 : ℕ) ≠ 1 := by decide
      simpa only [ite_true, ite_eq_right h21, mul_zero, add_zero, mul_left_comm, mul_assoc] using hh
#print axioms Paper7Lemma21.signedArms_pendant_quadratic

def signedCore (b : ℕ) (p : Fin b → ℕ) (ε : ℝ) : Matrix (Fin b) (Fin b) ℝ :=
  Cyc b + Matrix.diagonal (fun k => ε * ((p k : ℝ) - 1))
#print axioms Paper7Lemma21.signedCore

theorem signedCore_isHermitian (b : ℕ) (p : Fin b → ℕ) (ε : ℝ) :
    (signedCore b p ε).IsHermitian :=
  ((SimpleGraph.cycleGraph b).isHermitian_adjMatrix ℝ).add (Matrix.isHermitian_diagonal _)
#print axioms Paper7Lemma21.signedCore_isHermitian

theorem signedLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hε : ε ^ 2 = 1) (r : Fin b → ℝ) (a : QSupport b q → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) ε).toQuadraticForm'
        (signedLift b p q ε (r,a)) =
      (signedCore b p ε).toQuadraticForm' r + 2 * ∑ k : QSupport b q, r k.1 * a k := by
  classical
  let u := signedArms b p q ε r a
  have hm : (SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) ε =
      -(ε • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℝ) -
        (SG b p q).adjMatrix ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    abel
  have hc : r ⬝ᵥ (cycleShift b ε *ᵥ r) = ε * (r ⬝ᵥ r) - r ⬝ᵥ (Cyc b *ᵥ r) := by
    simp only [cycleShift, Cyc, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hd : r ⬝ᵥ (Matrix.diagonal (fun k => ε * ((p k : ℝ) - 1)) *ᵥ r) =
      ε * (∑ k, (p k : ℝ) * r k ^ 2) - ε * (r ⬝ᵥ r) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hm]
  simp only [quadratic_apply, Matrix.neg_mulVec, dotProduct_neg]
  rw [sun_shift_fromBlocks b (pq b p q) hb ε]
  change -(Sum.elim r u ⬝ᵥ
      (Matrix.fromBlocks (cycleShift b ε) (attachment b (pq b p q))
        (attachment b (pq b p q)).transpose (pendantShift b (pq b p q) ε)) *ᵥ
          Sum.elim r u) = _
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim, dotProduct_add,
    dotProduct_add, Matrix.dotProduct_transpose_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hc, signedArms_attachment_dot b p q ε r a,
    signedArms_pendant_quadratic b p q ε hε r a]
  simp only [signedCore, Matrix.add_mulVec, dotProduct_add]
  rw [hd]
  ring
#print axioms Paper7Lemma21.signedLift_quadratic

end Paper7Lemma21
