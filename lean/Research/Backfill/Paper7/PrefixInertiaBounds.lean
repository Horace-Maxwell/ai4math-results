import Research.Backfill.Paper7.EncodedThresholdCounts
import Research.Backfill.Paper7.Lemma51

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The literal legacy path matrices are identified with the exact Lemma51 matrices.
EncodedThresholdCounts passed development in dev224; this new repair is uncompiled.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy Paper7PruningSpectrum

def pathIndexEquivX (b : ℕ) : PathIndex b ≃ Xset b where
  toFun i := ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    have hi := i.property
    omega⟩⟩
  invFun i := ⟨i.val, by
    have hi := (Finset.mem_filter.mp i.property).2
    omega⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl
#print axioms Paper7PruningGuards.pathIndexEquivX

def rIndexEquivX (b d : ℕ) (x : PQ b) :
    RIndex b d x ≃ ↥(Xset b \ Kq b («prefix» d x).2) where
  toFun i := ⟨i.val, by
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have hi := i.property.1
        omega⟩
    · intro hi
      have hp := (Finset.mem_filter.mp hi).2
      have hz := i.property.2
      omega⟩
  invFun i := ⟨i.val, by
    have hi := Finset.mem_sdiff.mp i.property
    constructor
    · have hx := (Finset.mem_filter.mp hi.1).2
      omega
    · by_contra hn
      exact hi.2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hn⟩)⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl
#print axioms Paper7PruningGuards.rIndexEquivX

theorem pathMatrix_reindex (b d : ℕ) (x : PQ b) (m : ℝ) :
    Matrix.reindex (pathIndexEquivX b) (pathIndexEquivX b) (pathMatrix b d x m) =
      tridiag (Xset b) (fun k => fk b («prefix» d x).1 («prefix» d x).2 m k - m) := by
  classical
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [Matrix.reindex_apply, pathMatrix, tridiag, pathIndexEquivX]
  · have he : (pathIndexEquivX b).symm i ≠ (pathIndexEquivX b).symm j :=
      (pathIndexEquivX b).symm.injective.ne h
    change pathMatrix b d x m ((pathIndexEquivX b).symm i) ((pathIndexEquivX b).symm j) = _
    rw [pathMatrix, ite_eq_right he, tridiag, ite_eq_right h]
    rfl
#print axioms Paper7PruningGuards.pathMatrix_reindex

theorem rPathMatrix_reindex (b d : ℕ) (x : PQ b) :
    Matrix.reindex (rIndexEquivX b d x) (rIndexEquivX b d x) (rPathMatrix b d x) =
      tridiag (Xset b \ Kq b («prefix» d x).2) (fun k => ((«prefix» d x).1 k : ℝ) - 1) := by
  classical
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [Matrix.reindex_apply, rPathMatrix, tridiag, rIndexEquivX]
  · have he : (rIndexEquivX b d x).symm i ≠ (rIndexEquivX b d x).symm j :=
      (rIndexEquivX b d x).symm.injective.ne h
    change rPathMatrix b d x ((rIndexEquivX b d x).symm i) ((rIndexEquivX b d x).symm j) = _
    rw [rPathMatrix, ite_eq_right he, tridiag, ite_eq_right h]
    rfl
#print axioms Paper7PruningGuards.rPathMatrix_reindex

theorem pathMatrix_inertia_eq (b d : ℕ) (x : PQ b) (m : ℝ) :
    nPos (pathMatrix b d x m) =
        nPos (tridiag (Xset b) (fun k => fk b («prefix» d x).1 («prefix» d x).2 m k - m)) ∧
      nZero (pathMatrix b d x m) =
        nZero (tridiag (Xset b) (fun k => fk b («prefix» d x).1 («prefix» d x).2 m k - m)) := by
  have hc := Matrix.charpoly_reindex (pathIndexEquivX b) (pathMatrix b d x m)
  rw [pathMatrix_reindex] at hc
  constructor
  · unfold nPos eigs
    rw [hc]
  · unfold nZero eigs
    rw [hc]
#print axioms Paper7PruningGuards.pathMatrix_inertia_eq

theorem rPathMatrix_inertia_eq (b d : ℕ) (x : PQ b) :
    nPos (rPathMatrix b d x) =
      nPos (tridiag (Xset b \ Kq b («prefix» d x).2)
        (fun k => ((«prefix» d x).1 k : ℝ) - 1)) := by
  have hc := Matrix.charpoly_reindex (rIndexEquivX b d x) (rPathMatrix b d x)
  rw [rPathMatrix_reindex] at hc
  unfold nPos eigs
  rw [hc]
#print axioms Paper7PruningGuards.rPathMatrix_inertia_eq

theorem prefix_coordinate_le (b d : ℕ) (x : PQ b) :
    ∀ i, («prefix» d x).1 i ≤ x.1 i ∧ («prefix» d x).2 i ≤ x.2 i := by
  intro i
  by_cases hi : i.val < d <;> simp [«prefix», hi]
#print axioms Paper7PruningGuards.prefix_coordinate_le

theorem prefix_fk_le (b d : ℕ) (x : PQ b) (m : ℝ) (hm : 2 ≤ m) (i : Fin b) :
    fk b («prefix» d x).1 («prefix» d x).2 m i ≤ fk b x.1 x.2 m i := by
  have hp : ((«prefix» d x).1 i : ℝ) ≤ x.1 i := by
    exact_mod_cast (prefix_coordinate_le b d x i).1
  have hq : ((«prefix» d x).2 i : ℝ) ≤ x.2 i := by
    exact_mod_cast (prefix_coordinate_le b d x i).2
  have hm0 : 0 ≤ m := by linarith
  have hd : 0 ≤ m ^ 2 - 1 := by nlinarith
  unfold fk
  exact add_le_add (div_le_div_of_nonneg_right hp hm0)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq hm0) hd)
#print axioms Paper7PruningGuards.prefix_fk_le

theorem prefix_Kq_subset_full_X (b d : ℕ) (x : PQ b) (hd : d < b) :
    Kq b («prefix» d x).2 ⊆ Kq b x.2 ∩ Xset b := by
  intro i hi
  have hq : 0 < («prefix» d x).2 i := (Finset.mem_filter.mp hi).2
  have hid : i.val < d := by
    by_contra hn
    simp only [«prefix», ite_eq_right hn] at hq
    omega
  apply Finset.mem_inter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hq.trans_le (prefix_coordinate_le b d x i).2⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
#print axioms Paper7PruningGuards.prefix_Kq_subset_full_X

theorem prefix_ordinary_bounds (b d : ℕ) (x : PQ b) (hb : 3 ≤ b)
    (m : ℕ) (hm : 2 ≤ m) :
    nPos (pathMatrix b d x m) ≤ Ngt (SG b x.1 x.2) m ∧
      nPos (pathMatrix b d x m) ≤ Nlt (SG b x.1 x.2) (-(m : ℝ)) ∧
      nPos (pathMatrix b d x m) + nZero (pathMatrix b d x m) ≤ Nge (SG b x.1 x.2) m ∧
      nPos (pathMatrix b d x m) + nZero (pathMatrix b d x m) ≤
        Nle (SG b x.1 x.2) (-(m : ℝ)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h := (Paper7Comparison.check_Lemma51 b x.1 x.2 hb).1 (m : ℝ)
    (fun k => fk b («prefix» d x).1 («prefix» d x).2 m k - m) hmR
    (fun k _ => sub_le_sub_right (prefix_fk_le b d x m hmR k) _)
  have he := pathMatrix_inertia_eq b d x m
  rw [← he.1, ← he.2] at h
  exact h
#print axioms Paper7PruningGuards.prefix_ordinary_bounds

theorem prefix_unit_bounds (b d : ℕ) (x : PQ b) (hb : 3 ≤ b) (hd : d < b) :
    lowerGT b d x 1 ≤ Ngt (SG b x.1 x.2) 1 ∧
      lowerGT b d x 1 ≤ Nlt (SG b x.1 x.2) (-1) := by
  have h := (Paper7Comparison.check_Lemma51 b x.1 x.2 hb).2
    (Kq b («prefix» d x).2) (fun k => ((«prefix» d x).1 k : ℝ) - 1)
    (prefix_Kq_subset_full_X b d x hd) (fun k _ => by
      have hp : ((«prefix» d x).1 k : ℝ) ≤ x.1 k := by
        exact_mod_cast (prefix_coordinate_le b d x k).1
      linarith)
  rw [← rPathMatrix_inertia_eq b d x] at h
  simpa only [lowerGT, ite_true] using h
#print axioms Paper7PruningGuards.prefix_unit_bounds

theorem prefix_threshold_bounds (b d : ℕ) (x : PQ b) (hb : 3 ≤ b) (hd : d < b)
    (m : ℕ) (hm : 1 ≤ m) :
    lowerGT b d x m ≤ Ngt (SG b x.1 x.2) m ∧
      lowerGT b d x m ≤ Nlt (SG b x.1 x.2) (-(m : ℝ)) ∧
      lowerGE b d x m ≤ Nge (SG b x.1 x.2) m ∧
      lowerGE b d x m ≤ Nle (SG b x.1 x.2) (-(m : ℝ)) := by
  by_cases hm1 : m = 1
  · subst m
    have h := prefix_unit_bounds b d x hb hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_one] using h.1
    · simpa only [Nat.cast_one] using h.2
    · simp [lowerGE]
    · simp [lowerGE]
  · have hm2 : 2 ≤ m := by omega
    have hm0 : ¬ m < 2 := by omega
    simpa only [lowerGT, ite_eq_right hm1, lowerGE, ite_eq_right hm0] using
      prefix_ordinary_bounds b d x hb m hm2
#print axioms Paper7PruningGuards.prefix_threshold_bounds

theorem prefix_feature_bounds (b N d : ℕ) (x : PQ b) (hb : 3 ≤ b) (hd : d < b)
    (hN : N ≤ 49) (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    ∀ m : ℕ, 1 ≤ m → m ≤ 9 →
      lowerGT b d x m ≤ specGT b (actualCounts b x hb) m ∧
        lowerGE b d x m ≤ specGE b (actualCounts b x hb) m := by
  intro m hm _hm9
  have h := prefix_threshold_bounds b d x hb hd m hm
  constructor
  · rw [actualCounts_specGT b N x hb hN hx hG m hm]
    by_cases he : Even b
    · rw [ite_eq_left he]
      exact h.1
    · rw [ite_eq_right he]
      exact le_min h.1 h.2.1
  · by_cases hm2 : 2 ≤ m
    · rw [actualCounts_specGE b N x hb hN hx hG m hm2]
      by_cases he : Even b
      · rw [ite_eq_left he]
        exact h.2.2.1
      · rw [ite_eq_right he]
        exact le_min h.2.2.1 h.2.2.2
    · have hm0 : m < 2 := by omega
      simp only [lowerGE, specGE, ite_eq_left hm0, le_refl]
#print axioms Paper7PruningGuards.prefix_feature_bounds

end Paper7PruningGuards
