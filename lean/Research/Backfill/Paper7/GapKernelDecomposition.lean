import Research.Backfill.Paper7.GapPartition

/-! Actual restriction/zero-extension maps and both inverse identities for the
frozen gap images. Partition is proved in GapPartition, never assumed here. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge

def gapRestriction (b : ℕ) (q : Fin b → ℕ) (k : Fin b) :
    (Fin b → ℝ) →ₗ[ℝ] ({j : Fin b // inGap b (Kq b q) k j} → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun j => j.val)
#print axioms Paper7Lemma22Gaps.gapRestriction

def gapImage (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) (k : Fin b) :
    Submodule ℝ ({j : Fin b // inGap b (Kq b q) k j} → ℝ) :=
  (LinearMap.ker (Matrix.toLin' (Wmat b p q ε))).map (gapRestriction b q k)
#print axioms Paper7Lemma22Gaps.gapImage

def gapExtend (b : ℕ) (q : Fin b → ℕ) (k : Fin b) :
    ({j : Fin b // inGap b (Kq b q) k j} → ℝ) →ₗ[ℝ] (Fin b → ℝ) := by
  classical
  exact {
    toFun := fun v j => if h : inGap b (Kq b q) k j then v ⟨j, h⟩ else 0
    map_add' := by
      intro v w
      funext j
      by_cases h : inGap b (Kq b q) k j <;> simp [h]
    map_smul' := by
      intro a v
      funext j
      by_cases h : inGap b (Kq b q) k j <;> simp [h] }
#print axioms Paper7Lemma22Gaps.gapExtend

theorem gapExtend_apply_mem (b : ℕ) (q : Fin b → ℕ) (k j : Fin b)
    (v : {j : Fin b // inGap b (Kq b q) k j} → ℝ)
    (h : inGap b (Kq b q) k j) : gapExtend b q k v j = v ⟨j, h⟩ := by
  simp [gapExtend, h]
#print axioms Paper7Lemma22Gaps.gapExtend_apply_mem

theorem gapExtend_apply_not_mem (b : ℕ) (q : Fin b → ℕ) (k j : Fin b)
    (v : {j : Fin b // inGap b (Kq b q) k j} → ℝ)
    (h : ¬ inGap b (Kq b q) k j) : gapExtend b q k v j = 0 := by
  simp [gapExtend, h]
#print axioms Paper7Lemma22Gaps.gapExtend_apply_not_mem

/-- Restrict a genuine solution to one gap and set every other coordinate to
zero. The result still satisfies every original Wmat row. -/
theorem gap_project_mem_kernel (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (k : Fin b) (hk : k ∈ Kq b q) (y : Fin b → ℝ)
    (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε))) :
    gapExtend b q k (gapRestriction b q k y) ∈
      LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) := by
  classical
  let z := gapExtend b q k (gapRestriction b q k y)
  have hzero (i : Fin b) (hi : ¬ inGap b (Kq b q) k i) : z i = 0 :=
    gapExtend_apply_not_mem b q k i _ hi
  have heq (i : Fin b) (hi : inGap b (Kq b q) k i ∨ i ∈ Kq b q) : z i = y i := by
    rcases hi with hg | hK
    · exact gapExtend_apply_mem b q k i _ hg
    · have hg : ¬ inGap b (Kq b q) k i := fun h => (inGap_not_mem b _ k i h) hK
      rw [hzero i hg, kernel_zero_on_support b p q ε y hy i hK]
  apply (mem_ker_Wmat_iff b p q ε z).mpr
  intro j
  by_cases hq : 0 < q j
  · rw [ite_eq_left hq]
    have hj : j ∈ Kq b q := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hq⟩
    exact hzero j (fun h => (inGap_not_mem b _ k j h) hj)
  · rw [ite_eq_right hq]
    have hj : j ∉ Kq b q := by
      simpa only [Kq, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    by_cases hg : inGap b (Kq b q) k j
    · have hp : inGap b (Kq b q) k (prv b j) ∨ prv b j ∈ Kq b q := by
        by_cases h : prv b j ∈ Kq b q
        · exact Or.inr h
        · exact Or.inl (inGap_prev b (Kq b q) k j hk hg h)
      have hn : inGap b (Kq b q) k (nxt b j) ∨ nxt b j ∈ Kq b q := by
        by_cases h : nxt b j ∈ Kq b q
        · exact Or.inr h
        · exact Or.inl (inGap_next b (Kq b q) k j hk hg h)
      rw [heq _ hp, heq _ hn, heq _ (Or.inl hg)]
      exact kernel_recurrence_off_support b p q ε y hy j hj
    · have hp : ¬ inGap b (Kq b q) k (prv b j) := by
        intro h
        have h' := inGap_next b (Kq b q) k (prv b j) hk h
          (by simpa only [nxt, prv, Equiv.apply_symm_apply] using hj)
        exact hg (by simpa only [nxt, prv, Equiv.apply_symm_apply] using h')
      have hn : ¬ inGap b (Kq b q) k (nxt b j) := by
        intro h
        have h' := inGap_prev b (Kq b q) k (nxt b j) hk h
          (by simpa only [nxt, prv, Equiv.symm_apply_apply] using hj)
        exact hg (by simpa only [nxt, prv, Equiv.symm_apply_apply] using h')
      rw [hzero _ hp, hzero _ hn, hzero _ hg]
      simp
#print axioms Paper7Lemma22Gaps.gap_project_mem_kernel

def extendGapImage (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (k : Fin b) (hk : k ∈ Kq b q) :
    gapImage b p q ε k →ₗ[ℝ] LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) where
  toFun v := ⟨gapExtend b q k v.1, by
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp v.property
    rw [← he]
    exact gap_project_mem_kernel b p q ε k hk y hy⟩
  map_add' v w := by
    apply Subtype.ext
    exact (gapExtend b q k).map_add v.1 w.1
  map_smul' a v := by
    apply Subtype.ext
    exact (gapExtend b q k).map_smul a v.1
#print axioms Paper7Lemma22Gaps.extendGapImage

def restrictAllGaps (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) →ₗ[ℝ]
      (∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) :=
  LinearMap.pi fun k => (gapRestriction b q k.1).submoduleMap _
#print axioms Paper7Lemma22Gaps.restrictAllGaps

def glueAllGaps (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    (∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) →ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) := by
  classical
  exact ∑ k : {k : Fin b // k ∈ Kq b q},
    (extendGapImage b p q ε k.1 k.2).comp (LinearMap.proj k)
#print axioms Paper7Lemma22Gaps.glueAllGaps

theorem glueAllGaps_apply (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : ∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) (j : Fin b) :
    (glueAllGaps b p q ε v).1 j =
      ∑ k : {k : Fin b // k ∈ Kq b q}, gapExtend b q k.1 (v k).1 j := by
  classical
  simp only [glueAllGaps, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply, extendGapImage]
  rfl
#print axioms Paper7Lemma22Gaps.glueAllGaps_apply

theorem restrictAllGaps_injective (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) : Function.Injective (restrictAllGaps b p q ε) := by
  intro y z he
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ Kq b q
  · rw [kernel_zero_on_support b p q ε y.1 y.2 j hj,
      kernel_zero_on_support b p q ε z.1 z.2 j hj]
  · obtain ⟨k, hk, hgap⟩ := exists_gap_start b (Kq b q) hK j hj
    have h := congrFun (congrArg Subtype.val (congrFun he ⟨k, hk⟩)) ⟨j, hgap⟩
    exact h
#print axioms Paper7Lemma22Gaps.restrictAllGaps_injective

theorem restrict_glueAllGaps (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (v : ∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) :
    restrictAllGaps b p q ε (glueAllGaps b p q ε v) = v := by
  classical
  funext k
  apply Subtype.ext
  funext j
  change (glueAllGaps b p q ε v).1 j.1 = (v k).1 j
  rw [glueAllGaps_apply]
  calc
    _ = gapExtend b q k.1 (v k).1 j.1 := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        apply gapExtend_apply_not_mem
        intro hg
        exact hl (Subtype.ext (inGap_unique_start b (Kq b q) l.1 k.1 j.1
          l.2 k.2 hg j.2))
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    _ = (v k).1 j := gapExtend_apply_mem b q k.1 j.1 (v k).1 j.2
#print axioms Paper7Lemma22Gaps.restrict_glueAllGaps

theorem glue_restrictAllGaps (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) (y : LinearMap.ker (Matrix.toLin' (Wmat b p q ε))) :
    glueAllGaps b p q ε (restrictAllGaps b p q ε y) = y := by
  apply restrictAllGaps_injective b p q ε hK
  exact restrict_glueAllGaps b p q ε (restrictAllGaps b p q ε y)
#print axioms Paper7Lemma22Gaps.glue_restrictAllGaps

def gapKernelEquiv (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) :
    LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) ≃ₗ[ℝ]
      (∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) where
  toFun := restrictAllGaps b p q ε
  invFun := glueAllGaps b p q ε
  left_inv := glue_restrictAllGaps b p q ε hK
  right_inv := restrict_glueAllGaps b p q ε
  map_add' := (restrictAllGaps b p q ε).map_add
  map_smul' := (restrictAllGaps b p q ε).map_smul
#print axioms Paper7Lemma22Gaps.gapKernelEquiv

/-- Exact sum of the original restriction-image dimensions, for all real ε. -/
theorem deltaE_eq_sum_gapDim (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) :
    deltaE b p q ε = ∑ k ∈ Kq b q, gapDim b p q ε k := by
  classical
  calc
    deltaE b p q ε = Module.finrank ℝ
        (∀ k : {k : Fin b // k ∈ Kq b q}, gapImage b p q ε k.1) :=
      (gapKernelEquiv b p q ε hK).finrank_eq
    _ = ∑ k : {k : Fin b // k ∈ Kq b q}, Module.finrank ℝ (gapImage b p q ε k.1) :=
      Module.finrank_pi_fintype ℝ
    _ = ∑ k ∈ Kq b q, gapDim b p q ε k := by
      exact Finset.sum_coe_sort (Kq b q) (fun k => gapDim b p q ε k)
#print axioms Paper7Lemma22Gaps.deltaE_eq_sum_gapDim

end Paper7Lemma22Gaps
