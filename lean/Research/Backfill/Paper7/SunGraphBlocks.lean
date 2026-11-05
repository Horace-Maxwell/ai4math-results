import Research.Backfill.Paper7.SunBlockDefinitions

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open BackfillPaper7.Challenge

theorem sun_leaf_shift_entry {K : Type*} [CommRing K]
    (b : ℕ) (L : Fin b → List ℕ) (x : K) (k k' : Fin b)
    (j : Fin (L k).length) (j' : Fin (L k').length)
    (a : Fin ((L k).get j)) (a' : Fin ((L k').get j')) :
    (x • (1 : Matrix (SunV b L) (SunV b L) K) - (sunGraph b L).adjMatrix K)
        (Sum.inr ⟨k, j, a⟩) (Sum.inr ⟨k', j', a'⟩) =
      pendantShift b L x ⟨k, j, a⟩ ⟨k', j', a'⟩ := by
  classical
  by_cases hk : k = k'
  · subst k'
    by_cases hj : j = j'
    · subst j'
      simp only [pendantShift, Matrix.blockDiagonal'_apply_eq, pathShift,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        sun_same_arm_vertex_eq_iff, SimpleGraph.adjMatrix_apply, sun_arm_adj_iff,
        true_and]
      by_cases ha : a = a' <;> simp [ha]
    · have hjval : j.val ≠ j'.val := fun h => hj (Fin.ext h)
      have hv : (Sum.inr ⟨k, j, a⟩ : SunV b L) ≠ Sum.inr ⟨k, j', a'⟩ := by
        intro h
        apply hjval
        exact congrArg (fun v : SunV b L =>
          match v with
          | Sum.inl _ => 0
          | Sum.inr z => z.2.1.val) h
      have hn : ¬(sunGraph b L).Adj (Sum.inr ⟨k, j, a⟩) (Sum.inr ⟨k, j', a'⟩) := by
        intro h
        exact hjval ((sun_arm_adj_iff b L k k j j' a a').mp h).2.1
      rw [show pendantShift b L x ⟨k, j, a⟩ ⟨k, j', a'⟩ = 0 by
        unfold pendantShift
        rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne _ _ _ hj]]
      simp [Matrix.sub_apply, Matrix.smul_apply, 
        SimpleGraph.adjMatrix_apply, hv, hn]
  · have hv : (Sum.inr ⟨k, j, a⟩ : SunV b L) ≠ Sum.inr ⟨k', j', a'⟩ := by
      intro h
      apply hk
      exact congrArg (fun v : SunV b L =>
        match v with
        | Sum.inl z => z
        | Sum.inr z => z.1) h
    have hn : ¬(sunGraph b L).Adj (Sum.inr ⟨k, j, a⟩) (Sum.inr ⟨k', j', a'⟩) := by
      intro h
      exact hk ((sun_arm_adj_iff b L k k' j j' a a').mp h).1
    rw [show pendantShift b L x ⟨k, j, a⟩ ⟨k', j', a'⟩ = 0 by
      unfold pendantShift
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hk]
    simp [Matrix.sub_apply, Matrix.smul_apply, 
      SimpleGraph.adjMatrix_apply, hv, hn]

#print axioms Paper7Cleared.sun_leaf_shift_entry

/-- The actual shifted adjacency matrix of the original SunV graph has its
cycle/pendant decomposition, including all dependent path indices. -/
theorem sun_shift_fromBlocks {K : Type*} [CommRing K]
    (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (x : K) :
    x • (1 : Matrix (SunV b L) (SunV b L) K) - (sunGraph b L).adjMatrix K =
      Matrix.fromBlocks (cycleShift b x) (attachment b L)
        (attachment b L).transpose (pendantShift b L x) := by
  classical
  ext u v
  rcases u with i | ⟨k, j, a⟩ <;> rcases v with i' | ⟨k', j', a'⟩
  · simp only [Matrix.fromBlocks_apply₁₁, cycleShift, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Sum.inl.injEq,
      SimpleGraph.adjMatrix_apply, sun_cycle_adj_iff b L hb]
  · by_cases h : k' = i ∧ a'.val = 0 <;>
      simp [Matrix.fromBlocks_apply₁₂, attachment, Matrix.sub_apply,
        Matrix.smul_apply,  SimpleGraph.adjMatrix_apply,
        sun_root_arm_adj_iff, h]
  · by_cases h : k = i' ∧ a.val = 0 <;>
      simp [Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, attachment,
        Matrix.sub_apply, Matrix.smul_apply, 
        SimpleGraph.adjMatrix_apply, sun_arm_root_adj_iff, h]
  · change _ = pendantShift b L x ⟨k, j, a⟩ ⟨k', j', a'⟩
    exact sun_leaf_shift_entry b L x k k' j j' a a'

#print axioms Paper7Cleared.sun_shift_fromBlocks

end Paper7Cleared
