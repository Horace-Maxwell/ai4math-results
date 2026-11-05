import Mathlib

/-! Integral image bases give matrix factorizations in both directions. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Rank

theorem integer_rank_factorization {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) :
    ∃ (X : Matrix n (Fin M.rank) ℤ) (Y : Matrix (Fin M.rank) n ℤ)
      (Z : Matrix n (Fin M.rank) ℤ),
      M = X * Y ∧ X = M * Z ∧ LinearIndependent ℤ X.col := by
  classical
  let P : Submodule ℤ (n → ℤ) := LinearMap.range M.mulVecLin
  let b : Module.Basis (Fin M.rank) ℤ P := Module.finBasis ℤ P
  have hc (j : n) : M.col j ∈ P := by
    change M.col j ∈ LinearMap.range M.mulVecLin
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  let X : Matrix n (Fin M.rank) ℤ := fun i j => (b j).val i
  let Y : Matrix (Fin M.rank) n ℤ := fun i j => b.repr ⟨M.col j, hc j⟩ i
  have hM : M = X * Y := by
    ext i j
    change M i j = ∑ k : Fin M.rank, (b k).val i * b.repr ⟨M.col j, hc j⟩ k
    have h := congrArg (fun v : P => v.val i) (b.sum_repr ⟨M.col j, hc j⟩)
    have hs : (∑ k : Fin M.rank, b.repr ⟨M.col j, hc j⟩ k * (b k).val i) = M i j := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.col_apply] using h
    calc
      M i j = ∑ k : Fin M.rank, b.repr ⟨M.col j, hc j⟩ k * (b k).val i := hs.symm
      _ = ∑ k : Fin M.rank, (b k).val i * b.repr ⟨M.col j, hc j⟩ k := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact mul_comm _ _
  have hz : ∀ j : Fin M.rank, ∃ v : n → ℤ, M.mulVecLin v = (b j).val :=
    fun j => (b j).property
  choose z hz using hz
  let Z : Matrix n (Fin M.rank) ℤ := fun i j => z j i
  have hX : X = M * Z := by
    ext i j
    change (b j).val i = M.mulVecLin (z j) i
    exact (congrFun (hz j) i).symm
  have hli : LinearIndependent ℤ X.col := by
    change LinearIndependent ℤ (fun j => ((b j : P) : n → ℤ))
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  exact ⟨X, Y, Z, hM, hX, hli⟩

#print axioms Paper7Rank.integer_rank_factorization

end Paper7Rank
