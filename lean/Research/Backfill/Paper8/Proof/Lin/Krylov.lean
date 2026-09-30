import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Basic
import Research.Backfill.Paper8.Proof.Lin.BaseChange
import Research.Backfill.Paper8.Proof.Lin.Spectral

/-!
# Paper 8 back-fill (agent `lin`): Lemma 2.2 (Krylov certificate)

`rank_ℚ K = rank_ℝ K` (`rank_map_of_linearOrder`), the columns of `K` over `ℝ` are `A^j s`
(`j < d`), and their span has dimension `#{θ : P_θ s ≠ 0}` (`finrank_span_krylov`). If `K` has
rank `d` mod a prime, it has rank `d` over `ℚ` (`rank_rat_of_rank_zmod`), so every eigenvalue has
`P_θ s ≠ 0`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Lin

/-- The columns of `K` over `ℝ` are the vectors `A_ℝ^j s_ℝ`. -/
theorem krylov_col (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ) :
    ((Matrix.of fun i (j : Fin d) => ((A ^ (j : ℕ)) *ᵥ s) i).map (Int.cast : ℤ → ℝ)).col =
      fun j : Fin d => (A.map (Int.cast : ℤ → ℝ)) ^ (j : ℕ) *ᵥ (fun i => (s i : ℝ)) := by
  funext j i
  have h := RingHom.map_mulVec (Int.castRingHom ℝ) (A ^ (j : ℕ)) s i
  rw [Matrix.map_pow] at h
  simpa [Matrix.col, Function.comp_def] using h

/-- The first half of Lemma 2.2: `rank_ℚ K = #{θ : P_θ s ≠ 0}` (with `d` columns, `d` the number
of eigenvalues). -/
theorem krylov_rank (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) (s : Fin n → ℤ)
    (d : ℕ) (hd : d = {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ}.ncard) :
    ((Matrix.of fun i (j : Fin d) => ((A ^ (j : ℕ)) *ᵥ s) i).map (Int.cast : ℤ → ℚ)).rank =
      {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ ∧
        ProjNe (A.map (Int.cast : ℤ → ℝ)) θ (fun i => (s i : ℝ))}.ncard := by
  classical
  have hH : (A.map (Int.cast : ℤ → ℝ)).IsHermitian := isHermitian_iff_isSymm.2 (hA.map _)
  set K := Matrix.of fun i (j : Fin d) => ((A ^ (j : ℕ)) *ᵥ s) i with hK
  have h1 : (K.map (Int.cast : ℤ → ℚ)).rank = (K.map (Int.cast : ℤ → ℝ)).rank := by
    have : K.map (Int.cast : ℤ → ℝ) = (K.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℝ) := by
      ext i j
      simp
    rw [this, rank_map_of_linearOrder]
  rw [h1, rank_eq_finrank_span_cols, hK, krylov_col,
    finrank_span_krylov hH _ d (by rw [hd, card_eigSet hH]), ← Set.ncard_coe_finset]
  congr 1
  ext θ
  simp [mem_eigSet hH]

/-- **Lemma 2.2** (`lem:krylov`). -/
theorem lemma_2_2 : Lemma_2_2 := by
  intro n A hA s
  dsimp only
  have hH : (A.map (Int.cast : ℤ → ℝ)).IsHermitian := isHermitian_iff_isSymm.2 (hA.map _)
  refine ⟨krylov_rank n A hA s _ rfl, ?_⟩
  rintro ⟨p, hp, hrank⟩
  have hQ := rank_rat_of_rank_zmod _ p hp hrank
  rw [krylov_rank n A hA s _ rfl] at hQ
  have hsub : {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ ∧
      ProjNe (A.map (Int.cast : ℤ → ℝ)) θ (fun i => (s i : ℝ))} ⊆
      {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ} := fun θ h => h.1
  have hfin : {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ}.Finite := by
    rw [eigSet_coe hH]
    exact Finset.finite_toSet _
  have heq := Set.eq_of_subset_of_ncard_le hsub hQ.ge hfin
  intro θ hθ
  have hmem : θ ∈ {θ : ℝ | IsEigenvalue (A.map (Int.cast : ℤ → ℝ)) θ ∧
      ProjNe (A.map (Int.cast : ℤ → ℝ)) θ (fun i => (s i : ℝ))} := by
    rw [heq]
    exact hθ
  exact hmem.2

end P8Lin
