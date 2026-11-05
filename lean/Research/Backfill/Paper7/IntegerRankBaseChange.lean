import Research.Backfill.Paper7.IntegerRankFactorization

/-! Rank bounds under integer casts; equality in every characteristic-zero field. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Rank

theorem intCast_rank_le (K : Type) [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) : (M.map (Int.castRingHom K)).rank ≤ M.rank := by
  obtain ⟨X, Y, _Z, hM, _hX, _hli⟩ := integer_rank_factorization M
  calc
    (M.map (Int.castRingHom K)).rank =
        (X.map (Int.castRingHom K) * Y.map (Int.castRingHom K)).rank := by
      rw [← Matrix.map_mul, ← hM]
    _ ≤ (X.map (Int.castRingHom K)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin M.rank) := Matrix.rank_le_card_width _
    _ = M.rank := Fintype.card_fin _

#print axioms Paper7Rank.intCast_rank_le

theorem intCast_rank_eq (K : Type) [Field K] [CharZero K]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ) :
    (M.map (Int.castRingHom K)).rank = M.rank := by
  apply le_antisymm (intCast_rank_le K M)
  obtain ⟨X, _Y, Z, _hM, hX, hli⟩ := integer_rank_factorization M
  have hliK : LinearIndependent K (X.map (Int.castRingHom K)).col := by
    change LinearIndependent K (fun j => algebraMap ℤ K ∘ X.col j)
    exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := K)).mpr hli
  have hrX : (X.map (Int.castRingHom K)).rank = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hliK, Fintype.card_fin]
  calc
    M.rank = (X.map (Int.castRingHom K)).rank := hrX.symm
    _ = (M.map (Int.castRingHom K) * Z.map (Int.castRingHom K)).rank := by
      rw [← Matrix.map_mul, ← hX]
    _ ≤ (M.map (Int.castRingHom K)).rank := Matrix.rank_mul_le_left _ _

#print axioms Paper7Rank.intCast_rank_eq

end Paper7Rank
