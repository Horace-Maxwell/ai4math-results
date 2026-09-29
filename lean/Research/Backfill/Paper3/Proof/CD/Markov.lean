import Research.Backfill.Paper3.Proof.CD.Pd

/-!
# Markov bounds and the edge polynomials of `m K_{d,d}` and `G_n`

`#{A : e(A) ≤ T} ≤ q^{-T} P_G(q)` for `0 < q ≤ 1` and `#{A : e(A) > T} ≤ q^{-T} P_G(q)` for
`q ≥ 1` (termwise comparison with `q^{e(A) - T}`); `i_γ` as a filter count and its complement;
`P_{mK}(q) = P_d(q)^m`, `P_{G_n}(q) = P_{H_d}(q)^k P_d(q)^r`, `|V(G_n)| = 2dm`.
-/

set_option autoImplicit false

namespace P3CD

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem iGamma_eq_card (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (γ : ℝ) :
    iGamma G d γ =
      #(univ.filter fun A : Finset V => (edgesIn G A : ℝ) ≤ γ * d * Fintype.card V) := by
  unfold iGamma
  exact congrArg Finset.card (Finset.filter_congr fun A _ => Iff.rfl)

theorem card_le_add_card_gt (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℝ) :
    #(univ.filter fun A : Finset V => (edgesIn G A : ℝ) ≤ T) +
      #(univ.filter fun A : Finset V => T < (edgesIn G A : ℝ)) = 2 ^ Fintype.card V := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Finset V)))
    (fun A : Finset V => (edgesIn G A : ℝ) ≤ T)
  rw [Finset.card_univ, Fintype.card_finset] at h
  rw [← h]
  congr 2
  ext A
  simp [not_le]

theorem edgesIn_empty (G : SimpleGraph V) [DecidableRel G.Adj] : edgesIn G ∅ = 0 := by
  simp [edgesIn]

theorem one_le_iGamma (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    1 ≤ iGamma G d γ := by
  rw [iGamma_eq_card, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨∅, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgesIn_empty, Nat.cast_zero]
  positivity

theorem one_le_evalR_edgePoly (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ} (hq : 0 ≤ q) :
    1 ≤ evalR (edgePoly G) q := by
  rw [evalR_edgePoly]
  calc (1 : ℝ) = q ^ edgesIn G ∅ := by rw [edgesIn_empty, pow_zero]
    _ ≤ ∑ A : Finset V, q ^ edgesIn G A :=
      Finset.single_le_sum (f := fun A => q ^ edgesIn G A) (fun A _ => pow_nonneg hq _)
        (Finset.mem_univ _)

theorem evalR_edgePoly_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    evalR (edgePoly G) 1 = 2 ^ Fintype.card V := by
  rw [evalR_edgePoly]
  simp [Finset.card_univ, Fintype.card_finset]

/-- Lower-tail Markov bound: `#{A : e(A) ≤ T} ≤ q^{-T} P_G(q)` for `0 < q ≤ 1`. -/
theorem card_le_markov (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    (#(univ.filter fun A : Finset V => (edgesIn G A : ℝ) ≤ T) : ℝ) ≤
      q ^ (-T) * evalR (edgePoly G) q := by
  rw [evalR_edgePoly, Finset.mul_sum, Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun A _ => ?_
  split_ifs with h
  · rw [← Real.rpow_natCast, ← Real.rpow_add hq0]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1 (by linarith)
  · positivity

/-- Upper-tail Markov bound: `#{A : e(A) > T} ≤ q^{-T} P_G(q)` for `q ≥ 1`. -/
theorem card_gt_markov (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    (#(univ.filter fun A : Finset V => T < (edgesIn G A : ℝ)) : ℝ) ≤
      q ^ (-T) * evalR (edgePoly G) q := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [evalR_edgePoly, Finset.mul_sum, Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun A _ => ?_
  split_ifs with h
  · rw [← Real.rpow_natCast, ← Real.rpow_add hq0]
    exact Real.one_le_rpow hq (by linarith)
  · positivity

end General

/-! ### `m K_{d,d}` and `G_n` -/

theorem evalR_KddUnion (m d : ℕ) (q : ℝ) : evalR (edgePoly (KddUnion m d)) q = Pf d q ^ m := by
  rw [check_PolyFacts.2.2.1 m d, ← evalR_Pd]
  unfold evalR
  rw [map_pow]

theorem evalR_Gn (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) (q : ℝ) :
    evalR (edgePoly (Gn d m a₁ b₁ a₂ b₂)) q =
      evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q ^ (m / 2) * Pf d q ^ (m % 2) := by
  have h1 : edgePoly (Gn d m a₁ b₁ a₂ b₂) =
      edgePoly (copies (m / 2) (Hd d a₁ b₁ a₂ b₂)) * edgePoly (KddUnion (m % 2) d) :=
    edgePoly_sum _ _
  rw [h1, edgePoly_copies]
  have h2 : evalR (edgePoly (Hd d a₁ b₁ a₂ b₂) ^ (m / 2) * edgePoly (KddUnion (m % 2) d)) q =
      evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q ^ (m / 2) * evalR (edgePoly (KddUnion (m % 2) d)) q := by
    unfold evalR
    rw [map_mul, map_pow]
  rw [h2, evalR_KddUnion]

theorem card_GnV (d m : ℕ) : Fintype.card (GnV d m) = 2 * d * m := by
  simp only [GnV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  conv_rhs => rw [← Nat.div_add_mod m 2]
  ring

end P3CD
