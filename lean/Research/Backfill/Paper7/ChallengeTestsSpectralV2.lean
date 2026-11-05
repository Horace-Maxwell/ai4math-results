import Research.Backfill.Paper7.ChallengeV2

/-!
# Known-answer tests for the spectral and real-valued custom definitions (Paper 7)

Addendum 1, item 2 (second file).  Small cases with known answers, proved with `simp`/`norm_num`
and Mathlib lemmas (`Matrix.charpoly_zero`, `Matrix.charpoly_one`, `Polynomial.roots_X_pow`,
`SimpleGraph.adjMatrix_bot`, `spectrum.zero_eq`).
-/

set_option autoImplicit false

namespace BackfillPaper7.Challenge

open Polynomial

/-! ### `eigs`, `nPos`, `nNeg`, `nZero` -/

theorem test_051 : eigs (0 : Matrix (Fin 3) (Fin 3) ℝ) = 3 • {0} := by
  simp [eigs, Matrix.charpoly_zero]

theorem test_052 : nZero (0 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
  simp [nZero, eigs, Matrix.charpoly_zero]

theorem test_053 : nPos (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [nPos, eigs, Matrix.charpoly_zero]

theorem test_054 : nPos (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  have h : (X - 1 : ℝ[X]) = X - C 1 := by rw [C_1]
  simp only [nPos, eigs, Matrix.charpoly_one, Fintype.card_fin, pow_one, h, Polynomial.roots_X_sub_C]
  rw [Multiset.filter_singleton, ite_eq_left (by norm_num : (0 : ℝ) < 1), Multiset.card_singleton]

theorem test_055 : nNeg (1 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
  have h : (X - 1 : ℝ[X]) = X - C 1 := by rw [C_1]
  simp only [nNeg, eigs, Matrix.charpoly_one, Fintype.card_fin, pow_one, h, Polynomial.roots_X_sub_C]
  simp

/-! ### `spec`, `mult`, `Ngt`, `Bplus`, `S2`, `bigEigs`, `Theta` on the empty graph -/

theorem test_056 : spec (⊥ : SimpleGraph (Fin 3)) = 3 • {0} := by
  simp [spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero]

theorem test_057 : mult (⊥ : SimpleGraph (Fin 3)) 0 = 3 := by
  simp [mult, spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero]

theorem test_058 : mult (⊥ : SimpleGraph (Fin 3)) 1 = 0 := by
  simp [mult, spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero]

theorem test_059 : Ngt (⊥ : SimpleGraph (Fin 3)) 0 = 0 := by
  simp [Ngt, spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero]

theorem test_060 : Ngt (⊥ : SimpleGraph (Fin 1)) (-1) = 1 := by
  simp only [Ngt, spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero, Fintype.card_fin,
    pow_one, Polynomial.roots_X]
  rw [Multiset.filter_singleton, ite_eq_left (by norm_num : (-1 : ℝ) < 0), Multiset.card_singleton]

theorem test_061 : Bplus (⊥ : SimpleGraph (Fin 3)) = 0 ∧ bigEigs (⊥ : SimpleGraph (Fin 3)) = 0 := by
  simp [Bplus, bigEigs, spec, eigs, SimpleGraph.adjMatrix_bot, Matrix.charpoly_zero]

theorem test_062 : Theta (⊥ : SimpleGraph (Fin 3)) = 0 := by
  simp [Theta]

/-! ### `IsIntegralGraph` -/

-- the empty graph is integral (spectrum `{0}`)
theorem test_063 : IsIntegralGraph (⊥ : SimpleGraph (Fin 3)) := by
  intro μ hμ
  rw [SimpleGraph.adjMatrix_bot, spectrum.zero_eq] at hμ
  exact ⟨0, by simpa using hμ⟩

/-! ### `cycleCount` -/

-- the empty graph has no cycle of length 3
theorem test_064 : cycleCount (⊥ : SimpleGraph (Fin 3)) 3 = 0 := by
  have : cycleEdgeSets (⊥ : SimpleGraph (Fin 3)) 3 = ∅ := by
    ext s
    simp only [cycleEdgeSets, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and]
    intro u w _ hlen _
    cases w with
    | nil => simp at hlen
    | cons h _ => exact h.elim
  simp [cycleCount, this]

/-! ### `Cyc`, `fk`, `Smat`, `Tk`, `Mono` -/

theorem test_065 : Cyc 5 0 1 = 1 := by
  rw [Cyc, SimpleGraph.adjMatrix_apply, ite_eq_left (by decide)]

theorem test_066 : Cyc 5 0 4 = 1 := by
  rw [Cyc, SimpleGraph.adjMatrix_apply, ite_eq_left (by decide)]

theorem test_067 : Cyc 5 0 2 = 0 := by
  rw [Cyc, SimpleGraph.adjMatrix_apply, ite_eq_right (by decide)]

-- `f_0(2) = p_0/2 + q_0·2/3` with `p_0 = 1`, `q_0 = 3`: `1/2 + 2 = 5/2`
theorem test_068 : fk 3 ![1, 0, 0] ![3, 0, 0] 2 0 = 5 / 2 := by
  norm_num [fk]

-- the bare triangle at `m = 2`: `T = [[2,-1],[1,0]]`, `M = T³ = [[4,-3],[3,-2]]`, `tr M = 2`,
-- `M ≠ I`: so `mult(2) = 1` for `C_3` (Lemma 2.2(a)), as the spectrum `{2, -1, -1}` says
theorem test_069 : Mono 3 (fun _ => 0) (fun _ => 0) 2 = !![4, -3; 3, -2] := by
  simp [Mono, Tk, fk, List.finRange_succ]
  norm_num

/-! ### `tridiagGen`, `pivCount` (Lemma 5.2 conventions) -/

theorem test_070 : tridiagGen 2 (fun _ => 0) (fun _ => 1) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tridiagGen]

-- `[[0,1],[1,0]]` (eigenvalues ±1): zero pivot, then the next index counts: one positive, one negative
theorem test_071 : pivCount true [(0, 0), (0, 1)] none = 1 ∧ pivCount false [(0, 0), (0, 1)] none = 1 := by
  norm_num [pivCount]

-- `[[1,1],[1,1]]` (eigenvalues 2, 0): pivots 1, then 1 - 1/1 = 0 (zero pivot, last index)
theorem test_072 : pivCount true [(1, 0), (1, 1)] none = 1 ∧ pivCount false [(1, 0), (1, 1)] none = 0 := by
  norm_num [pivCount]

/-! ### `IsDihedral` -/

theorem test_073 : IsDihedral 6 id := ⟨0, Or.inl fun k => by simp [Nat.mod_eq_of_lt k.isLt]⟩

end BackfillPaper7.Challenge

#print axioms BackfillPaper7.Challenge.test_051
#print axioms BackfillPaper7.Challenge.test_052
#print axioms BackfillPaper7.Challenge.test_053
#print axioms BackfillPaper7.Challenge.test_054
#print axioms BackfillPaper7.Challenge.test_055
#print axioms BackfillPaper7.Challenge.test_056
#print axioms BackfillPaper7.Challenge.test_057
#print axioms BackfillPaper7.Challenge.test_058
#print axioms BackfillPaper7.Challenge.test_059
#print axioms BackfillPaper7.Challenge.test_060
#print axioms BackfillPaper7.Challenge.test_061
#print axioms BackfillPaper7.Challenge.test_062
#print axioms BackfillPaper7.Challenge.test_063
#print axioms BackfillPaper7.Challenge.test_064
#print axioms BackfillPaper7.Challenge.test_065
#print axioms BackfillPaper7.Challenge.test_066
#print axioms BackfillPaper7.Challenge.test_067
#print axioms BackfillPaper7.Challenge.test_068
#print axioms BackfillPaper7.Challenge.test_069
#print axioms BackfillPaper7.Challenge.test_070
#print axioms BackfillPaper7.Challenge.test_071
#print axioms BackfillPaper7.Challenge.test_072
#print axioms BackfillPaper7.Challenge.test_073
