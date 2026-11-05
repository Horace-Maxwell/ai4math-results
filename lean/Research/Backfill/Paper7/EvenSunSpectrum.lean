import Research.Backfill.Paper7.Lemma22RealReduction

/-! Source candidate: the actual whole SunV graph has a sign-changing diagonal
involution when the cycle length is even. No assertion of bipartiteness is used
as an unproved premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Admissible
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def vertexDepth (b : ℕ) (L : Fin b → List ℕ) : SunV b L → ℕ
  | .inl k => k.val
  | .inr x => x.1.val + x.2.2.val + 1

def paritySign (n : ℕ) : ℝ := if n % 2 = 0 then 1 else -1

theorem paritySign_sq (n : ℕ) : paritySign n * paritySign n = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

theorem paritySign_opposite {n m : ℕ} (h : n % 2 ≠ m % 2) :
    paritySign n = -paritySign m := by
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  have hm := Nat.mod_lt m (by decide : 0 < 2)
  unfold paritySign
  split_ifs <;> norm_num <;> omega

theorem sunRel_depth_parity (b : ℕ) (L : Fin b → List ℕ) (he : Even b)
    (u v : SunV b L) (h : sunRel b L u v) :
    vertexDepth b L u % 2 ≠ vertexDepth b L v % 2 := by
  have hb2 : b % 2 = 0 := Nat.mod_eq_zero_of_dvd he.two_dvd
  cases u with
  | inl k =>
    cases v with
    | inl l =>
      change l.val = (k.val + 1) % b at h
      change k.val % 2 ≠ l.val % 2
      by_cases hk : k.val + 1 < b
      · rw [Nat.mod_eq_of_lt hk] at h
        omega
      · have heq : k.val + 1 = b := by omega
        rw [heq, Nat.mod_self] at h
        omega
    | inr x =>
      change x.1 = k ∧ x.2.2.val = 0 at h
      rcases h with ⟨hbase, hi⟩
      simp only [vertexDepth, hbase, hi, Nat.add_zero]
      omega
  | inr x =>
    cases v with
    | inl k => exact False.elim h
    | inr y =>
      change x.1 = y.1 ∧ x.2.1.val = y.2.1.val ∧ y.2.2.val = x.2.2.val + 1 at h
      rcases h with ⟨hbase, _, hi⟩
      simp only [vertexDepth, hbase, hi]
      omega

theorem sun_adj_sign (b : ℕ) (L : Fin b → List ℕ) (he : Even b)
    (u v : SunV b L) (h : (sunGraph b L).Adj u v) :
    paritySign (vertexDepth b L u) = -paritySign (vertexDepth b L v) := by
  apply paritySign_opposite
  rcases h.2 with huv | hvu
  · exact sunRel_depth_parity b L he u v huv
  · exact (sunRel_depth_parity b L he v u hvu).symm

theorem rank_diagonal_involution {V : Type} [Fintype V] [DecidableEq V]
    (D A : Matrix V V ℝ) (hD : D * D = 1) : (D * A * D).rank = A.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h : D * (D * A * D) * D = A := by
      calc
        D * (D * A * D) * D = (D * D) * A * (D * D) := by simp only [mul_assoc]
        _ = A := by rw [hD]; simp
    calc
      A.rank = (D * (D * A * D) * D).rank := congrArg Matrix.rank h.symm
      _ ≤ (D * A * D).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem graph_mult_sign_symmetry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → ℝ)
    (hs : ∀ v, s v * s v = 1)
    (hAdj : ∀ u v, G.Adj u v → s u = -s v) (μ : ℝ) :
    mult G μ = mult G (-μ) := by
  classical
  let D : Matrix V V ℝ := Matrix.diagonal s
  have hD : D * D = 1 := by
    ext u v
    by_cases huv : u = v <;> simp [D, Matrix.one_apply, huv, hs]
  have hshift :
      D * (μ • (1 : Matrix V V ℝ) - G.adjMatrix ℝ) * D =
        -( (-μ) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ) := by
    ext u v
    simp only [D, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
    by_cases huv : u = v
    · subst v
      simp only [Matrix.one_apply_eq, SimpleGraph.adjMatrix_apply,
        SimpleGraph.irrefl, ite_false, mul_one, sub_zero, neg_neg]
      linear_combination μ * hs u
    · by_cases h : G.Adj u v
      · simp only [Matrix.one_apply_ne huv, SimpleGraph.adjMatrix_apply, h,
          ite_true, mul_zero, zero_sub, neg_neg]
        rw [hAdj u v h]
        nlinarith [hs v]
      · simp [Matrix.one_apply_ne huv, SimpleGraph.adjMatrix_apply, h]
  have hneg (A : Matrix V V ℝ) : (-A).rank = A.rank := by
    simpa only [neg_one_smul] using Matrix.rank_smul_of_mem_nonZeroDivisors A
      (show (-1 : ℝ) ∈ nonZeroDivisors ℝ from
        mem_nonZeroDivisors_of_ne_zero (by norm_num))
  have hr := rank_diagonal_involution D (μ • (1 : Matrix V V ℝ) - G.adjMatrix ℝ) hD
  rw [hshift, hneg] at hr
  rw [Paper7Lemma22.mult_eq_real_shift_nullity,
    Paper7Lemma22.mult_eq_real_shift_nullity]
  have hp := Paper7Rank.rank_add_matrixNullity
    (μ • (1 : Matrix V V ℝ) - G.adjMatrix ℝ)
  have hn := Paper7Rank.rank_add_matrixNullity
    ((-μ) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ)
  omega

theorem even_sun_mult_symmetry (b : ℕ) (L : Fin b → List ℕ) (he : Even b) (x : ℝ) :
    mult (sunGraph b L) x = mult (sunGraph b L) (-x) :=
  graph_mult_sign_symmetry (sunGraph b L) (fun v => paritySign (vertexDepth b L v))
    (fun v => paritySign_sq (vertexDepth b L v)) (sun_adj_sign b L he) x

end Paper7Admissible
#print axioms Paper7Admissible.vertexDepth
#print axioms Paper7Admissible.paritySign
#print axioms Paper7Admissible.paritySign_sq
#print axioms Paper7Admissible.paritySign_opposite
#print axioms Paper7Admissible.sunRel_depth_parity
#print axioms Paper7Admissible.sun_adj_sign
#print axioms Paper7Admissible.rank_diagonal_involution
#print axioms Paper7Admissible.graph_mult_sign_symmetry
#print axioms Paper7Admissible.even_sun_mult_symmetry
