import Research.Backfill.Paper7.BMSWidePositive
import Research.Backfill.Paper7.MatrixInertiaEmbeddings

/-! Reflection is a similarity between two different core matrices, not a
claim that an arbitrary graph has a symmetric spectrum. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7BMS
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
def pendantSign : ι ⊕ Fin 3 → ℝ := Sum.elim (fun _ => 1) ![-1, 1, -1]
#print axioms Paper7BMS.pendantSign

omit [Fintype ι] [DecidableEq ι] in
theorem pendantSign_sq (i : ι ⊕ Fin 3) : pendantSign i * pendantSign i = 1 := by
  rcases i with i | i
  · simp [pendantSign]
  · fin_cases i <;> norm_num [pendantSign]
#print axioms Paper7BMS.pendantSign_sq

theorem pendantSign_inverse :
    Matrix.diagonal (pendantSign (ι := ι)) * Matrix.diagonal pendantSign = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [pendantSign_sq, Matrix.diagonal_one]
#print axioms Paper7BMS.pendantSign_inverse

theorem wideMatrix_sign_shift (M : Matrix ι ι ℝ) (v : ι) (x : ℝ) :
    (Matrix.diagonal pendantSign)ᵀ *
        (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) (-x)) *
        Matrix.diagonal pendantSign =
      -(wideMatrix (-M) v - Matrix.scalar (ι ⊕ Fin 3) x) := by
  rw [Matrix.diagonal_transpose]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply,
    Matrix.sub_apply]
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst j
      simp [pendantSign, wideMatrix, Matrix.scalar_apply, Matrix.diagonal, add_comm]
    · simp [pendantSign, wideMatrix, Matrix.scalar_apply, Matrix.diagonal, h]
  · fin_cases j <;>
      simp [pendantSign, wideMatrix, terminalCoupling, Matrix.scalar_apply,
        Matrix.diagonal]
  · fin_cases i
    · by_cases hj : j = v <;>
        simp [pendantSign, wideMatrix, terminalCoupling, Matrix.scalar_apply,
          Matrix.diagonal, hj]
    · simp [pendantSign, wideMatrix, terminalCoupling, Matrix.scalar_apply,
        Matrix.diagonal]
    · simp [pendantSign, wideMatrix, terminalCoupling, Matrix.scalar_apply,
        Matrix.diagonal]
  · fin_cases i <;> fin_cases j <;>
      simp [pendantSign, wideMatrix, terminalBlock, Matrix.scalar_apply,
        Matrix.diagonal]
#print axioms Paper7BMS.wideMatrix_sign_shift

theorem wideMatrix_negative_reflection (M : Matrix ι ι ℝ) (v : ι)
    (hM : M.IsHermitian) (x : ℝ) :
    nNeg (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) (-x)) =
      nPos (wideMatrix (-M) v - Matrix.scalar (ι ⊕ Fin 3) x) := by
  have h₁ : (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) (-x)).IsHermitian :=
    (wideMatrix_isHermitian M v hM).sub (Matrix.isHermitian_diagonal _)
  have h₂ : (wideMatrix (-M) v - Matrix.scalar (ι ⊕ Fin 3) x).IsHermitian :=
    (wideMatrix_isHermitian (-M) v hM.neg).sub (Matrix.isHermitian_diagonal _)
  have h := (inertia_congruence _ (Matrix.diagonal pendantSign)
    (Matrix.diagonal pendantSign) h₁ pendantSign_inverse pendantSign_inverse).2
  rw [wideMatrix_sign_shift, nNeg_neg _ h₂] at h
  exact h.symm
#print axioms Paper7BMS.wideMatrix_negative_reflection

theorem nNeg_shift_eq_filter (M : Matrix ι ι ℝ) (x : ℝ) :
    nNeg (M - Matrix.scalar ι x) = ((eigs M).filter (fun y => y < x)).card := by
  simp only [nNeg, eigs_real_shift, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro y _
  exact sub_neg
#print axioms Paper7BMS.nNeg_shift_eq_filter

theorem exists_mem_Ico_of_count_drop (s : Multiset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcount : (s.filter (fun x => x < a)).card < (s.filter (fun x => x < b)).card) :
    ∃ x ∈ s, a ≤ x ∧ x < b := by
  classical
  by_contra hnone
  have heq : s.filter (fun x => x < b) = s.filter (fun x => x < a) := by
    apply Multiset.filter_congr
    intro x hx
    constructor
    · intro hxb
      apply lt_of_not_ge
      intro hax
      exact hnone ⟨x, hx, hax, hxb⟩
    · intro hxa
      exact lt_of_lt_of_le hxa hab
  rw [heq] at hcount
  exact (lt_irrefl _) hcount
#print axioms Paper7BMS.exists_mem_Ico_of_count_drop

theorem wideMatrix_negative_interval (M : Matrix ι ι ℝ) (v : ι)
    (hM : M.IsHermitian) : ∃ x ∈ eigs (wideMatrix M v), -rho ≤ x ∧ x < -1 := by
  apply exists_mem_Ico_of_count_drop _ (-rho) (-1) (neg_le_neg one_lt_rho.le)
  have h := wideMatrix_positive_count_drop (-M) v hM.neg
  rw [← wideMatrix_negative_reflection M v hM rho,
    ← wideMatrix_negative_reflection M v hM 1] at h
  simpa only [nNeg_shift_eq_filter] using h
#print axioms Paper7BMS.wideMatrix_negative_interval

end Paper7BMS
