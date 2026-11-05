import Research.Backfill.Paper7.BMSTerminalInertia
import Research.Backfill.Paper7.BMSSpectralCounts
import Research.Backfill.Paper7.Lemma21SchurInertia
import Research.Backfill.Paper7.SpectralThresholdCounts

/-! The attachment core is arbitrary; no connectedness or bipartiteness is used. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7BMS
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
def terminalCoupling (v : ι) : Matrix ι (Fin 3) ℝ :=
  Matrix.of fun i j => if i = v then if j = 0 then 1 else 0 else 0
#print axioms Paper7BMS.terminalCoupling

omit [Fintype ι] in
def wideMatrix (M : Matrix ι ι ℝ) (v : ι) : Matrix (ι ⊕ Fin 3) (ι ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks M (terminalCoupling v) (terminalCoupling v)ᵀ terminalBlock
#print axioms Paper7BMS.wideMatrix

omit [Fintype ι] in
theorem wideMatrix_isHermitian (M : Matrix ι ι ℝ) (v : ι) (hM : M.IsHermitian) :
    (wideMatrix M v).IsHermitian :=
  hM.fromBlocks (by simp only [Matrix.conjTranspose_eq_transpose_of_trivial])
    terminalBlock_isHermitian
#print axioms Paper7BMS.wideMatrix_isHermitian

theorem wideMatrix_shift (M : Matrix ι ι ℝ) (v : ι) (x : ℝ) :
    wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) x =
      Matrix.fromBlocks (M - Matrix.diagonal (fun _ => x))
        (terminalCoupling v) (terminalCoupling v)ᵀ (terminalShift x) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [wideMatrix, terminalShift, Matrix.scalar_apply, Matrix.diagonal]
#print axioms Paper7BMS.wideMatrix_shift

omit [Fintype ι] in
theorem terminal_schur_product (v : ι) (x : ℝ) (hx : x*(2-x^2) ≠ 0) :
    terminalCoupling v * (terminalShift x)⁻¹ * (terminalCoupling v)ᵀ =
      Matrix.diagonal (fun i => terminalResolvent x * (if i = v then 1 else 0)) := by
  rw [terminal_inverse_eq x hx]
  apply Matrix.ext
  intro i j
  by_cases hi : i = v
  · subst i
    by_cases hj : j = v
    · subst j
      simp [terminalCoupling, terminalInverse, Matrix.mul_apply,
        Matrix.diagonal, terminalResolvent, div_eq_mul_inv,
        mul_comm]
    · simp [terminalCoupling, terminalInverse, Matrix.mul_apply,
        Matrix.diagonal, hj, Ne.symm hj]
  · by_cases hij : i = j
    · subst j
      simp [terminalCoupling, terminalInverse, Matrix.mul_apply,
        Matrix.diagonal, hi]
    · simp [terminalCoupling, terminalInverse, Matrix.mul_apply,
        Matrix.diagonal, hi, hij]
#print axioms Paper7BMS.terminal_schur_product

omit [Fintype ι] in
theorem terminal_schur_complement (M : Matrix ι ι ℝ) (v : ι) (x : ℝ)
    (hx : x*(2-x^2) ≠ 0) :
    (M - Matrix.diagonal (fun _ => x)) -
        terminalCoupling v * (terminalShift x)⁻¹ * (terminalCoupling v)ᵀ =
      terminalCoreShift M v x := by
  rw [terminal_schur_product v x hx]
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp only [terminalCoreShift, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    ring
  · simp [terminalCoreShift, Matrix.diagonal, h]
#print axioms Paper7BMS.terminal_schur_complement

theorem wideMatrix_schur_nPos (M : Matrix ι ι ℝ) (v : ι) (hM : M.IsHermitian)
    (x : ℝ) (hx : x*(2-x^2) ≠ 0) :
    nPos (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) x) =
      nPos (terminalCoreShift M v x) + nPos (terminalShift x) := by
  let : Invertible (terminalShift x) :=
    invertibleOfRightInverse _ _ (terminal_inverse_right x hx)
  rw [wideMatrix_shift]
  have h := (Paper7Lemma21.schur_inertia (M - Matrix.diagonal (fun _ => x))
    (terminalCoupling v) (terminalShift x)
    (hM.sub (Matrix.isHermitian_diagonal _)) (terminalShift_isHermitian x)).1
  rw [terminal_schur_complement M v x hx] at h
  exact h
#print axioms Paper7BMS.wideMatrix_schur_nPos

theorem wideMatrix_positive_count_drop (M : Matrix ι ι ℝ) (v : ι)
    (hM : M.IsHermitian) :
    nPos (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) rho) <
      nPos (wideMatrix M v - Matrix.scalar (ι ⊕ Fin 3) 1) := by
  rw [wideMatrix_schur_nPos M v hM rho rho_resolvent_denominator_ne,
    wideMatrix_schur_nPos M v hM 1 (by norm_num), terminal_nPos_rho, terminal_nPos_one]
  have h := terminalCoreShift_nPos_le M v hM
  omega
#print axioms Paper7BMS.wideMatrix_positive_count_drop

theorem nPos_shift_eq_filter (M : Matrix ι ι ℝ) (x : ℝ) :
    nPos (M - Matrix.scalar ι x) = ((eigs M).filter (fun y => x < y)).card := by
  simp only [nPos, eigs_real_shift, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro y _
  exact sub_pos
#print axioms Paper7BMS.nPos_shift_eq_filter

theorem wideMatrix_positive_interval (M : Matrix ι ι ℝ) (v : ι)
    (hM : M.IsHermitian) : ∃ x ∈ eigs (wideMatrix M v), 1 < x ∧ x ≤ rho := by
  apply exists_mem_Ioc_of_count_drop _ 1 rho one_lt_rho.le
  simpa only [nPos_shift_eq_filter] using wideMatrix_positive_count_drop M v hM
#print axioms Paper7BMS.wideMatrix_positive_interval

end Paper7BMS
