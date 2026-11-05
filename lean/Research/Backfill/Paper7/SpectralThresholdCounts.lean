import Research.Backfill.Paper7.InertiaComparison

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix Polynomial BackfillPaper7.Challenge
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Translation of the actual characteristic-root multiset, including multiplicities. -/
theorem eigs_real_shift (M : Matrix ι ι ℝ) (m : ℝ) :
    eigs (M - Matrix.scalar ι m) = (eigs M).map (fun x => x-m) := by
  rw [eigs, Matrix.charpoly_sub_scalar]
  simpa [eigs] using Polynomial.roots_comp_C_mul_X_add_C M.charpoly (1 : ℝ) m isUnit_one
#print axioms Paper7Comparison.eigs_real_shift

theorem nPos_shift_eq_Ngt (G : SimpleGraph ι) [DecidableRel G.Adj] (m : ℝ) :
    nPos (G.adjMatrix ℝ - Matrix.scalar ι m) = Ngt G m := by
  simp only [nPos, eigs_real_shift, Ngt, spec, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  change 0 < x-m ↔ m < x
  exact sub_pos
#print axioms Paper7Comparison.nPos_shift_eq_Ngt

theorem nNeg_shift_eq_Nlt (G : SimpleGraph ι) [DecidableRel G.Adj] (m : ℝ) :
    nNeg (G.adjMatrix ℝ - Matrix.scalar ι m) = Nlt G m := by
  simp only [nNeg, eigs_real_shift, Nlt, spec, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  change x-m < 0 ↔ x < m
  exact sub_neg
#print axioms Paper7Comparison.nNeg_shift_eq_Nlt

theorem nonneg_shift_eq_Nge (G : SimpleGraph ι) [DecidableRel G.Adj] (m : ℝ) :
    nPos (G.adjMatrix ℝ - Matrix.scalar ι m) +
      nZero (G.adjMatrix ℝ - Matrix.scalar ι m) = Nge G m := by
  rw [nPos, nZero, multiset_pos_zero_eq_nonneg, eigs_real_shift]
  simp only [Nge, spec, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  change 0 ≤ x-m ↔ m ≤ x
  exact sub_nonneg
#print axioms Paper7Comparison.nonneg_shift_eq_Nge

theorem nonpos_shift_eq_Nle (G : SimpleGraph ι) [DecidableRel G.Adj] (m : ℝ) :
    nNeg (G.adjMatrix ℝ - Matrix.scalar ι m) +
      nZero (G.adjMatrix ℝ - Matrix.scalar ι m) = Nle G m := by
  rw [nNeg, nZero, multiset_neg_zero_eq_nonpos, eigs_real_shift]
  simp only [Nle, spec, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  change x-m ≤ 0 ↔ x ≤ m
  exact sub_nonpos
#print axioms Paper7Comparison.nonpos_shift_eq_Nle

end Paper7Comparison
