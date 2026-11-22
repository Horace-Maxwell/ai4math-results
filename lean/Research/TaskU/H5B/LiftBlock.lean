import Research.TaskU.H5B.LiftRing
import Research.TaskU.H5.IntegerFactors

namespace TaskU.H5.Spectrum
open Finset Matrix
open Cyc5 (V)
open scoped BigOperators

/-- Matrix in the integral power basis for the primitive central character. -/
def coordBlock (f : H → ℤ) : Matrix F F V := Matrix.of fun i j =>
  ∑ b : F, ∑ c : F, (f ⟨i-j,b,c⟩ : V)*Cyc5.rootAt (c+b*j)

theorem map_coordBlock (f : H → ℤ) (r : F) (hr : r ≠ 0) :
    (coordBlock f).map (Cyc5.valueHom (ch r) (Cyc5.character_rel r hr)) =
      frequencyBlock f 0 r := by
  ext i j : 1
  simp only [coordBlock, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_intCast,
    frequencyBlock, sumH, zero_mul, zero_add]
  simp only [Cyc5.valueHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Cyc5.val_rootAt_character _ _ hr]
  symm
  rw [Finset.sum_eq_single (i-j)]
  · simp [mul_comm r]
  · intro a _ hne
    have hn : i ≠ a+j := by intro h; exact hne (by rw [h]; abel)
    simp [hn]
  · simp

theorem norm_coordBlock (f : H → ℤ) :
    Cyc5.norm (coordBlock f).det = Cyc5.norm (TraceWords.nonlinear f) := by
  apply Int.cast_injective (α := ℂ)
  rw [norm_values, norm_values]
  apply prod_congr rfl
  intro r hr
  have hn := ne_of_mem_erase hr
  rw [val_nonlinear f r hn]
  change Cyc5.valueHom (ch r) (Cyc5.character_rel r hn) (coordBlock f).det = _
  rw [RingHom.map_det]
  exact congrArg Matrix.det (map_coordBlock f r hn)

/-- Executable column expansion with its proof of correctness. -/
def laplace : (n : ℕ) → Matrix (Fin n) (Fin n) V → V
  | 0, _ => 1
  | n+1, M => ∑ i : Fin (n+1),
      (-1:V)^i.val * M i 0 * laplace n (M.submatrix i.succAbove Fin.succ)

theorem laplace_correct (n : ℕ) (M : Matrix (Fin n) (Fin n) V) :
    laplace n M = M.det := by
  induction n with
  | zero => simp [laplace]
  | succ n ih => rw [laplace,Matrix.det_succ_column_zero]; simp_rw [ih]

theorem fiveLaplace (M : Matrix F F V) :
    laplace 5 M = M.det := laplace_correct 5 M

end TaskU.H5.Spectrum
