import Research.Backfill.Paper7.SpectrumGraphBasics
import Research.Backfill.Paper7.RankReductionAndNullity
import Research.Backfill.Paper7.Test114SpectralMultiplicity

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Spectrum

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem euclidean_kernel_finrank_eq_nullity {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin A)) = matrixNullity A := by
  have hr : A.rank = Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin A)) := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_eq_toLin] using!
      A.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℝ n) (PiLp.basisFun 2 ℝ n)
  have he : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin A)) +
      Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin A)) = Fintype.card n := by
    simpa only [finrank_euclideanSpace] using!
      (Matrix.toEuclideanLin A).finrank_range_add_finrank_ker
  have hm := Paper7Rank.rank_add_matrixNullity A
  omega

#print axioms Paper7Spectrum.euclidean_kernel_finrank_eq_nullity

theorem realHermitian_count_eq_shift_nullity {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    A.charpoly.roots.count μ = matrixNullity (A - μ • (1 : Matrix n n ℝ)) := by
  rw [Paper7Test114Generic.realHermitian_count_roots A hA μ, Module.End.eigenspace_def]
  have hshift : Matrix.toEuclideanLin (A - μ • (1 : Matrix n n ℝ)) =
      Matrix.toEuclideanLin A - μ • (1 : Module.End ℝ (EuclideanSpace ℝ n)) := by
    change Matrix.toLpLin 2 2 (A - μ • (1 : Matrix n n ℝ)) =
      Matrix.toLpLin 2 2 A - μ • (1 : Module.End ℝ (EuclideanSpace ℝ n))
    rw [map_sub, map_smul, Matrix.toLpLin_one, Module.End.one_eq_id]
  rw [← hshift]
  exact euclidean_kernel_finrank_eq_nullity _

#print axioms Paper7Spectrum.realHermitian_count_eq_shift_nullity

theorem overR_adjacency_shift {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℤ) :
    overR ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ)) =
      G.adjMatrix ℝ - (m : ℝ) • (1 : Matrix V V ℝ) := by
  ext i j
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;>
    simp [overR, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.intCast_apply, SimpleGraph.adjMatrix_apply, hij, hadj]

#print axioms Paper7Spectrum.overR_adjacency_shift

theorem mult_eq_rational_nullity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℤ) :
    mult G (m : ℝ) =
      matrixNullity (overQ ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ))) := by
  have hQR := (Paper7Rank.check_RankReductionAndNullity V
    ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ)) 2 Nat.prime_two).2.2.2.1
  calc
    mult G (m : ℝ) = matrixNullity (G.adjMatrix ℝ - (m : ℝ) • (1 : Matrix V V ℝ)) :=
      realHermitian_count_eq_shift_nullity (G.adjMatrix ℝ) (realAdjHermitian G) (m : ℝ)
    _ = matrixNullity (overR ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ))) := by
      rw [overR_adjacency_shift G m]
    _ = matrixNullity (overQ ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ))) := hQR.symm

#print axioms Paper7Spectrum.mult_eq_rational_nullity

end Paper7Spectrum
