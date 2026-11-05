import Research.Backfill.Paper7.SpectralMoments
import Research.Backfill.Paper7.SpectrumGraphBasics

/-! The exact seven-root annihilator for an arbitrary finite integral graph
whose real spectrum lies in [-3,3]. No restriction on branches is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPendantFour
open Matrix SimpleGraph BackfillPaper7.Challenge

def radiusThreeFactor {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ :=
  A ^ 4 - (10 : ℝ) • A ^ 2 + (9 : ℝ) • 1
#print axioms Paper7IntroPendantFour.radiusThreeFactor

theorem scalar_one_diagonal {V : Type} [Fintype V] [DecidableEq V] (r : ℝ) :
    r • (1 : Matrix V V ℝ) = Matrix.diagonal (fun _ => r) := by
  ext i j
  by_cases h : i = j <;> simp [h]
#print axioms Paper7IntroPendantFour.scalar_one_diagonal

theorem radiusThreeFactor_diagonal {V : Type} [Fintype V] [DecidableEq V]
    (d : V → ℝ) : radiusThreeFactor (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d i ^ 4 - 10 * d i ^ 2 + 9) := by
  rw [radiusThreeFactor, Matrix.diagonal_pow, Matrix.diagonal_pow,
    ← Matrix.diagonal_smul, Matrix.diagonal_sub, scalar_one_diagonal,
    Matrix.diagonal_add]
  rfl
#print axioms Paper7IntroPendantFour.radiusThreeFactor_diagonal

theorem integer_radius_three_annihilator (z : ℤ) (hz : |z| ≤ 3) :
    ((z : ℝ) ^ 4 - 10 * (z : ℝ) ^ 2 + 9) * (z : ℝ) *
      ((z : ℝ) ^ 2 - 4) = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  interval_cases z <;> norm_num
#print axioms Paper7IntroPendantFour.integer_radius_three_annihilator

theorem integral_radius_three_matrix_annihilator
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ x ∈ spec G, |x| ≤ 3) :
    radiusThreeFactor (G.adjMatrix ℝ) * G.adjMatrix ℝ *
      ((G.adjMatrix ℝ) ^ 2 - (4 : ℝ) • 1) = 0 := by
  let hA := Paper7Spectrum.realAdjHermitian G
  let d : V → ℝ := hA.eigenvalues
  let D : Matrix V V ℝ := Matrix.diagonal d
  let F := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
  have hs : G.adjMatrix ℝ = F D := by
    simpa [F, D, d] using hA.spectral_theorem
  have hd : ∀ i, (d i ^ 4 - 10 * d i ^ 2 + 9) * d i * (d i ^ 2 - 4) = 0 := by
    intro i
    have hm : d i ∈ spec G := by
      change d i ∈ (G.adjMatrix ℝ).charpoly.roots
      rw [hA.roots_charpoly_eq_eigenvalues]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), by simp [d]⟩
    obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry G hI (d i) hm
    have hb := hbound (d i) hm
    rw [hz] at hb ⊢
    exact integer_radius_three_annihilator z (by exact_mod_cast hb)
  have hD : radiusThreeFactor D * D * (D ^ 2 - (4 : ℝ) • 1) = 0 := by
    change radiusThreeFactor (Matrix.diagonal d) * Matrix.diagonal d *
      ((Matrix.diagonal d) ^ 2 - (4 : ℝ) • 1) = 0
    rw [radiusThreeFactor_diagonal, Matrix.diagonal_pow, scalar_one_diagonal,
      Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
      exact hd i
    · simp [h]
  calc
    _ = F (radiusThreeFactor D * D * (D ^ 2 - (4 : ℝ) • 1)) := by
      rw [hs]
      simp only [radiusThreeFactor, map_mul, map_add, map_sub, map_pow,
        map_smul, map_one]
    _ = 0 := by rw [hD, map_zero]
#print axioms Paper7IntroPendantFour.integral_radius_three_matrix_annihilator

end Paper7IntroPendantFour
