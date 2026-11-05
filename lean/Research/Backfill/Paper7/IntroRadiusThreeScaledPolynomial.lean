import Research.Backfill.Paper7.IntroIntegralRadiusThreeAnnihilator

/-! Scaled zero and plus/minus-one spectral polynomials. All identities are
derived from the actual integral graph's seven-root annihilator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroZeroOneProjectors
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

def radiusThreeQ0 {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ := by
  exact (36 : ℝ) • 1 - (49 : ℝ) • A ^ 2 + (14 : ℝ) • A ^ 4 - A ^ 6
#print axioms Paper7IntroZeroOneProjectors.radiusThreeQ0

def radiusThreeP1 {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ := by
  exact A ^ 6 - (13 : ℝ) • A ^ 4 + (36 : ℝ) • A ^ 2
#print axioms Paper7IntroZeroOneProjectors.radiusThreeP1

theorem symmetric_scaled_idempotent_nonnegative
    {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsSymm) (r : ℝ) (hr : 0 < r)
    (hsq : M ^ 2 = r • M) (v : V → ℝ) :
    0 ≤ v ⬝ᵥ M *ᵥ v := by
  have hn : 0 ≤ (M *ᵥ v) ⬝ᵥ (M *ᵥ v) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((M *ᵥ v) i)
  have he : (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = r * (v ⬝ᵥ M *ᵥ v) := by
    calc
      _ = v ⬝ᵥ M *ᵥ (M *ᵥ v) := hM.dotProduct_mulVec_comm
      _ = v ⬝ᵥ (M ^ 2) *ᵥ v := by rw [pow_two, ← Matrix.mulVec_mulVec]
      _ = r * (v ⬝ᵥ M *ᵥ v) := by
        rw [hsq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [he] at hn
  exact (mul_nonneg_iff_of_pos_left hr).mp hn
#print axioms Paper7IntroZeroOneProjectors.symmetric_scaled_idempotent_nonnegative

theorem integral_radius_three_Q0_P1_relations
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) :
    radiusThreeQ0 (G.adjMatrix ℝ) * G.adjMatrix ℝ = 0 ∧
      radiusThreeQ0 (G.adjMatrix ℝ) ^ 2 =
        (36 : ℝ) • radiusThreeQ0 (G.adjMatrix ℝ) ∧
      radiusThreeP1 (G.adjMatrix ℝ) ^ 2 =
        (24 : ℝ) • radiusThreeP1 (G.adjMatrix ℝ) := by
  let A := G.adjMatrix ℝ
  have h41 : A ^ 4 * A = A ^ 5 := (pow_succ A 4).symm
  have h21 : A ^ 2 * A = A ^ 3 := (pow_succ A 2).symm
  have h52 : A ^ 5 * A ^ 2 = A ^ 7 := (pow_add A 5 2).symm
  have h32 : A ^ 3 * A ^ 2 = A ^ 5 := (pow_add A 3 2).symm
  have h12 : A * A ^ 2 = A ^ 3 := (pow_succ' A 2).symm
  have hpoly : A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 -
      (36 : ℝ) • A = 0 := by
    have hz := integral_radius_three_matrix_annihilator G hI hbound
    change radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1) = 0 at hz
    have he : radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1) =
        A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A := by
      simp only [radiusThreeFactor, add_mul, sub_mul, mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, mul_one, one_mul, smul_smul, h41, h21, h52, h32, h12]
      module
    rwa [he] at hz
  have h61 : A ^ 6 * A = A ^ 7 := (pow_succ A 6).symm
  have hQA : radiusThreeQ0 A * A = 0 := by
    calc
      _ = -(A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A) := by
        simp only [radiusThreeQ0, add_mul, sub_mul, Matrix.smul_mul,
          one_mul, h21, h41, h61]
        module
      _ = 0 := by rw [hpoly, neg_zero]
  have h11 : A * A = A ^ 2 := (pow_two A).symm
  have h13 : A * A ^ 3 = A ^ 4 := (pow_succ' A 3).symm
  have h15 : A * A ^ 5 = A ^ 6 := (pow_succ' A 5).symm
  have hQfactor : radiusThreeQ0 A - (36 : ℝ) • 1 =
      A * ((-49 : ℝ) • A + (14 : ℝ) • A ^ 3 - A ^ 5) := by
    simp only [radiusThreeQ0, mul_add, mul_sub, Matrix.mul_smul, h11, h13, h15]
    module
  have hQsq : radiusThreeQ0 A ^ 2 = (36 : ℝ) • radiusThreeQ0 A := by
    have hz : radiusThreeQ0 A * (radiusThreeQ0 A - (36 : ℝ) • 1) = 0 := by
      rw [hQfactor, ← mul_assoc, hQA, zero_mul]
    rw [mul_sub, Matrix.mul_smul, mul_one, ← pow_two] at hz
    exact sub_eq_zero.mp hz
  have hPsq : radiusThreeP1 A ^ 2 = (24 : ℝ) • radiusThreeP1 A := by
    apply sub_eq_zero.mp
    calc
      _ = (A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A) *
          (A ^ 5 - (12 : ℝ) • A ^ 3 + (24 : ℝ) • A) := by
        rw [pow_two]
        simp only [radiusThreeP1, add_mul, sub_mul, mul_add, mul_sub,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add,
          ← pow_succ, ← pow_succ', h11]
        module
      _ = 0 := by rw [hpoly, zero_mul]
  exact ⟨hQA, hQsq, hPsq⟩
#print axioms Paper7IntroZeroOneProjectors.integral_radius_three_Q0_P1_relations

end Paper7IntroZeroOneProjectors
