import Research.Backfill.Paper7.IntroIntegralRadiusThreeAnnihilator

/-! Exact polynomial identities. The rank-two conclusion is not an assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroProjectors
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

def radiusThreeS {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ := by
  exact A ^ 6 - (5 : ℝ) • A ^ 4 + (4 : ℝ) • A ^ 2
#print axioms Paper7IntroProjectors.radiusThreeS

def radiusThreeT {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ := by
  exact A ^ 5 - (5 : ℝ) • A ^ 3 + (4 : ℝ) • A
#print axioms Paper7IntroProjectors.radiusThreeT

theorem radiusThreeST_factored {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) :
    radiusThreeS A = A ^ 2 * (A ^ 2 - 1) * (A ^ 2 - (4 : ℝ) • 1) ∧
    radiusThreeT A = A * (A ^ 2 - 1) * (A ^ 2 - (4 : ℝ) • 1) := by
  have h22 : A ^ 2 * A ^ 2 = A ^ 4 := (pow_add A 2 2).symm
  have h42 : A ^ 4 * A ^ 2 = A ^ 6 := (pow_add A 4 2).symm
  have h12 : A * A ^ 2 = A ^ 3 := (pow_succ' A 2).symm
  have h32 : A ^ 3 * A ^ 2 = A ^ 5 := (pow_add A 3 2).symm
  constructor
  · simp only [radiusThreeS, mul_sub, sub_mul, Matrix.mul_smul, mul_one, h22, h42]
    module
  · simp only [radiusThreeT, mul_sub, sub_mul, Matrix.mul_smul, mul_one, h12, h32]
    module
#print axioms Paper7IntroProjectors.radiusThreeST_factored

theorem radiusThreeST_symmetric {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) :
    (radiusThreeS A).IsSymm ∧ (radiusThreeT A).IsSymm := by
  exact ⟨((hA.pow 6).sub ((hA.pow 4).smul 5)).add ((hA.pow 2).smul 4),
    ((hA.pow 5).sub ((hA.pow 3).smul 5)).add (hA.smul 4)⟩
#print axioms Paper7IntroProjectors.radiusThreeST_symmetric

theorem radiusThreeST_adj_relations
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) :
    G.adjMatrix ℝ * radiusThreeT (G.adjMatrix ℝ) = radiusThreeS (G.adjMatrix ℝ) ∧
    G.adjMatrix ℝ * radiusThreeS (G.adjMatrix ℝ) = (9 : ℝ) • radiusThreeT (G.adjMatrix ℝ) := by
  let A := G.adjMatrix ℝ
  have h41 : A ^ 4 * A = A ^ 5 := (pow_succ A 4).symm
  have h21 : A ^ 2 * A = A ^ 3 := (pow_succ A 2).symm
  have h52 : A ^ 5 * A ^ 2 = A ^ 7 := (pow_add A 5 2).symm
  have h32 : A ^ 3 * A ^ 2 = A ^ 5 := (pow_add A 3 2).symm
  have h12 : A * A ^ 2 = A ^ 3 := (pow_succ' A 2).symm
  have hpoly : A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A = 0 := by
    have hz := integral_radius_three_matrix_annihilator G hI hbound
    change radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1) = 0 at hz
    have he : radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1) =
        A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A := by
      simp only [radiusThreeFactor, add_mul, sub_mul, mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, mul_one, one_mul, smul_smul, h41, h21, h52, h32, h12]
      module
    rwa [he] at hz
  have h16 : A * A ^ 6 = A ^ 7 := (pow_succ' A 6).symm
  have h14 : A * A ^ 4 = A ^ 5 := (pow_succ' A 4).symm
  have h15 : A * A ^ 5 = A ^ 6 := (pow_succ' A 5).symm
  have h13 : A * A ^ 3 = A ^ 4 := (pow_succ' A 3).symm
  have h11 : A * A = A ^ 2 := (pow_two A).symm
  constructor
  · change A * radiusThreeT A = radiusThreeS A
    simp only [radiusThreeT, radiusThreeS, mul_add, mul_sub, Matrix.mul_smul, h15, h13, h11]
  · change A * radiusThreeS A = (9 : ℝ) • radiusThreeT A
    apply sub_eq_zero.mp
    calc
      _ = A ^ 7 - (14 : ℝ) • A ^ 5 + (49 : ℝ) • A ^ 3 - (36 : ℝ) • A := by
        simp only [radiusThreeS, radiusThreeT, mul_add, mul_sub, Matrix.mul_smul, h16, h14, h12]
        module
      _ = 0 := hpoly
#print axioms Paper7IntroProjectors.radiusThreeST_adj_relations

theorem radiusThreeST_eigenvector
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (r : ℝ) (f : V → ℝ) (hf : A *ᵥ f = r • f) :
    radiusThreeS A *ᵥ f = (r ^ 6 - 5 * r ^ 4 + 4 * r ^ 2) • f ∧
    radiusThreeT A *ᵥ f = (r ^ 5 - 5 * r ^ 3 + 4 * r) • f := by
  have hp (k : ℕ) : A ^ k *ᵥ f = r ^ k • f := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul, ih]
      simp only [smul_smul, pow_succ, mul_comm]
  constructor
  · rw [radiusThreeS, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hp 6, hp 4, hp 2]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [radiusThreeT, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hp 5, hp 3, hf]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
#print axioms Paper7IntroProjectors.radiusThreeST_eigenvector

theorem radiusThreeST_integer_entries
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (∃ z : ℤ, radiusThreeS (G.adjMatrix ℝ) u v = z) ∧
    (∃ z : ℤ, radiusThreeT (G.adjMatrix ℝ) u v = z) := by
  let castM : Matrix V V ℤ →+* Matrix V V ℝ := (Int.castRingHom ℝ).mapMatrix
  have hc : castM (G.adjMatrix ℤ) = G.adjMatrix ℝ :=
    Paper7Moments.adjMatrix_map G (Int.castRingHom ℝ)
  have hp (k : ℕ) : (((G.adjMatrix ℤ) ^ k) u v : ℝ) = ((G.adjMatrix ℝ) ^ k) u v := by
    have he : castM ((G.adjMatrix ℤ) ^ k) = (G.adjMatrix ℝ) ^ k := by rw [map_pow, hc]
    exact congrArg (fun M : Matrix V V ℝ => M u v) he
  constructor
  · refine ⟨((G.adjMatrix ℤ) ^ 6) u v - 5 * ((G.adjMatrix ℤ) ^ 4) u v +
      4 * ((G.adjMatrix ℤ) ^ 2) u v, ?_⟩
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hp,
      radiusThreeS, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  · refine ⟨((G.adjMatrix ℤ) ^ 5) u v - 5 * ((G.adjMatrix ℤ) ^ 3) u v +
      4 * (G.adjMatrix ℤ) u v, ?_⟩
    have h1 : ((G.adjMatrix ℤ) u v : ℝ) = (G.adjMatrix ℝ) u v := by simpa only [pow_one] using hp 1
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hp, h1,
      radiusThreeT, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
#print axioms Paper7IntroProjectors.radiusThreeST_integer_entries

end Paper7IntroProjectors
