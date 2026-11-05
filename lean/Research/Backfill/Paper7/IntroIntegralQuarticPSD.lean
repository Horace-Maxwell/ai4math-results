import Research.Backfill.Paper7.SpectralMoments
import Research.Backfill.Paper7.ConnectedPerron

/-! A local positive semidefinite obstruction valid for every integral graph,
without an order bound, a cycle hypothesis or a supplied root profile. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLocalQuartic
open Matrix SimpleGraph BackfillPaper7.Challenge

def quarticGap {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ :=
  A ^ 4 - (5 : ℝ) • A ^ 2 + (4 : ℝ) • 1
#print axioms Paper7IntroLocalQuartic.quarticGap

theorem integer_quartic_nonneg (z : ℤ) :
    0 ≤ (z : ℝ) ^ 4 - 5 * (z : ℝ) ^ 2 + 4 := by
  have hf : (z : ℝ) ^ 4 - 5 * (z : ℝ) ^ 2 + 4 =
      ((z : ℝ) ^ 2 - 1) * ((z : ℝ) ^ 2 - 4) := by ring
  by_cases hlo : z ≤ -2
  · have h : (z : ℝ) ≤ -2 := by exact_mod_cast hlo
    rw [hf]
    exact mul_nonneg (by nlinarith) (by nlinarith)
  · by_cases hhi : 2 ≤ z
    · have h : 2 ≤ (z : ℝ) := by exact_mod_cast hhi
      rw [hf]
      exact mul_nonneg (by nlinarith) (by nlinarith)
    · have hz : z = -1 ∨ z = 0 ∨ z = 1 := by omega
      rcases hz with rfl | rfl | rfl <;> norm_num
#print axioms Paper7IntroLocalQuartic.integer_quartic_nonneg

theorem quarticGap_diagonal {V : Type} [Fintype V] [DecidableEq V]
    (d : V → ℝ) : quarticGap (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d i ^ 4 - 5 * d i ^ 2 + 4) := by
  have hfour : (4 : ℝ) • (1 : Matrix V V ℝ) = Matrix.diagonal (fun _ => 4) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [quarticGap, Matrix.diagonal_pow, Matrix.diagonal_pow,
    ← Matrix.diagonal_smul, Matrix.diagonal_sub, hfour, Matrix.diagonal_add]
  rfl
#print axioms Paper7IntroLocalQuartic.quarticGap_diagonal

theorem integral_quarticGap_posSemidef
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G) :
    (quarticGap (G.adjMatrix ℝ)).PosSemidef := by
  let hA := Paper7Spectrum.realAdjHermitian G
  let d : V → ℝ := hA.eigenvalues
  let F := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
  have hs : G.adjMatrix ℝ = F (Matrix.diagonal d) := by
    simpa [F, d] using hA.spectral_theorem
  have hd : ∀ i, 0 ≤ d i ^ 4 - 5 * d i ^ 2 + 4 := by
    intro i
    have hm : d i ∈ spec G := by
      change d i ∈ (G.adjMatrix ℝ).charpoly.roots
      rw [hA.roots_charpoly_eq_eigenvalues]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), by simp [d]⟩
    obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry G hI (d i) hm
    rw [hz]
    exact integer_quartic_nonneg z
  have hq : quarticGap (G.adjMatrix ℝ) =
      F (Matrix.diagonal (fun i => d i ^ 4 - 5 * d i ^ 2 + 4)) := by
    calc
      _ = F (quarticGap (Matrix.diagonal d)) := by
        rw [hs]
        simp only [quarticGap, map_add, map_sub, map_pow, map_smul, map_one]
      _ = _ := congrArg F (quarticGap_diagonal d)
  rw [hq]
  change ((hA.eigenvectorUnitary : Matrix V V ℝ) *
    Matrix.diagonal (fun i => d i ^ 4 - 5 * d i ^ 2 + 4) *
    (hA.eigenvectorUnitary : Matrix V V ℝ)ᴴ).PosSemidef
  exact (Matrix.posSemidef_diagonal_iff.mpr hd).mul_mul_conjTranspose_same _
#print axioms Paper7IntroLocalQuartic.integral_quarticGap_posSemidef

theorem quarticGap_mulVec_eigenvector
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (r : ℝ) (y : V → ℝ) (he : A *ᵥ y = r • y) :
    quarticGap A *ᵥ y = (r ^ 4 - 5 * r ^ 2 + 4) • y := by
  have hp (k : ℕ) : A ^ k *ᵥ y = r ^ k • y := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, ih]
      simp only [smul_smul, pow_succ, mul_comm]
  rw [quarticGap, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, hp 4, hp 2, Matrix.one_mulVec]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
#print axioms Paper7IntroLocalQuartic.quarticGap_mulVec_eigenvector

theorem positive_eigenvector_quartic_diagonal_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hQ : (quarticGap A).PosSemidef)
    (r : ℝ) (y : V → ℝ) (hr : 2 < r) (hy : ∀ i, 0 < y i)
    (he : A *ᵥ y = r • y) (i : V) : 0 < quarticGap A i i := by
  by_contra hn
  have hz : quarticGap A i i = 0 := le_antisymm (le_of_not_gt hn) hQ.diag_nonneg
  have hc : quarticGap A *ᵥ Pi.single i 1 = 0 :=
    hQ.dotProduct_mulVec_zero_iff.mp (by simpa using hz)
  have hcol (j : V) : quarticGap A j i = 0 := by
    rw [Matrix.mulVec_single_one] at hc
    exact congrFun hc j
  have hsym : (quarticGap A).IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.isHermitian
  have hrow (j : V) : quarticGap A i j = 0 := (hsym.apply i j).symm.trans (hcol j)
  have hzero : (quarticGap A *ᵥ y) i = 0 := by
    simp only [Matrix.mulVec, dotProduct, hrow, zero_mul, Finset.sum_const_zero]
  have h := congrFun (quarticGap_mulVec_eigenvector A r y he) i
  rw [hzero] at h
  have hpoly : 0 < r ^ 4 - 5 * r ^ 2 + 4 := by
    have hf : r ^ 4 - 5 * r ^ 2 + 4 = (r ^ 2 - 1) * (r ^ 2 - 4) := by ring
    rw [hf]
    exact mul_pos (by nlinarith) (by nlinarith)
  have hp := mul_pos hpoly (hy i)
  change 0 = (r ^ 4 - 5 * r ^ 2 + 4) * y i at h
  linarith
#print axioms Paper7IntroLocalQuartic.positive_eigenvector_quartic_diagonal_pos

theorem integral_connected_quartic_diagonal_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s) (i : V) :
    0 < quarticGap (G.adjMatrix ℝ) i i := by
  let : Nonempty V := ⟨i⟩
  obtain ⟨r, _hr, y, hy, _hn, he, _hr0, _hm, _hu, hdom⟩ :=
    Paper7Admissible.connected_perron G hG
  have hr : 2 < r := lt_of_lt_of_le hs2 ((le_abs_self s).trans (hdom s hs))
  exact positive_eigenvector_quartic_diagonal_pos (G.adjMatrix ℝ)
    (integral_quarticGap_posSemidef G hI) r y hr hy he i
#print axioms Paper7IntroLocalQuartic.integral_connected_quartic_diagonal_pos

end Paper7IntroLocalQuartic
