import Research.Backfill.Paper7.IntroIntegralQuarticPSD

/-! The integral quartic is strictly positive on every nonzero nonnegative
vector when a positive adjacency eigenvector has eigenvalue greater than two. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLocalQuartic
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem positive_eigenvector_quartic_nonnegative_vector_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hQ : (quarticGap A).PosSemidef)
    (r : ℝ) (y : V → ℝ) (hr : 2 < r) (hy : ∀ i, 0 < y i)
    (he : A *ᵥ y = r • y) (z : V → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hzpos : ∃ i, 0 < z i) :
    0 < z ⬝ᵥ quarticGap A *ᵥ z := by
  have hnonneg : 0 ≤ z ⬝ᵥ quarticGap A *ᵥ z := by
    simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg z
  by_contra hn
  have hzero : z ⬝ᵥ quarticGap A *ᵥ z = 0 :=
    le_antisymm (le_of_not_gt hn) hnonneg
  have hkernel : quarticGap A *ᵥ z = 0 :=
    hQ.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using hzero)
  have hcomm : z ⬝ᵥ quarticGap A *ᵥ y = y ⬝ᵥ quarticGap A *ᵥ z := by
    simpa only [star_trivial] using hQ.isHermitian.star_dotProduct_mulVec_comm z y
  rw [hkernel, dotProduct_zero] at hcomm
  have hzy : 0 < z ⬝ᵥ y := by
    apply Finset.sum_pos'
    · intro i _hi
      exact mul_nonneg (hz i) (le_of_lt (hy i))
    · obtain ⟨i, hi⟩ := hzpos
      exact ⟨i, Finset.mem_univ i, mul_pos hi (hy i)⟩
  have hpoly : 0 < r ^ 4 - 5 * r ^ 2 + 4 := by
    rw [show r ^ 4 - 5 * r ^ 2 + 4 = (r ^ 2 - 1) * (r ^ 2 - 4) from by ring]
    exact mul_pos (by nlinarith) (by nlinarith)
  rw [quarticGap_mulVec_eigenvector A r y he, dotProduct_smul, smul_eq_mul] at hcomm
  exact (ne_of_gt (mul_pos hpoly hzy)) hcomm
#print axioms Paper7IntroLocalQuartic.positive_eigenvector_quartic_nonnegative_vector_pos

theorem integral_connected_quartic_nonnegative_vector_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (z : V → ℝ) (hz : ∀ i, 0 ≤ z i) (hzpos : ∃ i, 0 < z i) :
    0 < z ⬝ᵥ quarticGap (G.adjMatrix ℝ) *ᵥ z := by
  obtain ⟨i, hi⟩ := hzpos
  let : Nonempty V := ⟨i⟩
  obtain ⟨r, _hr, y, hy, _hn, he, _hr0, _hm, _hu, hdom⟩ :=
    Paper7Admissible.connected_perron G hG
  have hr : 2 < r := lt_of_lt_of_le hs2 ((le_abs_self s).trans (hdom s hs))
  exact positive_eigenvector_quartic_nonnegative_vector_pos (G.adjMatrix ℝ)
    (integral_quarticGap_posSemidef G hI) r y hr hy he z hz ⟨i, hi⟩
#print axioms Paper7IntroLocalQuartic.integral_connected_quartic_nonnegative_vector_pos

end Paper7IntroLocalQuartic
