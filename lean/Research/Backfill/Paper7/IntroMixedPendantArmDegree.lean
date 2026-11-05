import Research.Backfill.Paper7.IntroIntegralRadiusThreeAnnihilator
import Research.Backfill.Paper7.IntroIntegralDegreeTwoChain
import Research.Backfill.Paper7.IntroFourRootLeafExclusion

/-! Actual mixed pendant arms force an exact degree under the integral
radius-three spectrum. The remainder of the graph is unrestricted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroMixedArms
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroPendantFour Paper7IntroLocalQuartic Paper7IntroFourExternal

theorem integral_radius_three_mixed_pendant_arms_degree_twelve
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (v y k l : V) (hvk : G.Adj v k) (hvy : G.Adj v y) (hyl : G.Adj y l)
    (hvl : v ≠ l) (hk : G.degree k = 1) (hy : G.degree y = 2)
    (hl : G.degree l = 1) : G.degree v = 12 := by
  let A := G.adjMatrix ℝ
  let ev : V → ℝ := Pi.single v 1
  let ey : V → ℝ := Pi.single y 1
  let ek : V → ℝ := Pi.single k 1
  let el : V → ℝ := Pi.single l 1
  let u : V → ℝ := ey - ek
  let F := radiusThreeFactor A
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have leafcol (i p : V) (hip : G.Adj i p) (hi : G.degree i = 1) :
      A *ᵥ Pi.single i 1 = Pi.single p 1 := by
    apply adjacency_single_one G i p
    obtain ⟨_j, _hij, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hi
    intro j
    constructor
    · intro hij
      exact (huniq j hij).trans (huniq p hip).symm
    · intro hjp
      exact hjp.symm ▸ hip
  have hAk : A *ᵥ ek = ev := leafcol k v hvk.symm hk
  have hAl : A *ᵥ el = ey := leafcol l y hyl.symm hl
  have hpair : ({v, l} : Finset V) ⊆ G.neighborFinset y := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hjv | hjl
    · rw [hjv]
      exact (G.mem_neighborFinset y v).mpr hvy.symm
    · rw [hjl]
      exact (G.mem_neighborFinset y l).mpr hyl
  have hpcard : ({v, l} : Finset V).card = 2 := by simp [hvl]
  have hset : ({v, l} : Finset V) = G.neighborFinset y := by
    apply Finset.eq_of_subset_of_card_le hpair
    rw [G.card_neighborFinset_eq_degree, hy, hpcard]
  have hyrow : ∀ j, G.Adj y j ↔ j = v ∨ j = l := by
    intro j
    rw [← G.mem_neighborFinset y j, ← hset, Finset.mem_insert, Finset.mem_singleton]
  have hAy : A *ᵥ ey = ev + el :=
    adjacency_single_of_two_neighbors G y v l hvl hyrow
  have hAu : A *ᵥ u = el := by
    change A *ᵥ (ey - ek) = el
    rw [Matrix.mulVec_sub, hAy, hAk]
    exact add_sub_cancel_left _ _
  have hA2u : A ^ 2 *ᵥ u = ey := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAu, hAl]
  have hmove : (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ u = ev - (3 : ℝ) • el := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, hA2u, Matrix.mulVec_smul, hAu, hAy]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : F *ᵥ (ev - (3 : ℝ) • el) = 0 := by
    have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ u)
      (integral_radius_three_matrix_annihilator G hI hbound)
    rw [Matrix.zero_mulVec] at h
    change (F * A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ u = 0 at h
    rwa [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hmove] at h
  have hA2l : A ^ 2 *ᵥ el = ev + el := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAl, hAy]
  have hA4l : A ^ 4 *ᵥ el = A ^ 2 *ᵥ ev + (ev + el) := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2,
      ← Matrix.mulVec_mulVec, hA2l, Matrix.mulVec_add, hA2l]
  have hFl : F *ᵥ el = A ^ 2 *ᵥ ev - (9 : ℝ) • ev := by
    rw [show F = radiusThreeFactor A from rfl, radiusThreeFactor,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hA4l, hA2l]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hFsym : F.IsSymm := by
    change (A ^ 4 - (10 : ℝ) • A ^ 2 + (9 : ℝ) • 1).IsSymm
    exact ((hA.pow 4).sub ((hA.pow 2).smul (10 : ℝ))).add
      (Matrix.isSymm_one.smul (9 : ℝ))
  have h2vv : (A ^ 2 *ᵥ ev) v = (G.degree v : ℝ) := by
    rw [Matrix.mulVec_single_one]
    change ((G.adjMatrix ℝ) ^ 2) v v = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have h2vl : (A ^ 2) v l = 1 := by
    have h := congrFun hA2l v
    simpa only [ev, el, Matrix.mulVec_single_one, Matrix.col_apply, Pi.add_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hvl, add_zero] using h
  have h2lv : (A ^ 2 *ᵥ ev) l = 1 := by
    rw [Matrix.mulVec_single_one]
    exact ((hA.pow 2).apply v l).trans h2vl
  have hFvv : (F *ᵥ ev) l = (G.degree v : ℝ) - 9 := by
    calc
      (F *ᵥ ev) l = (F *ᵥ el) v := by
        simpa only [ev, el, Matrix.mulVec_single_one, Matrix.col_apply] using hFsym.apply v l
      _ = (G.degree v : ℝ) - 9 := by
        rw [hFl]
        change (A ^ 2 *ᵥ ev) v - 9 * (Pi.single v (1 : ℝ) : V → ℝ) v = _
        rw [h2vv, Pi.single_eq_same, mul_one]
  have hFll : (F *ᵥ el) l = 1 := by
    rw [hFl]
    change (A ^ 2 *ᵥ ev) l - 9 * (Pi.single v (1 : ℝ) : V → ℝ) l = 1
    rw [h2lv, Pi.single_eq_of_ne hvl.symm, mul_zero, sub_zero]
  have h := congrFun hzero l
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at h
  rw [hFvv, hFll] at h
  have hd : (G.degree v : ℝ) = 12 := by linarith
  exact_mod_cast hd
#print axioms Paper7IntroMixedArms.integral_radius_three_mixed_pendant_arms_degree_twelve

end Paper7IntroMixedArms
