import Research.Backfill.Paper7.IntroFourCycleColumnStarWeights
import Research.Backfill.Paper7.IntroPureLeafStarLocalMoments

/-! Exact real norm saturation, followed by its actual graph realization.
The constants are explicit only in the generic intermediate interface. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafSaturation
open Matrix SimpleGraph Paper7IntroFourCycleWeights
open Paper7IntroPureLeafMoments Paper7IntroLocalQuartic

theorem three_leaf_finite_norm_saturation
    {V : Type} [Fintype V] [DecidableEq V]
    (F q : V → ℝ) (c : V) (Y : Finset V)
    (hc : c ∉ Y) (hm : Y.card = 3)
    (hFc : F c = 6) (hqc : q c = 4)
    (hFY : ∀ y ∈ Y, F y = 1) (hqY : ∀ y ∈ Y, q y = 1)
    (hFF : F ⬝ᵥ F = 120) (hqq : q ⬝ᵥ q = 28) (hqF : q ⬝ᵥ F = 54) :
    ∀ t, t ≠ c → t ∉ Y → F t = 3 * q t := by
  let e : V → ℝ := Pi.single c 1
  let L : V → ℝ := ∑ y ∈ Y, Pi.single y 1
  have hLv (y : V) : L y = if y ∈ Y then 1 else 0 := by
    change (∑ z ∈ Y, Pi.single z (1 : ℝ)) y = _
    rw [Finset.sum_apply, Finset.sum_pi_single]
  have hLdot (z : V → ℝ) (hz : ∀ y ∈ Y, z y = 1) : L ⬝ᵥ z = 3 := by
    change (∑ y ∈ Y, Pi.single y (1 : ℝ)) ⬝ᵥ z = 3
    rw [sum_dotProduct]
    calc
      _ = ∑ _y ∈ Y, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [single_dotProduct, one_mul, hz y hy]
      _ = 3 := by simp [hm]
  have hLL : L ⬝ᵥ L = 3 := hLdot L (fun y hy => by rw [hLv, ite_eq_left hy])
  have hLq : L ⬝ᵥ q = 3 := hLdot q hqY
  have hqL : q ⬝ᵥ L = 3 := (dotProduct_comm q L).trans hLq
  have hLF : L ⬝ᵥ F = 3 := hLdot F hFY
  have hFL : F ⬝ᵥ L = 3 := (dotProduct_comm F L).trans hLF
  have hee : e ⬝ᵥ e = 1 := by simp only [e, single_dotProduct, one_mul, Pi.single_eq_same]
  have heq : e ⬝ᵥ q = 4 := by simpa only [e, single_dotProduct, one_mul] using hqc
  have hqe : q ⬝ᵥ e = 4 := (dotProduct_comm q e).trans heq
  have heF : e ⬝ᵥ F = 6 := by simpa only [e, single_dotProduct, one_mul] using hFc
  have hFe : F ⬝ᵥ e = 6 := (dotProduct_comm F e).trans heF
  have heL : e ⬝ᵥ L = 0 := by
    rw [show e = Pi.single c 1 from rfl, single_dotProduct, one_mul, hLv, ite_eq_right hc]
  have hLe : L ⬝ᵥ e = 0 := (dotProduct_comm L e).trans heL
  let v := q - (4 : ℝ) • e - L
  let g := F - (6 : ℝ) • e - L
  have hv : v ⬝ᵥ v = 9 := by
    change (q - (4 : ℝ) • e - L) ⬝ᵥ (q - (4 : ℝ) • e - L) = 9
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      hqq, hqe, hqL, heq, hee, heL, hLq, hLe, hLL]
    norm_num
  have hg : g ⬝ᵥ g = 81 := by
    change (F - (6 : ℝ) • e - L) ⬝ᵥ (F - (6 : ℝ) • e - L) = 81
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      hFF, hFe, hFL, heF, hee, heL, hLF, hLe, hLL]
    norm_num
  have hvg : v ⬝ᵥ g = 27 := by
    change (q - (4 : ℝ) • e - L) ⬝ᵥ (F - (6 : ℝ) • e - L) = 27
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      hqF, hqe, hqL, heF, hee, heL, hLF, hLe, hLL]
    norm_num
  have hgv : g ⬝ᵥ v = 27 := (dotProduct_comm g v).trans hvg
  have hz : (g - (3 : ℝ) • v) ⬝ᵥ (g - (3 : ℝ) • v) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      hg, hgv, hvg, hv]
    norm_num
  have heqv : g = (3 : ℝ) • v := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz)
  intro t htc htY
  have het : e t = 0 := by simp only [e, Pi.single_eq_of_ne htc]
  have hLt : L t = 0 := by rw [hLv, ite_eq_right htY]
  have he := congrFun heqv t
  change F t - 6 * e t - L t = 3 * (q t - 4 * e t - L t) at he
  rw [het, hLt] at he
  linarith only [he]
#print axioms Paper7IntroThreeLeafSaturation.three_leaf_finite_norm_saturation

theorem actual_three_leaf_four_column_saturation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps f : V → ℝ)
    (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (a c : V) (Y : Finset V) (hc : c ∉ Y) (hm : Y.card = 3)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (hFY : ∀ y ∈ Y, f y = 1) (hfc : f c = 6) (hd : G.degree c = 4)
    (hside : (∑ v, if eps v = eps c then f v ^ 2 else 0) = 120)
    (hM4 : ((G.adjMatrix ℝ) ^ 4) c c = 28) :
    ∀ t, eps t = eps c → t ≠ c → t ∉ Y →
      f t = 3 * ((G.adjMatrix ℝ) ^ 2) t c := by
  let A := G.adjMatrix ℝ
  let q : V → ℝ := A ^ 2 *ᵥ Pi.single c 1
  let F : V → ℝ := fun v => if eps v = eps c then f v else 0
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hac : G.Adj a c := by
    apply (G.mem_neighborFinset a c).mp
    rw [hNa]
    exact Finset.mem_insert_self c Y
  have hqzero (v : V) (hv : eps v ≠ eps c) : q v = 0 := by
    change (A ^ 2 *ᵥ Pi.single c 1) v = 0
    rw [Matrix.mulVec_single_one]
    change ((G.adjMatrix ℝ) ^ 2) v c = 0
    rw [pow_two, G.adjMatrix_mul_apply]
    apply Finset.sum_eq_zero
    intro u hu
    have hvu := (G.mem_neighborFinset v u).mp hu
    have huc : ¬ G.Adj u c := by
      intro huc
      apply hv
      linarith only [hflip v u hvu, hflip u c huc]
    exact ite_eq_right huc
  have hFcc : F c = 6 := by simpa only [F, ↓reduceIte] using hfc
  have hFY' : ∀ y ∈ Y, F y = 1 := by
    intro y hy
    have hya := (hNl y hy a).mpr rfl
    have hs : eps y = eps c := by linarith only [hflip y a hya, hflip a c hac]
    simpa only [F, hs, ↓reduceIte] using hFY y hy
  have hqc : q c = 4 := by
    change (A ^ 2 *ᵥ Pi.single c 1) c = 4
    rw [Matrix.mulVec_single_one]
    change ((G.adjMatrix ℝ) ^ 2) c c = 4
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hd]
    norm_num
  have hqY : ∀ y ∈ Y, q y = 1 := by
    intro y hy
    have he := (actual_leaf_square_entry G y a c (hNl y hy)).2
    change (A ^ 2 *ᵥ Pi.single c 1) y = 1
    rw [Matrix.mulVec_single_one]
    change ((G.adjMatrix ℝ) ^ 2) y c = 1
    simpa only [hac, ↓reduceIte] using he
  have hFF : F ⬝ᵥ F = 120 := by
    calc
      F ⬝ᵥ F = ∑ v, if eps v = eps c then f v ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        dsimp only [F]
        split_ifs <;> ring
      _ = 120 := hside
  have hqq : q ⬝ᵥ q = 28 := by
    calc
      q ⬝ᵥ q = (A ^ 4) c c := by
        rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
          symmetric_square_diagonal (A ^ 2) (hA.pow 2) c]
      _ = 28 := hM4
  have hAf2 : A ^ 2 *ᵥ f = (9 : ℝ) • f := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAf, Matrix.mulVec_smul, hAf, smul_smul]
    norm_num
  have hqf : q ⬝ᵥ f = 54 := by
    calc
      q ⬝ᵥ f = f ⬝ᵥ A ^ 2 *ᵥ Pi.single c 1 := dotProduct_comm q f
      _ = Pi.single c 1 ⬝ᵥ A ^ 2 *ᵥ f := (hA.pow 2).dotProduct_mulVec_comm
      _ = 54 := by
        rw [hAf2, single_dotProduct]
        simp only [one_mul, Pi.smul_apply, smul_eq_mul, hfc]
        norm_num
  have hqF : q ⬝ᵥ F = 54 := by
    calc
      q ⬝ᵥ F = q ⬝ᵥ f := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hs : eps v = eps c
        · simp only [F, hs, ↓reduceIte]
        · simp only [F, hs, ↓reduceIte, hqzero v hs, zero_mul]
      _ = 54 := hqf
  intro t htc hne htY
  have he := three_leaf_finite_norm_saturation F q c Y hc hm hFcc hqc hFY' hqY hFF hqq hqF t hne htY
  simp only [F, htc, ↓reduceIte, q, Matrix.mulVec_single_one] at he
  change f t = 3 * (A ^ 2) t c at he
  change f t = 3 * (A ^ 2) t c
  exact he
#print axioms Paper7IntroThreeLeafSaturation.actual_three_leaf_four_column_saturation

end Paper7IntroThreeLeafSaturation
