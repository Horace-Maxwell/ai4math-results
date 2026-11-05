import Research.Backfill.Paper7.IntroBipartiteEigenSign
import Research.Backfill.Paper7.IntroRadiusThreeProjectorAlgebra
import Research.Backfill.Paper7.IntegerSpectrum

/-! Rank-two formulas derived from the actual annihilator and the connected
Perron proportionality theorem. No rank or projection conclusion is a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroProjectors
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7Admissible Paper7OddIntegral

theorem symmetric_matrix_of_proportional_columns
    {V : Type} [Fintype V] (M : Matrix V V ℝ) (f : V → ℝ) (k : ℝ)
    (hM : M.IsSymm) (hn : f ⬝ᵥ f ≠ 0)
    (hc : ∀ j, ∃ t : ℝ, (fun i => M i j) = t • f)
    (he : M *ᵥ f = k • f) (u v : V) :
    M u v = (k / (f ⬝ᵥ f)) * f u * f v := by
  obtain ⟨t, ht⟩ := hc v
  have hm : t * (f ⬝ᵥ f) = k * f v := by
    calc
      t * (f ⬝ᵥ f) = f ⬝ᵥ (t • f) := by rw [dotProduct_smul]; ring
      _ = f ⬝ᵥ (fun i => M i v) := by rw [ht]
      _ = (M *ᵥ f) v := by
        change (∑ i, f i * M i v) = ∑ i, M v i * f i
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hM.apply v i]
        ring
      _ = k * f v := congrFun he v
  have htval : t = k * f v / (f ⬝ᵥ f) := (eq_div_iff hn).mpr hm
  have huv := congrFun ht u
  change M u v = t * f u at huv
  rw [huv, htval]
  ring
#print axioms Paper7IntroProjectors.symmetric_matrix_of_proportional_columns

theorem radius_three_projector_formulas
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hI : IsIntegralGraph G) (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (eps f : V → ℝ) (hs : ∀ i, eps i = 1 ∨ eps i = -1)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j)
    (hf : ∀ i, 0 < f i) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f) :
    ∀ u v,
      radiusThreeS (G.adjMatrix ℝ) u v =
        (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
      radiusThreeT (G.adjMatrix ℝ) u v =
        (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v) := by
  let A := G.adjMatrix ℝ
  let S := radiusThreeS A
  let T := radiusThreeT A
  let Mplus := S + (3 : ℝ) • T
  let Mminus := S - (3 : ℝ) • T
  let g := signTwist eps f
  have hn : f ⬝ᵥ f ≠ 0 := by
    intro hz
    have hzero : f = 0 := dotProduct_self_eq_zero.mp hz
    have hp := hf (Classical.choice (inferInstance : Nonempty V))
    simp only [hzero, Pi.zero_apply, lt_self_iff_false] at hp
  have hgn : g ⬝ᵥ g = f ⬝ᵥ f := signTwist_norm eps f hs
  have hgne : g ⬝ᵥ g ≠ 0 := by rw [hgn]; exact hn
  have hg : A *ᵥ g = (-3 : ℝ) • g := signTwist_eigenvector G eps f 3 hflip hAf
  obtain ⟨hAT, hAS⟩ := radiusThreeST_adj_relations G hI hbound
  change A * T = S at hAT
  change A * S = (9 : ℝ) • T at hAS
  obtain ⟨hS, hT⟩ := radiusThreeST_symmetric A G.isSymm_adjMatrix
  have hplusSym : Mplus.IsSymm := hS.add (hT.smul 3)
  have hminusSym : Mminus.IsSymm := hS.sub (hT.smul 3)
  have hplus : A * Mplus = (3 : ℝ) • Mplus := by
    change A * (S + (3 : ℝ) • T) = (3 : ℝ) • (S + (3 : ℝ) • T)
    rw [mul_add, Matrix.mul_smul, hAS, hAT]
    module
  have hminus : A * Mminus = (-3 : ℝ) • Mminus := by
    change A * (S - (3 : ℝ) • T) = (-3 : ℝ) • (S - (3 : ℝ) • T)
    rw [mul_sub, Matrix.mul_smul, hAS, hAT]
    module
  have hplusCols : ∀ j, ∃ t : ℝ, (fun i => Mplus i j) = t • f := by
    intro j
    have hcol : G.adjMatrix ℝ *ᵥ (fun i => Mplus i j) = (3 : ℝ) • (fun i => Mplus i j) := by
      funext i
      exact congrArg (fun M : Matrix V V ℝ => M i j) hplus
    exact graph_perron_proportional G hG 3 f hf hAf _ hcol
  have hminusCols : ∀ j, ∃ t : ℝ, (fun i => Mminus i j) = t • g := by
    intro j
    have hcol : G.adjMatrix ℝ *ᵥ (fun i => Mminus i j) = (-3 : ℝ) • (fun i => Mminus i j) := by
      funext i
      exact congrArg (fun M : Matrix V V ℝ => M i j) hminus
    exact negative_three_eigenvector_proportional G hG eps f _ hs hflip hf hAf hcol
  obtain ⟨hSf, hTf⟩ := radiusThreeST_eigenvector A 3 f hAf
  have hMp : Mplus *ᵥ f = (720 : ℝ) • f := by
    change (S + (3 : ℝ) • T) *ᵥ f = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hSf, hTf]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨hSg, hTg⟩ := radiusThreeST_eigenvector A (-3) g hg
  have hMm : Mminus *ᵥ g = (720 : ℝ) • g := by
    change (S - (3 : ℝ) • T) *ᵥ g = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hSg, hTg]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  intro u v
  have hp := symmetric_matrix_of_proportional_columns Mplus f 720 hplusSym hn hplusCols hMp u v
  have hm := symmetric_matrix_of_proportional_columns Mminus g 720 hminusSym hgne hminusCols hMm u v
  rw [hgn] at hm
  change S u v + 3 * T u v = (720 / (f ⬝ᵥ f)) * f u * f v at hp
  change S u v - 3 * T u v = (720 / (f ⬝ᵥ f)) * (eps u * f u) * (eps v * f v) at hm
  constructor
  · change S u v = _
    calc
      S u v = ((720 / (f ⬝ᵥ f)) * f u * f v +
        (720 / (f ⬝ᵥ f)) * (eps u * f u) * (eps v * f v)) / 2 := by linarith
      _ = _ := by ring
  · change T u v = _
    calc
      T u v = ((720 / (f ⬝ᵥ f)) * f u * f v -
        (720 / (f ⬝ᵥ f)) * (eps u * f u) * (eps v * f v)) / 6 := by linarith
      _ = _ := by ring
#print axioms Paper7IntroProjectors.radius_three_projector_formulas

theorem exists_positive_three_eigenvector_normalized
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hI : IsIntegralGraph G) (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (hthree : (integerSpectrum G).count 3 = 1) (o : V) :
    ∃ f : V → ℝ, (∀ i, 0 < f i) ∧ f o = 1 ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨r, hr, v, hv, _hnorm, hAv, _hrnonneg, _hsimple, _hupper, hdom⟩ := connected_perron G hG
  have hcount : (spec G).count (3 : ℝ) = 1 := by
    simpa only [integerSpectrum_count G hI, Int.cast_ofNat, mult] using hthree
  have hmem : (3 : ℝ) ∈ spec G := Multiset.count_pos.mp (by rw [hcount]; norm_num)
  have hlo : (3 : ℝ) ≤ r := by simpa using hdom 3 hmem
  have hhi : r ≤ 3 := (le_abs_self r).trans (hbound r hr)
  have hr3 : r = 3 := le_antisymm hhi hlo
  rw [hr3] at hAv
  let f : V → ℝ := (v o)⁻¹ • v
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    exact mul_pos (inv_pos.mpr (hv o)) (hv i)
  · change (v o)⁻¹ * v o = 1
    exact inv_mul_cancel₀ (ne_of_gt (hv o))
  · change G.adjMatrix ℝ *ᵥ ((v o)⁻¹ • v) = (3 : ℝ) • ((v o)⁻¹ • v)
    rw [Matrix.mulVec_smul, hAv]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
#print axioms Paper7IntroProjectors.exists_positive_three_eigenvector_normalized

theorem connected_bipartite_integral_radius_three_projectors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hI : IsIntegralGraph G) (hB : G.Colorable 2)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (hthree : (integerSpectrum G).count 3 = 1) (o : V) :
    ∃ eps f : V → ℝ,
      (∀ i, eps i = 1 ∨ eps i = -1) ∧
      (∀ i j, G.Adj i j → eps i = -eps j) ∧
      (∀ i, 0 < f i) ∧ f o = 1 ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (∑ i, if eps i = 1 then f i ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∑ i, if eps i = -1 then f i ^ 2 else 0) = (f ⬝ᵥ f) / 2 := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨eps, hs, hflip⟩ := colorable_two_has_real_sign G hB
  obtain ⟨f, hf, hfo, hAf⟩ := exists_positive_three_eigenvector_normalized G hG hI hbound hthree o
  obtain ⟨hp, hm⟩ := positive_three_bipartite_half_norm G eps f hs hflip hAf
  exact ⟨eps, f, hs, hflip, hf, hfo, hAf,
    radius_three_projector_formulas G hG hI hbound eps f hs hflip hf hAf, hp, hm⟩
#print axioms Paper7IntroProjectors.connected_bipartite_integral_radius_three_projectors

end Paper7IntroProjectors
