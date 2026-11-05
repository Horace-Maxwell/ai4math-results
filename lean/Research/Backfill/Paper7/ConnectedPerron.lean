import Research.Backfill.Paper7.PerronVariational
import Research.Backfill.Paper7.SpectrumNullity

set_option autoImplicit false

noncomputable section

namespace Paper7Admissible

open Matrix SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7Inertia
open scoped Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem adj_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    (0 : ℝ) ≤ G.adjMatrix ℝ i j := by
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]
#print axioms Paper7Admissible.adj_nonnegative

omit [DecidableEq V] in
theorem graph_nonnegative_neighbor_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → ℝ) (hy : ∀ i, 0 ≤ y i) (i j : V) (hij : G.Adj i j)
    (hrow : (G.adjMatrix ℝ *ᵥ y) i = 0) : y j = 0 := by
  have hterm := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset V)) =>
      mul_nonneg (adj_nonnegative G i k) (hy k)) (Finset.mem_univ j)
  have hle : y j ≤ (G.adjMatrix ℝ *ᵥ y) i := by
    simpa only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
      ite_eq_left hij, one_mul] using hterm
  exact le_antisymm (hrow ▸ hle) (hy j)
#print axioms Paper7Admissible.graph_nonnegative_neighbor_zero

omit [DecidableEq V] in
/-- A genuine maximum principle on reachable graph vertices. -/
theorem graph_nonnegative_supersolution_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (r : ℝ) (y : V → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hrow : ∀ i, (G.adjMatrix ℝ *ᵥ y) i ≤ r * y i)
    (i₀ : V) (hi₀ : y i₀ = 0) : y = 0 := by
  have hprop (i j : V) (hij : G.Adj i j) (hi : y i = 0) : y j = 0 := by
    have hn : 0 ≤ (G.adjMatrix ℝ *ᵥ y) i :=
      Finset.sum_nonneg (fun k hk => mul_nonneg (adj_nonnegative G i k) (hy k))
    have hp := hrow i
    rw [hi, mul_zero] at hp
    exact graph_nonnegative_neighbor_zero G y hy i j hij (le_antisymm hp hn)
  have hwalk (i j : V) (w : G.Walk i j) : y i = 0 → y j = 0 := by
    induction w with
    | nil => exact id
    | @cons i j k hij w ih =>
      intro hi
      exact ih (hprop i j hij hi)
  funext j
  obtain ⟨w⟩ := hG i₀ j
  exact hwalk i₀ j w hi₀
#print axioms Paper7Admissible.graph_nonnegative_supersolution_zero

omit [DecidableEq V] in
theorem graph_eigenvector_strictly_positive (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (r : ℝ) (v : V → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvnorm : v ⬝ᵥ v = 1) (hve : G.adjMatrix ℝ *ᵥ v = r • v) : ∀ i, 0 < v i := by
  intro i
  have hne : v i ≠ 0 := by
    intro hzero
    have hrow (j : V) : (G.adjMatrix ℝ *ᵥ v) j ≤ r * v j := by
      rw [hve]
      rfl
    have hz := graph_nonnegative_supersolution_zero G hG r v hv hrow i hzero
    have hn := hvnorm
    simp only [hz, zero_dotProduct] at hn
    norm_num at hn
  exact lt_of_le_of_ne (hv i) (Ne.symm hne)
#print axioms Paper7Admissible.graph_eigenvector_strictly_positive

omit [DecidableEq V] in
/-- All vectors in the actual Perron eigenspace are proportional to its positive vector. -/
theorem graph_perron_proportional [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (r : ℝ) (v : V → ℝ) (hv : ∀ i, 0 < v i)
    (hve : G.adjMatrix ℝ *ᵥ v = r • v)
    (w : V → ℝ) (hwe : G.adjMatrix ℝ *ᵥ w = r • w) :
    ∃ c : ℝ, w = c • v := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => w i / v i)
    Finset.univ_nonempty
  let c := w i₀ / v i₀
  let y : V → ℝ := c • v - w
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    have hi := (div_le_iff₀ (hv i)).mp (hmax i (Finset.mem_univ i))
    change 0 ≤ c * v i - w i
    exact sub_nonneg.mpr hi
  have hy₀ : y i₀ = 0 := by
    change w i₀ / v i₀ * v i₀ - w i₀ = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hv i₀)), sub_self]
  have he : G.adjMatrix ℝ *ᵥ y = r • y := by
    simp only [y, Matrix.mulVec_sub, Matrix.mulVec_smul, hve, hwe]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz := graph_nonnegative_supersolution_zero G hG r y hy
    (fun i => by rw [he]; rfl) i₀ hy₀
  refine ⟨c, ?_⟩
  funext i
  have hi := congrFun hz i
  change c * v i - w i = 0 at hi
  change w i = c * v i
  linarith
#print axioms Paper7Admissible.graph_perron_proportional

theorem graph_perron_simple [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (r : ℝ) (v : V → ℝ) (hv : ∀ i, 0 < v i)
    (hve : G.adjMatrix ℝ *ᵥ v = r • v) : mult G r = 1 := by
  have hv0 : v ≠ 0 := by
    intro hz
    have h := hv (Classical.choice (inferInstance : Nonempty V))
    simp only [hz, Pi.zero_apply, lt_self_iff_false] at h
  have hker : LinearMap.ker (Matrix.toLin'
      (G.adjMatrix ℝ - r • (1 : Matrix V V ℝ))) = Submodule.span ℝ ({v} : Set (V → ℝ)) := by
    ext w
    constructor
    · intro hw
      have he : G.adjMatrix ℝ *ᵥ w = r • w := by
        simpa only [LinearMap.mem_ker, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
          Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] using hw
      obtain ⟨c, hc⟩ := graph_perron_proportional G hG r v hv hve w he
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    · intro hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      simp only [LinearMap.mem_ker, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
        Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_smul, hve]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      ring
  change (G.adjMatrix ℝ).charpoly.roots.count r = 1
  rw [Paper7Spectrum.realHermitian_count_eq_shift_nullity (G.adjMatrix ℝ)
    (Paper7Spectrum.realAdjHermitian G) r, matrixNullity, hker]
  exact finrank_span_singleton hv0
#print axioms Paper7Admissible.graph_perron_simple

/-- The actual connected-graph Perron conclusion needed before the sun-specific lower bound. -/
theorem connected_perron [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ r ∈ spec G, ∃ v : V → ℝ,
      (∀ i, 0 < v i) ∧ v ⬝ᵥ v = 1 ∧ G.adjMatrix ℝ *ᵥ v = r • v ∧
      0 ≤ r ∧ mult G r = 1 ∧
      (∀ x, (G.adjMatrix ℝ).toQuadraticForm' x ≤ r * (x ⬝ᵥ x)) ∧
      (∀ s ∈ spec G, |s| ≤ r) := by
  obtain ⟨r, hr, v, hv, hvnorm, hve, hr0, hupper, hdom⟩ :=
    exists_nonnegative_top_eigenvector (G.adjMatrix ℝ)
      (Paper7Spectrum.realAdjHermitian G) (adj_nonnegative G)
  have hpos := graph_eigenvector_strictly_positive G hG r v hv hvnorm hve
  exact ⟨r, hr, v, hpos, hvnorm, hve, hr0,
    graph_perron_simple G hG r v hpos hve, hupper, hdom⟩
#print axioms Paper7Admissible.connected_perron

end Paper7Admissible
