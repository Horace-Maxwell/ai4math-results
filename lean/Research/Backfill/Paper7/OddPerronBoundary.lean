import Research.Backfill.Paper7.ConnectedPerron

set_option autoImplicit false

noncomputable section

namespace Paper7Admissible

open Matrix SimpleGraph BackfillPaper7.Challenge
open scoped Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem graph_abs_mulVec_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (i : V) :
    |(G.adjMatrix ℝ *ᵥ w) i| ≤ (G.adjMatrix ℝ *ᵥ (fun j => |w j|)) i := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    |∑ j, G.adjMatrix ℝ i j * w j| ≤ ∑ j, |G.adjMatrix ℝ i j * w j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, G.adjMatrix ℝ i j * |w j| := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [abs_mul, abs_of_nonneg (adj_nonnegative G i j)]
#print axioms Paper7Admissible.graph_abs_mulVec_le

omit [DecidableEq V] in
/-- A -r eigenvector has constant absolute ratio to the positive r vector.
Connectedness is used through actual walks and the maximum principle. -/
theorem negative_eigenvector_abs_ratio [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (r : ℝ) (hr : 0 ≤ r) (v w : V → ℝ) (hv : ∀ i, 0 < v i)
    (hve : G.adjMatrix ℝ *ᵥ v = r • v)
    (hwe : G.adjMatrix ℝ *ᵥ w = (-r) • w) (hw0 : w ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, |w i| = c * v i := by
  classical
  have hsuper (i : V) : r * |w i| ≤
      (G.adjMatrix ℝ *ᵥ (fun j => |w j|)) i := by
    have h := graph_abs_mulVec_le G w i
    rw [hwe] at h
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_nonneg hr] using h
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |w i| / v i)
    Finset.univ_nonempty
  let c := |w i₀| / v i₀
  let y : V → ℝ := c • v - (fun i => |w i|)
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    exact sub_nonneg.mpr ((div_le_iff₀ (hv i)).mp (hmax i (Finset.mem_univ i)))
  have hy₀ : y i₀ = 0 := by
    change |w i₀| / v i₀ * v i₀ - |w i₀| = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hv i₀)), sub_self]
  have hrow (i : V) : (G.adjMatrix ℝ *ᵥ y) i ≤ r * y i := by
    simp only [y, Matrix.mulVec_sub, Matrix.mulVec_smul, hve,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hsuper i]
  have hz := graph_nonnegative_supersolution_zero G hG r y hy hrow i₀ hy₀
  have hc (i : V) : |w i| = c * v i := by
    have h := congrFun hz i
    change c * v i - |w i| = 0 at h
    linarith
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra! h
    exact hw0 (funext h)
  have hcpos : 0 < c := by
    have hp := abs_pos.mpr hj
    rw [hc j] at hp
    nlinarith [hv j]
  exact ⟨c, hcpos, hc⟩
#print axioms Paper7Admissible.negative_eigenvector_abs_ratio

omit [DecidableEq V] in
theorem negative_eigenvector_ratio_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (r c : ℝ) (v w : V → ℝ) (hv : ∀ i, 0 < v i)
    (hve : G.adjMatrix ℝ *ᵥ v = r • v)
    (hwe : G.adjMatrix ℝ *ᵥ w = (-r) • w)
    (hab : ∀ i, |w i| = c * v i) (i j : V) (hij : G.Adj i j) :
    w j / v j = -(w i / v i) := by
  by_cases hi : 0 ≤ w i
  · have hwi : w i = c * v i := (abs_of_nonneg hi).symm.trans (hab i)
    let y : V → ℝ := c • v + w
    have hy (k : V) : 0 ≤ y k := by
      change 0 ≤ c * v k + w k
      rw [← hab k]
      linarith [neg_abs_le (w k)]
    have hrow : (G.adjMatrix ℝ *ᵥ y) i = 0 := by
      simp only [y, Matrix.mulVec_add, Matrix.mulVec_smul, hve, hwe,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwi]
      ring
    have hz := graph_nonnegative_neighbor_zero G y hy i j hij hrow
    have hwj : w j = -(c * v j) := by
      change c * v j + w j = 0 at hz
      linarith
    rw [hwi, hwj]
    field_simp [ne_of_gt (hv i), ne_of_gt (hv j)]
  · have hwi : w i = -(c * v i) := by
      have h := hab i
      rw [abs_of_neg (lt_of_not_ge hi)] at h
      linarith
    let y : V → ℝ := c • v - w
    have hy (k : V) : 0 ≤ y k := by
      change 0 ≤ c * v k - w k
      rw [← hab k]
      exact sub_nonneg.mpr (le_abs_self (w k))
    have hrow : (G.adjMatrix ℝ *ᵥ y) i = 0 := by
      simp only [y, Matrix.mulVec_sub, Matrix.mulVec_smul, hve, hwe,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwi]
      ring
    have hz := graph_nonnegative_neighbor_zero G y hy i j hij hrow
    have hwj : w j = c * v j := by
      change c * v j - w j = 0 at hz
      linarith
    rw [hwi, hwj]
    field_simp [ne_of_gt (hv i), ne_of_gt (hv j)]
#print axioms Paper7Admissible.negative_eigenvector_ratio_edge

omit [Fintype V] [DecidableEq V] in
theorem alternating_ratio_walk (G : SimpleGraph V) (z : V → ℝ)
    (hz : ∀ i j, G.Adj i j → z j = -z i) (i j : V) (w : G.Walk i j) :
    z j = (-1 : ℝ) ^ w.length * z i := by
  induction w with
  | nil => simp
  | @cons i j k hij w ih =>
    rw [ih, hz i j hij]
    simp only [SimpleGraph.Walk.length_cons, pow_succ]
    ring
#print axioms Paper7Admissible.alternating_ratio_walk

/-- An actual odd closed walk excludes -r, with no whole-spectrum symmetry claim. -/
theorem odd_closed_walk_excludes_negative_perron [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (r : ℝ) (hr : 0 ≤ r) (v : V → ℝ) (hv : ∀ i, 0 < v i)
    (hve : G.adjMatrix ℝ *ᵥ v = r • v)
    (i : V) (walk : G.Walk i i) (hodd : Odd walk.length) : (-r) ∉ spec G := by
  intro hspec
  obtain ⟨w, hnorm, hwe⟩ := eigs_unit_eigenvector (G.adjMatrix ℝ)
    (Paper7Spectrum.realAdjHermitian G) (-r) hspec
  have hw0 : w ≠ 0 := by
    intro hzero
    simp only [hzero, zero_dotProduct] at hnorm
    norm_num at hnorm
  obtain ⟨c, hc, hab⟩ := negative_eigenvector_abs_ratio G hG r hr v w hv hve hwe hw0
  have hedge := negative_eigenvector_ratio_edge G r c v w hv hve hwe hab
  have hw := alternating_ratio_walk G (fun j => w j / v j) hedge i i walk
  rw [hodd.neg_one_pow] at hw
  have hratio : w i / v i = 0 := by linarith
  have hwi : w i = 0 := (div_eq_zero_iff.mp hratio).resolve_right (ne_of_gt (hv i))
  have hpos : 0 < |w i| := by rw [hab i]; exact mul_pos hc (hv i)
  simp only [hwi, abs_zero, lt_self_iff_false] at hpos
#print axioms Paper7Admissible.odd_closed_walk_excludes_negative_perron

end Paper7Admissible
