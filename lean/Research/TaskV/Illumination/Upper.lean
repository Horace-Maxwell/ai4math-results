import Research.TaskV.Illumination.Planar

namespace PrismIllumination

private def core : Set Space := {p | 0 < p 0 ∧ 0 < p 1 ∧ p 0 + p 1 < 1 ∧
  0 < p 2 ∧ p 2 < 1}

private theorem open_core : IsOpen core := by
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter <|
    (isOpen_lt continuous_const (continuous_apply 1)).inter <|
    (isOpen_lt ((continuous_apply 0).add (continuous_apply 1)) continuous_const).inter <|
    (isOpen_lt continuous_const (continuous_apply 2)).inter <|
    isOpen_lt (continuous_apply 2) continuous_const

private theorem core_prism : core ⊆ prism := by
  intro p h
  obtain ⟨a,b,c,d,e⟩ := h
  refine ⟨?_, c.le⟩
  intro i
  fin_cases i
  · change 0 ≤ p 0 ∧ p 0 ≤ 1
    constructor <;> linarith
  · change 0 ≤ p 1 ∧ p 1 ≤ 1
    constructor <;> linarith
  · exact ⟨d.le, e.le⟩

private def beam (e : ℝ) (j : ℕ) (v : ℝ) : Space := ![dx e j, dy e j, v]

private theorem beam_ne (e : ℝ) (j : ℕ) {v : ℝ} (hv : v ≠ 0) : beam e j v ≠ 0 := by
  intro h
  exact hv (congrFun h 2)

private theorem hit {K : Set Space} (hP : prism ⊆ K) {p : Space} {e v : ℝ} {j : ℕ}
    (hs : Step (p 0) (p 1) (dx e j) (dy e j))
    (height : ∀ t : ℝ, 0 < t → t < 1 → 0 < p 2 + t*v ∧ p 2 + t*v < 1) :
    Illuminates K (beam e j v) p := by
  obtain ⟨t, ht, hT, hx, hy, hxy⟩ := hs
  obtain ⟨hz,hZ⟩ := height t ht hT
  refine ⟨t, ht, interior_maximal (core_prism.trans hP) open_core ?_⟩
  exact ⟨hx, hy, hxy, hz, hZ⟩

private def level (b : Bool) (z : ℝ) := if b then 1-z else z
private def orient (b : Bool) (v : ℝ) := if b then -v else v

private theorem oriented_ne (b : Bool) {v : ℝ} (hv : v ≠ 0) : orient b v ≠ 0 := by
  cases b <;> simp [orient, hv]

private theorem level_bounds (b : Bool) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ level b z ∧ level b z ≤ 1 := by
  cases b <;> simp [level] <;> constructor <;> linarith [hz.1,hz.2]

private theorem from_level (b : Bool) {z t v : ℝ}
    (h : 0 < level b z + t*v ∧ level b z + t*v < 1) :
    0 < z + t * orient b v ∧ z + t * orient b v < 1 := by
  cases b <;> simp only [level,orient,Bool.false_eq_true,ite_false,ite_true,mul_neg] at * <;>
    constructor <;> linarith [h.1,h.2]

private def lamps (split : ℕ) (e up down : ℝ) (i : ℕ) : Space :=
  if i < split then beam e i up else beam e (i-split) down

private theorem lamps_ne (k i : ℕ) (e : ℝ) {v w : ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    lamps k e v w i ≠ 0 := by
  unfold lamps
  split <;> exact beam_ne _ _ (by assumption)

private theorem fromFirst {K : Set Space} {p : Space} {j k n : ℕ} {e v w : ℝ}
    (hj : j < k) (hkn : k ≤ n) (h : Illuminates K (beam e j v) p) :
    ∃ i : Fin n, Illuminates K (lamps k e v w i.val) p := by
  exact ⟨⟨j, by omega⟩, by simpa [lamps, hj] using h⟩

private theorem fromSecond {K : Set Space} {p : Space} {j k n : ℕ} {e v w : ℝ}
    (hj : j+k < n) (h : Illuminates K (beam e j w) p) :
    ∃ i : Fin n, Illuminates K (lamps k e v w i.val) p := by
  exact ⟨⟨j+k, hj⟩, by simpa [lamps] using h⟩

private theorem rise {z t v : ℝ} (hz : 0 ≤ z) (hroom : z + v < 1)
    (hv : 0 < v) (ht : 0 < t) (hT : t < 1) : 0 < z+t*v ∧ z+t*v < 1 := by
  constructor <;> nlinarith [mul_pos ht hv, mul_lt_mul_of_pos_right hT hv]

private theorem fall {z t v : ℝ} (hz : z ≤ 1) (hroom : v < z)
    (hv : 0 < v) (ht : 0 < t) (hT : t < 1) : 0 < z+t*(-v) ∧ z+t*(-v) < 1 := by
  constructor <;> nlinarith [mul_pos ht hv, mul_lt_mul_of_pos_right hT hv]

theorem upperSix {K : Set Space} (hc : IsClosed K) (hP : prism ⊆ K) (hQ : K ⊆ cube)
    {r : ℝ} (hr : 0 < r) (hg : ∀ p ∈ K, r ≤ max (1-p 0) (1-p 1)) : CanLight K 6 := by
  obtain ⟨e, he, hE⟩ := exists_between (lt_min (by norm_num : (0:ℝ) < 1/4) hr)
  have her := lt_of_lt_of_le hE (min_le_right _ _)
  have he1 := lt_of_lt_of_le hE (min_le_left _ _)
  refine ⟨fun i => lamps 3 e (1/4) (-(1/4)) i.val, fun _ => lamps_ne _ _ _ (by norm_num) (by norm_num), ?_⟩
  intro p hp
  have hK := hc.frontier_subset hp
  have H := hQ hK
  obtain ⟨j,hj,hs⟩ := planarThree (H 0).1 (H 0).2 (H 1).1 (H 1).2 he
    (by linarith : e < 1) her (hg p hK)
  by_cases hz : p 2 ≤ 1/2
  · apply fromFirst hj (by decide)
    exact hit hP hs (fun _ ht hT => rise (H 2).1 (by linarith) (by norm_num) ht hT)
  · apply fromSecond (by omega : j+3 < 6)
    exact hit hP hs (fun _ ht hT => fall (H 2).2 (by linarith) (by norm_num) ht hT)

theorem upperSeven {K : Set Space} (hc : IsClosed K) (hP : prism ⊆ K) (hQ : K ⊆ cube)
    (b : Bool) {r : ℝ} (hr : 0 < r)
    (hg : ∀ p ∈ K, r ≤ max (max (1-p 0) (1-p 1)) (if b then 1-p 2 else p 2)) :
    CanLight K 7 := by
  obtain ⟨e, he, hE⟩ := exists_between (lt_min (by norm_num : (0:ℝ) < 1/4) (show 0 < r/3 by linarith))
  have heR := lt_of_lt_of_le hE (min_le_right _ _)
  have he4 := lt_of_lt_of_le hE (min_le_left _ _)
  refine ⟨fun i => lamps 3 e (orient b e) (orient b (-e)) i.val,
    fun _ => lamps_ne _ _ _ (oriented_ne _ he.ne') (oriented_ne _ (neg_ne_zero.mpr he.ne')), ?_⟩
  intro p hp
  have hK := hc.frontier_subset hp
  have H := hQ hK
  have hL := level_bounds b (H 2)
  by_cases hz : level b (p 2) ≤ 2*e
  · have g : r ≤ max (1-p 0) (1-p 1) :=
      (le_max_iff.mp (show r ≤ max _ (level b (p 2)) from hg p hK)).resolve_right (by linarith)
    obtain ⟨j,hj,hs⟩ := planarThree (H 0).1 (H 0).2 (H 1).1 (H 1).2 he
      (by linarith : e < 1) (by linarith : e < r) g
    apply fromFirst hj (by decide)
    exact hit hP hs (fun _ ht hT => from_level b (rise hL.1 (by linarith) he ht hT))
  · obtain ⟨j,hj,hs⟩ := planarFour (H 0).1 (H 0).2 (H 1).1 (H 1).2 he he4
    apply fromSecond (by omega : j+3 < 7)
    exact hit hP hs (fun _ ht hT => from_level b (fall hL.2 (by linarith) he ht hT))

theorem cubeEight : CanLight cube 8 := by
  have closedCube : IsClosed cube := by
    have heq : cube = ⋂ i : Fin 3, {p : Space | 0 ≤ p i ∧ p i ≤ 1} := by
      ext p
      simp [cube]
    rw [heq]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  have hP : prism ⊆ cube := fun _ h => h.1
  refine ⟨fun i => lamps 4 (1/8) (1/4) (-(1/4)) i.val,
    fun _ => lamps_ne _ _ _ (by norm_num) (by norm_num), ?_⟩
  intro p hp
  have H := closedCube.frontier_subset hp
  obtain ⟨j,hj,hs⟩ := planarFour (H 0).1 (H 0).2 (H 1).1 (H 1).2
    (by norm_num : (0:ℝ) < 1/8) (by norm_num)
  by_cases hz : p 2 ≤ 1/2
  · apply fromFirst hj (by decide)
    exact hit hP hs (fun _ ht hT => rise (H 2).1 (by linarith) (by norm_num) ht hT)
  · apply fromSecond (by omega : j+4 < 8)
    exact hit hP hs (fun _ ht hT => fall (H 2).2 (by linarith) (by norm_num) ht hT)

end PrismIllumination
