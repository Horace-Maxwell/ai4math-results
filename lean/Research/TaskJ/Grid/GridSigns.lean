import Research.TaskJ.Grid.GridMetric

namespace Grid

open Challenge

def sign (d x : ℕ) : Bool := decide (d ≤ 2*x+1)

def signs : List ℕ → Point → List Bool
  | d :: ds, x :: xs => if d % 2 = 0 then sign d x :: signs ds xs else signs ds xs
  | _, _ => []

def flip (s : List Bool) : List Bool := s.map Bool.not

@[simp] theorem flip_flip (s : List Bool) : flip (flip s) = s := by
  simp [flip, List.map_map, Function.comp_def]

@[simp] theorem flip_cons (b : Bool) (bs : List Bool) : flip (b :: bs) = (!b) :: flip bs := rfl

theorem count_cons (d : ℕ) (ds : List ℕ) : evenCount (d :: ds) =
    if d % 2 = 0 then evenCount ds + 1 else evenCount ds := by
  by_cases hd : d % 2 = 0 <;> simp [evenCount, hd]

/-- Coordinate sign on an even axis that failed to change costs at least one distance unit. -/
theorem axis_same (d x y : ℕ) (he : d % 2 = 0) (hs : sign d x = sign d y) :
    2 ≤ axisRadius d x + axisRadius d y - 2*(Nat.dist x y : ℤ) := by
  simp only [sign, decide_eq_decide] at hs
  simp only [axisRadius, Nat.dist, Nat.cast_add, abs_eq_max_neg]
  omega

theorem defect_of_signs {ds x y : List ℕ} (hx : x.length = ds.length)
    (hy : y.length = ds.length) (hn : signs ds x ≠ flip (signs ds y)) :
    2 ≤ defect ds x y := by
  induction ds generalizing x y with
  | nil => simp [signs, flip] at hn
  | cons d ds ih =>
    cases x <;> cases y <;> simp_all only [List.length_nil, List.length_cons,
      Nat.succ.injEq, Nat.zero_ne_add_one]
    rename_i x xs y ys
    rw [defect_cons]
    by_cases hd : d%2=0
    · simp only [signs, hd, ite_true, flip_cons] at hn
      by_cases he : sign d x = !(sign d y)
      · have htail := ih hx hy (fun h => hn (by rw [he,h]))
        have := axis_dist_le d x y
        omega
      · have hs : sign d x = sign d y := by cases h : sign d y <;> simp_all
        have := axis_same d x y hd hs
        have := defect_nonneg hx hy
        omega
    · simp only [signs, hd, ite_false] at hn
      have := ih hx hy hn
      have := axis_dist_le d x y
      omega

theorem radius_evenCount {ds x : List ℕ} (hx : x.length = ds.length) :
    (evenCount ds : ℤ) ≤ radius ds x := by
  induction ds generalizing x with
  | nil => cases x <;> simp_all [evenCount, radius]
  | cons d ds ih =>
    cases x with
    | nil => simp at hx
    | cons x xs =>
      have ht : xs.length = ds.length := by simpa using hx
      have := ih ht
      rw [count_cons, radius_cons]
      by_cases h : d%2=0
      · simp only [h, ite_true, Nat.cast_add_one, axisRadius, abs_eq_max_neg]
        omega
      · simp only [h, ite_false]
        exact le_add_of_nonneg_of_le (abs_nonneg _) this

theorem realizes_signs {ds : List ℕ} (h : PositiveSides ds) {s : List Bool}
    (hs : s.length = evenCount ds) :
    ∃ x ∈ vertices ds, signs ds x = s := by
  induction ds generalizing s with
  | nil =>
    have : s = [] := by simpa [evenCount] using hs
    subst s
    exact ⟨[], by simp [vertices], rfl⟩
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : PositiveSides ds := fun a ha => h a (by simp [ha])
    rw [count_cons] at hs
    by_cases he : d%2=0
    · simp only [he, ite_true] at hs
      cases s with
      | nil => simp at hs
      | cons b bs =>
        have hb : bs.length = evenCount ds := by simpa using hs
        obtain ⟨x,hx,hxs⟩ := ih ht hb
        have make (a : ℕ) (ha : a < d) (hsg : sign d a = b) :
            ∃ y ∈ vertices (d :: ds), signs (d :: ds) y = b :: bs := by
          refine ⟨a :: x, ?_, by simp [signs, he, hsg, hxs]⟩
          exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,List.mem_map.mpr ⟨x,hx,rfl⟩⟩
        cases b with
        | false => exact make 0 hd (by simp [sign]; omega)
        | true => exact make (d-1) (by omega) (by simp [sign]; omega)
    · simp only [he, ite_false] at hs
      obtain ⟨x,hx,hxs⟩ := ih ht hs
      refine ⟨0 :: x, ?_, by simp [signs, he, hxs]⟩
      exact List.mem_flatMap.mpr ⟨0,List.mem_range.mpr hd,List.mem_map.mpr ⟨x,hx,rfl⟩⟩

end Grid
