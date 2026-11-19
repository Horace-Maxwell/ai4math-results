import Research.TaskJ.Grid.GridMetric

namespace Grid

open Challenge

/-- The coordinate contribution to the doubled radial mass of a box. -/
def massTerm (N d : ℕ) : ℤ := (N / d : ℕ) * ((d ^ 2 / 2 : ℕ) : ℤ)

def massAt (N : ℕ) (ds : List ℕ) : ℤ := (ds.map (massTerm N)).sum

def mass (ds : List ℕ) : ℤ := massAt ds.prod ds

theorem axisRadius_sum (d : ℕ) :
    ((List.range d).map (axisRadius d)).sum = (d ^ 2 / 2 : ℕ) := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one => decide
  | more d ih _ =>
    have hmid : ∀ x : ℕ, axisRadius (d+2) (x+1) = axisRadius d x := by
      intro x
      unfold axisRadius
      congr 1
      push_cast
      ring
    have hend : axisRadius (d+2) (d+1) = (d : ℤ)+1 := by
      unfold axisRadius
      push_cast
      rw [abs_of_nonneg] <;> omega
    have hbeg : axisRadius (d+2) 0 = (d : ℤ)+1 := by
      unfold axisRadius
      push_cast
      rw [abs_of_nonpos] <;> omega
    have hsq : (d+2)^2 = d^2 + 2*(2*d+2) := by ring
    rw [List.range_succ, List.range_succ_eq_map, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_map, Function.comp_def, List.sum_cons, List.map_nil,
      List.sum_nil, add_zero]
    rw [hbeg, hend]
    simp only [hmid, ih, hsq]
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
    push_cast
    ring

private theorem blockSum {α : Type} (l : List α) (a : ℤ) (f : α → ℤ) :
    (l.map (fun x => a + f x)).sum = (l.length : ℤ) * a + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add_one, ih]
    ring

private theorem layerSum (d : ℕ) (ds : List ℕ) (xs : List ℕ) :
    (((xs.flatMap fun x => (vertices ds).map (x :: ·)).map (radius (d::ds))).sum) =
    (ds.prod : ℤ) * (xs.map (axisRadius d)).sum +
      (xs.length : ℤ) * ((vertices ds).map (radius ds)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_map, Function.comp_def,
      radius_cons, List.sum_append, ih, blockSum, length_vertices, List.map_cons,
      List.sum_cons, List.length_cons, Nat.cast_add_one]
    ring

private theorem massAt_mul (c n : ℕ) (ds : List ℕ) (h : ∀ d ∈ ds, d ∣ n) :
    massAt (c*n) ds = (c : ℤ)*massAt n ds := by
  induction ds with
  | nil => simp [massAt]
  | cons d ds ih =>
    change massTerm (c*n) d + massAt (c*n) ds = _ * (massTerm n d + massAt n ds)
    rw [ih (fun a ha => h a (by simp [ha]))]
    simp only [massTerm, Nat.mul_div_assoc c (h d (by simp)), Nat.cast_mul]
    ring

theorem mass_cons {d : ℕ} (hd : 0 < d) (ds : List ℕ) :
    mass (d :: ds) = (ds.prod : ℤ) * ((d ^ 2 / 2 : ℕ) : ℤ) + d * mass ds := by
  change massTerm (d*ds.prod) d + massAt (d*ds.prod) ds = _
  rw [massAt_mul d ds.prod ds (fun a ha => List.dvd_prod ha)]
  simp [massTerm, Nat.mul_div_cancel_left _ hd, mass]

theorem vertex_radius_sum {ds : List ℕ} (h : PositiveSides ds) :
    ((vertices ds).map (radius ds)).sum = mass ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [vertices, layerSum, axisRadius_sum, List.length_range, mass_cons (h d (by simp)),
      ih (fun a ha => h a (by simp [ha]))]

theorem order_radius_sum {ds : List ℕ} {p : List Point} (h : PositiveSides ds)
    (hp : Order ds p) : (p.map (radius ds)).sum = mass ds :=
  (hp.map (radius ds)).sum_eq.trans (vertex_radius_sum h)

end Grid
