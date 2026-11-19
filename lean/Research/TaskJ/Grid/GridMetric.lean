import Research.TaskJ.Grid.Challenge
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

namespace Grid

open Challenge

def axisRadius (d x : ℕ) : ℤ := |2 * (x : ℤ) + 1 - d|

def radius (ds x : List ℕ) : ℤ := (List.zipWith axisRadius ds x).sum

def defect (ds x y : List ℕ) : ℤ :=
  radius ds x + radius ds y - 2 * (manhattan x y : ℤ)

def edgeLoss (ds : List ℕ) : List Point → ℤ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => defect ds x y + edgeLoss ds (y :: xs)

@[simp] theorem radius_cons (d x : ℕ) (ds xs : List ℕ) :
    radius (d :: ds) (x :: xs) = axisRadius d x + radius ds xs := rfl

@[simp] theorem manhattan_cons (x y : ℕ) (xs ys : Point) :
    manhattan (x :: xs) (y :: ys) = Nat.dist x y + manhattan xs ys := rfl

theorem axis_dist_le (d x y : ℕ) :
    2 * (Nat.dist x y : ℤ) ≤ axisRadius d x + axisRadius d y := by
  unfold axisRadius Nat.dist
  simp only [abs_eq_max_neg, Nat.cast_add]
  omega

theorem defect_cons (d x y : ℕ) (ds xs ys : List ℕ) :
    defect (d :: ds) (x :: xs) (y :: ys) =
      (axisRadius d x + axisRadius d y - 2 * (Nat.dist x y : ℤ)) + defect ds xs ys := by
  simp only [defect, radius_cons, manhattan_cons, Nat.cast_add]
  ring

theorem defect_nonneg {ds x y : List ℕ} (hx : x.length = ds.length)
    (hy : y.length = ds.length) : 0 ≤ defect ds x y := by
  induction ds generalizing x y with
  | nil => simp_all [defect, radius, manhattan]
  | cons d ds ih =>
    cases x <;> cases y <;> simp_all only [List.length_cons, List.length_nil, Nat.succ.injEq,
      Nat.zero_ne_add_one]
    rename_i x xs y ys
    rw [defect_cons]
    have := axis_dist_le d x y
    grind

theorem identity (ds : List ℕ) (x : Point) (xs : List Point) :
    2 * (pathLength (x :: xs) : ℤ) + radius ds x + radius ds (xs.getLastD x) +
      edgeLoss ds (x :: xs) = 2 * ((x :: xs).map (radius ds)).sum := by
  induction xs generalizing x with
  | nil => simp [pathLength, edgeLoss]
           ring
  | cons y ys ih =>
    have h := ih y
    simp only [pathLength, edgeLoss, List.map_cons, List.sum_cons, Nat.cast_add,
      List.getLastD_cons] at *
    unfold defect
    linarith

theorem length_vertices (ds : List ℕ) : (vertices ds).length = ds.prod := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp [vertices, List.length_flatMap, ih]

theorem length_of_mem_vertices {ds x : List ℕ} (h : x ∈ vertices ds) :
    x.length = ds.length := by
  induction ds generalizing x with
  | nil => simpa [vertices] using h
  | cons d ds ih =>
    simp only [vertices, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨a, _, b, hb, rfl⟩ := h
    simp [ih hb]

theorem edgeLoss_nonneg {ds : List ℕ} {p : List Point}
    (h : ∀ x ∈ p, x.length = ds.length) : 0 ≤ edgeLoss ds p := by
  match p with
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys =>
    have ht : ∀ z ∈ y :: ys, z.length = ds.length :=
      fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact add_nonneg (defect_nonneg (h x (by simp)) (ht y (by simp))) (edgeLoss_nonneg ht)

end Grid
