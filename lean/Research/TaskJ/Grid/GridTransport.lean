import Research.TaskJ.Grid.Challenge
import Mathlib.Data.List.Perm.Basic

namespace Grid.Transport

open Challenge

/-- A coordinate map usable for transferring a traversal to another box. -/
structure BoxMap (ds es : List ℕ) where
  point : Point → Point
  covers : ((vertices ds).map point).Perm (vertices es)
  dist_eq : ∀ x ∈ vertices ds, ∀ y ∈ vertices ds, manhattan (point x) (point y) = manhattan x y

theorem mem_cons_box {d : ℕ} {ds : List ℕ} {p : Point} :
    p ∈ vertices (d :: ds) ↔ ∃ x < d, ∃ xs ∈ vertices ds, p = x :: xs := by
  simp [vertices, eq_comm]

namespace BoxMap

variable {a b c : List ℕ}

theorem mem (f : BoxMap a b) {x : Point} (hx : x ∈ vertices a) : f.point x ∈ vertices b :=
  f.covers.mem_iff.mp (List.mem_map.mpr ⟨x, hx, rfl⟩)

def identity (ds : List ℕ) : BoxMap ds ds where
  point := id
  covers := by simp
  dist_eq := by simp

def trans (f : BoxMap a b) (g : BoxMap b c) : BoxMap a c where
  point := g.point ∘ f.point
  covers := by simpa [List.map_map] using (f.covers.map g.point).trans g.covers
  dist_eq x hx y hy := (g.dist_eq _ (f.mem hx) _ (f.mem hy)).trans (f.dist_eq _ hx _ hy)

theorem order (f : BoxMap a b) {p : List Point} (hp : Order a p) : Order b (p.map f.point) :=
  (hp.map f.point).trans f.covers

theorem length_eq (f : BoxMap a b) (p : List Point) (hp : ∀ x ∈ p, x ∈ vertices a) :
    pathLength (p.map f.point) = pathLength p := by
  match p with
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs =>
    simp only [List.map_cons, pathLength]
    rw [f.dist_eq _ (hp x (by simp)) _ (hp y (by simp))]
    exact congrArg (manhattan x y + ·) (f.length_eq (y :: xs) (fun z hz => hp z (List.mem_cons_of_mem x hz)))

theorem transport_order (f : BoxMap a b) {p : List Point} (hp : Order a p) :
    ∃ q, Order b q ∧ pathLength q = pathLength p :=
  ⟨_, f.order hp, f.length_eq p (fun _ hx => hp.mem_iff.mp hx)⟩

private def onTail (f : Point → Point) : Point → Point
  | [] => []
  | x :: xs => x :: f xs

def cons (d : ℕ) (f : BoxMap a b) : BoxMap (d :: a) (d :: b) where
  point := onTail f.point
  covers := by
    simp only [vertices, List.map_flatMap, List.map_map]
    apply List.Perm.flatMap_left
    intro x _
    simpa [List.map_map, Function.comp_def, onTail] using f.covers.map (x :: ·)
  dist_eq x hx y hy := by
    rcases mem_cons_box.mp hx with ⟨i, _, u, hu, rfl⟩
    rcases mem_cons_box.mp hy with ⟨j, _, v, hv, rfl⟩
    change Nat.dist i j + manhattan (f.point u) (f.point v) = Nat.dist i j + manhattan u v
    rw [f.dist_eq _ hu _ hv]

private def switch : Point → Point
  | x :: y :: xs => y :: x :: xs
  | xs => xs

private theorem interchange {α β γ : Type*} (xs : List α) (ys : List β) (f : α → β → List γ) :
    (xs.flatMap fun x => ys.flatMap (f x)).Perm (ys.flatMap fun y => xs.flatMap (f · y)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left _).trans (List.flatMap_append_perm ys _ _)

def swap (i j : ℕ) (ds : List ℕ) : BoxMap (i :: j :: ds) (j :: i :: ds) where
  point := switch
  covers := by
    simpa [vertices, List.map_map, List.map_flatMap, Function.comp_def, switch] using
      interchange (List.range i) (List.range j) (fun x y => (vertices ds).map (fun p => y :: x :: p))
  dist_eq x hx y hy := by
    rcases mem_cons_box.mp hx with ⟨x, _, xs, hxs, rfl⟩
    rcases mem_cons_box.mp hxs with ⟨u, _, us, _, rfl⟩
    rcases mem_cons_box.mp hy with ⟨y, _, ys, hys, rfl⟩
    rcases mem_cons_box.mp hys with ⟨v, _, vs, _, rfl⟩
    simp [switch, manhattan, Nat.add_left_comm]

def addOne (ds : List ℕ) : BoxMap ds (1 :: ds) where
  point := (0 :: ·)
  covers := by simp [vertices, List.range_succ]
  dist_eq := by simp [manhattan]

def eraseOne (ds : List ℕ) : BoxMap (1 :: ds) ds where
  point := List.tail
  covers := by simp [vertices, List.range_succ, List.map_map, Function.comp_def]
  dist_eq x hx y hy := by
    rcases mem_cons_box.mp hx with ⟨u, hu, x, _, rfl⟩
    rcases mem_cons_box.mp hy with ⟨v, hv, y, _, rfl⟩
    have : u = v := by omega
    simp [this, manhattan]

end BoxMap

theorem of_perm {a b : List ℕ} (h : a.Perm b) : Nonempty (BoxMap a b) := by
  induction h with
  | nil => exact ⟨BoxMap.identity _⟩
  | cons d _ ih => exact ih.map (BoxMap.cons d)
  | swap x y l => exact ⟨BoxMap.swap _ _ l⟩
  | trans _ _ ih ik =>
    obtain ⟨f⟩ := ih
    obtain ⟨g⟩ := ik
    exact ⟨f.trans g⟩

end Grid.Transport
