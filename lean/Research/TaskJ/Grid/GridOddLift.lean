import Research.TaskJ.Grid.GridSheets
import Research.TaskJ.Grid.GridSymmetry
import Research.TaskJ.Grid.GridEndpoints

namespace Grid.OddLift

open Challenge Sheets

def level : Sheet → ℕ
  | .lo => 0
  | .mid => 1
  | .hi => 2

def put (z : Point × Sheet) : Point := level z.2 :: z.1
def grow (p : List Point) : List Point := (liftCycle p).map put

structure Cycle (ds : List ℕ) (R : Point → Point → Prop) (a b : Point) (p : List Point) : Prop where
  order : Order ds p
  size : 3 ≤ p.length
  first : p.head? = some a
  last : p.getLast? = some b
  closed : (p ++ [a]).IsChain R

private theorem layers (ds : List ℕ) {p : List Point} (hp : Order ds p) :
    (p.flatMap fun x => [(0::x),(1::x),(2::x)]).Perm (vertices (3::ds)) := by
  have h := List.map_append_flatMap_perm p (0::·) (fun x => [(1::x),(2::x)])
  have h' := List.map_append_flatMap_perm p (1::·) (fun x => [2::x])
  simp only [← List.map_eq_flatMap] at h'
  apply h.symm.trans
  apply (h'.symm.append_left _).trans
  simpa [vertices, List.range_succ] using ((hp.map (0::·)).append
    ((hp.map (1::·)).append (hp.map (2::·))))

theorem grow_order {ds : List ℕ} {p : List Point} (hp : Order ds p) (hl : 3 ≤ p.length) :
    Order (3::ds) (grow p) := by
  have hh := (liftCycle_perm p hl).map put
  apply hh.trans
  simpa [sheets, put, level, List.map_flatMap] using layers ds hp

theorem grow_cycle {ds : List ℕ} {R S : Point → Point → Prop} {a b : Point} {p : List Point}
    (h : Cycle ds R a b p)
    (step_ok : ∀ x y s t, R x y → Cross s t → S (level s :: x) (level t :: y)) :
    Cycle (3::ds) S (1::a) (1::b) (grow p) := by
  obtain ⟨hp,hl,hfst,hlast,hr⟩ := h
  cases p with
  | nil => simp at hl
  | cons v vs =>
    simp only [List.head?_cons, Option.some.injEq] at hfst
    subst v
    have ho := grow_order hp hl
    refine ⟨ho, ?_, ?_, ?_, ?_⟩
    · have ht := ho.length_eq
      rw [length_vertices, List.prod_cons] at ht
      have hb := hp.length_eq
      rw [length_vertices] at hb
      omega
    · simp [grow,liftCycle_first,put,level]
    · simp [grow, liftCycle_last _ hl, hlast, put, level]
    · have hh := liftCycle_chain a vs hl hr
      have hc := List.isChain_map_of_isChain put
        (R := fun z w : Point × Sheet => R z.1 w.1 ∧ Cross z.2 w.2) (S := S)
        (fun z w hw => step_ok z.1 w.1 z.2 w.2 hw.1 hw.2) hh
      simpa [grow, put, level] using hc

theorem cross_defect (s t : Sheet) (h : Cross s t) :
    axisRadius 3 (level s) + axisRadius 3 (level t) -
      2*(Nat.dist (level s) (level t) : ℤ) = 0 := by
  cases s <;> cases t <;> first | decide | simp [Cross] at h

theorem defect_grow (ds : List ℕ) (x y : Point) (s t : Sheet) (h : Cross s t) :
    defect (3::ds) (level s :: x) (level t :: y) = defect ds x y := by
  rw [defect_cons, cross_defect s t h, zero_add]

theorem middle_radius (ds : List ℕ) (x : Point) : radius (3::ds) (1::x) = radius ds x := by
  rw [radius_cons]
  exact zero_add _

theorem loss_of_chain {ds : List ℕ} {p : List Point}
    (h : p.IsChain (fun x y => defect ds x y = 0)) : edgeLoss ds p = 0 := by
  match p with
  | [] | [_] => rfl
  | x::y::ys =>
    obtain ⟨h₁,h₂⟩ := List.isChain_cons_cons.mp h
    rw [edgeLoss,h₁,loss_of_chain h₂,zero_add]

theorem open_clean {ds : List ℕ} {R : Point → Point → Prop} {a b : Point} {p : List Point}
    (h : Cycle ds R a b p) (hr : ∀ x y, R x y → defect ds x y = 0) :
    edgeLoss ds p = 0 ∧ ∀ x ∈ p, Touches (fun u v => defect ds u v = 0) p x := by
  have hc := h.closed.left_of_append.imp hr
  exact ⟨loss_of_chain hc, all_touch_of_chain _ _ (by have := h.size; omega) hc⟩

end Grid.OddLift
