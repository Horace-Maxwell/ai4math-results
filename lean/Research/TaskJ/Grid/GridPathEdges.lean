import Research.TaskJ.Grid.GridMetric
import Mathlib.Data.List.Chain

namespace Grid

variable {α β : Type*}

def pathEdges : List α → List (α × α)
  | [] => []
  | [_] => []
  | x :: y :: ys => (x,y) :: pathEdges (y::ys)

theorem pathEdges_cut (l : List α) (a : α) (r : List α) :
    pathEdges (l ++ a::r) = pathEdges (l ++ [a]) ++ pathEdges (a::r) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => cases r <;> rfl
    | cons c cs =>
      simpa only [List.cons_append, pathEdges, List.cons.injEq, true_and] using ih

theorem pathEdges_map (f : α → β) : ∀ l : List α,
    pathEdges (l.map f) = (pathEdges l).map (fun (x,y) => (f x,f y))
  | [] | [_] => rfl
  | x::y::l => by
      exact congrArg ((f x, f y)::·) (pathEdges_map f (y::l))

theorem edgeLoss_edges (ds : List ℕ) : ∀ l : List Challenge.Point,
    edgeLoss ds l = ((pathEdges l).map (fun (x,y) => defect ds x y)).sum
  | [] | [_] => rfl
  | x::y::l => by simp [pathEdges,edgeLoss,edgeLoss_edges ds (y::l)]

theorem chain_edges (R : α → α → Prop) : ∀ l : List α,
    l.IsChain R ↔ ∀ e ∈ pathEdges l, R e.1 e.2
  | [] | [_] => by simp [pathEdges]
  | a::b::bs => by simp [pathEdges, List.isChain_cons_cons, chain_edges R (b::bs)]

/-- The vertex has an incident edge satisfying the given condition along this ordering. -/
def Touches (R : α → α → Prop) (l : List α) (a : α) : Prop :=
  ∃ e ∈ pathEdges l, R e.1 e.2 ∧ (e.1 = a ∨ e.2 = a)

theorem all_touch_of_chain (R : α → α → Prop) (l : List α) (hl : 2 ≤ l.length)
    (h : l.IsChain R) : ∀ a ∈ l, Touches R l a := by
  induction l with
  | nil => simp at hl
  | cons x xs ih =>
    cases xs with
    | nil => simp at hl
    | cons y ys =>
      intro a ha
      have he := (List.isChain_cons_cons.mp h).1
      by_cases ax : a = x
      · exact ⟨(x,y), by simp [pathEdges], he, Or.inl ax.symm⟩
      by_cases ay : a = y
      · exact ⟨(x,y), by simp [pathEdges], he, Or.inr ay.symm⟩
      cases ys with
      | nil => simp_all
      | cons z zs =>
        obtain ⟨e, hmem, hr, hx⟩ := ih (by simp) h.tail a (by simpa [List.mem_cons, ax] using ha)
        exact ⟨e, List.mem_cons_of_mem _ hmem, hr, hx⟩

/-- Every edge in the ordering has an actual adjacent decomposition. -/
theorem split_at_edge : ∀ (l : List α) (x y : α), (x,y) ∈ pathEdges l →
    ∃ pre post, l = pre ++ x :: y :: post
  | [], _, _, h | [_], _, _, h => by simp [pathEdges] at h
  | a::b::bs, x,y,h => by
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact ⟨[], bs,rfl⟩
      · obtain ⟨pre,post,hp⟩ := split_at_edge (b::bs) x y h
        exact ⟨a::pre,post,congrArg (a::·) hp⟩

theorem touch_after_splice (R : α → α → Prop) (pre post : List α) (x y u v : α)
    (hxu : R x u) (hvy : R v y) {a : α} (h : Touches R (pre ++ x::y::post) a) :
    Touches R (pre ++ x::u::v::y::post) a := by
  obtain ⟨e,he,hr,hinc⟩ := h
  rw [pathEdges_cut] at he
  change e ∈ pathEdges (pre ++ [x]) ++ (x,y)::pathEdges (y::post) at he
  unfold Touches
  rw [pathEdges_cut]
  change ∃ e ∈ pathEdges (pre ++ [x]) ++ (x,u)::(u,v)::(v,y)::pathEdges (y::post),
      R e.1 e.2 ∧ (e.1 = a ∨ e.2 = a)
  rcases List.mem_append.mp he with he | he
  · exact ⟨e,List.mem_append_left _ he,hr,hinc⟩
  rcases List.mem_cons.mp he with he | he
  · subst e
    rcases hinc with hx | hy
    · exact ⟨(x,u),by simp,hxu,Or.inl hx⟩
    · exact ⟨(v,y),by simp,hvy,Or.inr hy⟩
  · exact ⟨e,List.mem_append_right _ (by simp [he]),hr,hinc⟩

theorem edgeLoss_splice (ds : List ℕ) (pre post : List Challenge.Point) (x y u v : Challenge.Point)
    (hxy : defect ds x y = 0) (hxu : defect ds x u = 0) (huv : defect ds u v = 0)
    (hvy : defect ds v y = 0) :
    edgeLoss ds (pre ++ x::u::v::y::post) = edgeLoss ds (pre ++ x::y::post) := by
  rw [edgeLoss_edges, edgeLoss_edges, pathEdges_cut pre x (u::v::y::post), pathEdges_cut pre x (y::post)]
  simp only [pathEdges, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons, hxy, hxu, huv, hvy, zero_add]

end Grid
