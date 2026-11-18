import Research.TaskH.Fan.PathOperations

/-! One-edge and two-edge triangle arcs only become >=2 after a positive tail. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem one_two_prefixes_append (G : SimpleGraph V) {x p y : V}
    (s t : G.Walk x p) (r : G.Walk p y) (hs : s.IsPath) (ht : t.IsPath)
    (hr : r.IsPath) (hl : s.length = 1) (hl' : t.length = 2) (hrl : 1 ≤ r.length)
    (hsi : ∀ w, w ∈ s.support → w ∈ r.support → w = p)
    (hti : ∀ w, w ∈ t.support → w ∈ r.support → w = p) : HasTwoPaths G x y := by
  refine ⟨s.append r, t.append r,
    isPath_append_of_support_intersection s r hs hr hsi,
    isPath_append_of_support_intersection t r ht hr hti, ?_, ?_, Or.inl ?_⟩
  · simp only [Walk.length_append, hl]
    omega
  · simp only [Walk.length_append, hl']
    omega
  · simp only [Walk.length_append, hl, hl']
    omega

theorem triangle_positive_tail (G : SimpleGraph V) (x p q y : V)
    (hxp : x ≠ p) (hxq : x ≠ q) (hpq : p ≠ q)
    (exp : G.Adj x p) (epq : G.Adj p q) (eqx : G.Adj q x)
    (r : G.Walk p y) (hr : r.IsPath) (hrl : 1 ≤ r.length)
    (havoid : ∀ w, w ∈ r.support → w ≠ p → w ∉ ({x, p, q} : Set V)) :
    HasTwoPaths G x y := by
  classical
  let s : G.Walk x p := Walk.cons exp Walk.nil
  let t : G.Walk x p := Walk.cons eqx.symm (Walk.cons epq.symm Walk.nil)
  have hs : s.IsPath := by
    apply Walk.IsPath.mk'
    simp [s, Walk.support_cons, Walk.support_nil, hxp]
  have ht : t.IsPath := by
    apply Walk.IsPath.mk'
    simp [t, Walk.support_cons, Walk.support_nil, hxp, hxq, hpq.symm]
  have hmems : ∀ w ∈ s.support, w ∈ ({x, p, q} : Set V) := by
    intro w hw
    simp only [s, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> simp
  have hmemt : ∀ w ∈ t.support, w ∈ ({x, p, q} : Set V) := by
    intro w hw
    simp only [t, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp
  apply one_two_prefixes_append G s t r hs ht hr (by simp [s]) (by simp [t]) hrl
  · intro w hws hwr
    by_contra hwp
    exact havoid w hwr hwp (hmems w hws)
  · intro w hwt hwr
    by_contra hwp
    exact havoid w hwr hwp (hmemt w hwt)

#print axioms one_two_prefixes_append
#print axioms triangle_positive_tail
end TaskH.Fan
