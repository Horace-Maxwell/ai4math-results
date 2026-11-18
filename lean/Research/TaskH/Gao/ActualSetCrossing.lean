import Research.TaskH.Fan.Challenge

/-! A boundary edge is derived from an actual walk crossing a genuine vertex set. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem walk_crosses_vertex_set (G : SimpleGraph V) (S : Set V)
    {a b : V} (p : G.Walk a b) : a ∈ S → b ∉ S →
    ∃ u ∈ S, ∃ v, v ∉ S ∧ G.Adj u v := by
  classical
  induction p with
  | nil =>
    intro ha hb
    exact False.elim (hb ha)
  | @cons a c b e p ih =>
    intro ha hb
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, e⟩

theorem reachable_crosses_vertex_set (G : SimpleGraph V) (S : Set V)
    (a b : V) (ha : a ∈ S) (hb : b ∉ S) (hr : G.Reachable a b) :
    ∃ u ∈ S, ∃ v, v ∉ S ∧ G.Adj u v := by
  obtain ⟨p⟩ := hr
  exact walk_crosses_vertex_set G S p ha hb

#print axioms walk_crosses_vertex_set
#print axioms reachable_crosses_vertex_set
end TaskH.Gao
