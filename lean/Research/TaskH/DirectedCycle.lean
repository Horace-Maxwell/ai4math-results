import Research.TaskH.Recolor

set_option autoImplicit false

universe u v

namespace TaskH

open SimpleGraph

variable {V : Type u} {α : Type v} {G : SimpleGraph V}

def Follows {x y : V} (p : G.Walk x y) (c : V → α) (σ : Equiv.Perm α) : Prop :=
  ∀ d ∈ p.darts, c d.snd = σ (c d.fst)

theorem follows_nil (x : V) (c : V → α) (σ : Equiv.Perm α) :
    Follows (.nil : G.Walk x x) c σ := by
  simp [Follows]

theorem follows_cons {x y z : V} (hxy : G.Adj x y) (p : G.Walk y z)
    (c : V → α) (σ : Equiv.Perm α) :
    Follows (.cons hxy p) c σ ↔ c y = σ (c x) ∧ Follows p c σ := by
  simp [Follows, Walk.darts_cons]

theorem follows_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z)
    (c : V → α) (σ : Equiv.Perm α) :
    Follows (p.append q) c σ ↔ Follows p c σ ∧ Follows q c σ := by
  constructor
  · intro hf
    constructor
    · intro d hd
      apply hf d
      rw [Walk.darts_append]
      exact List.mem_append.mpr (Or.inl hd)
    · intro d hd
      apply hf d
      rw [Walk.darts_append]
      exact List.mem_append.mpr (Or.inr hd)
  · rintro ⟨hp, hq⟩ d hd
    rw [Walk.darts_append, List.mem_append] at hd
    exact hd.elim (hp d) (hq d)

theorem follows_bypass [DecidableEq V] {x y : V} (p : G.Walk x y) (c : V → α)
    (σ : Equiv.Perm α) (hp : Follows p c σ) : Follows p.bypass c σ := by
  intro d hd
  exact hp d (p.darts_bypass_subset_darts hd)

theorem reach_exists_follows_walk (c : V → α) (σ : Equiv.Perm α) {x y : V}
    (h : Relation.ReflTransGen (ColorStep G c σ) x y) :
    ∃ p : G.Walk x y, Follows p c σ := by
  induction h with
  | refl => exact ⟨.nil, follows_nil _ c σ⟩
  | @tail y z _ hyz ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.append (.cons hyz.1 .nil), (follows_append _ _ c σ).mpr ⟨hp, ?_⟩⟩
    exact (follows_cons _ _ c σ).mpr ⟨hyz.2, follows_nil _ c σ⟩

theorem isPath_follows_edge_at_start {x y z : V} (p : G.Walk x y)
    (hp : p.IsPath) (c : V → α) (σ : Equiv.Perm α) (hf : Follows p c σ)
    (he : s(x, z) ∈ p.edges) : c z = σ (c x) := by
  have hz := hp.eq_snd_of_mem_edges he
  rw [hz]
  cases p with
  | nil => simp at he
  | cons h p => simpa [Walk.snd] using ((follows_cons h p c σ).mp hf).1

/-- A directed closed walk has a genuine simple cycle through its base point
when the color permutation has no two-step return at that color. -/
theorem follows_closed_exists_cycle {x : V} (p : G.Walk x x) (hp : p ≠ .nil)
    (c : V → α) (σ : Equiv.Perm α) (hf : Follows p c σ)
    (hchange : σ (σ (c x)) ≠ c x) :
    ∃ q : G.Walk x x, q.IsCycle ∧ Follows q c σ := by
  classical
  cases p with
  | nil => exact (hp rfl).elim
  | @cons _ y _ hxy r =>
    have hparts := (follows_cons hxy r c σ).mp hf
    have hr := follows_bypass r c σ hparts.2
    have hn : s(x, y) ∉ r.bypass.edges := by
      intro he
      have he' : s(y, x) ∈ r.bypass.edges := by simpa only [Sym2.eq_swap] using he
      have hc := isPath_follows_edge_at_start r.bypass r.bypass_isPath c σ hr he'
      apply hchange
      rw [← hparts.1, ← hc]
    refine ⟨.cons hxy r.bypass, ?_, (follows_cons hxy r.bypass c σ).mpr ⟨hparts.1, hr⟩⟩
    exact (Walk.cons_isCycle_iff ..).mpr ⟨r.bypass_isPath, hn⟩

#print axioms reach_exists_follows_walk
#print axioms follows_closed_exists_cycle

end TaskH
