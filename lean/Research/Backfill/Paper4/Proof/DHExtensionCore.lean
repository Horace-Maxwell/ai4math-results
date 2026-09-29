import Research.Backfill.Paper4.Challenge

/-! Metric transport for the complete pendant/twin extension proof.
Weak edge maps may collapse an edge to one vertex; no ordinary graph-homomorphism
assumption is imposed on those maps. Every natural-distance comparison retains
source reachability. No finiteness assumptions are needed by this core.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.DHExtensionCore
open BackfillPaper4 SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Map a walk through a map which can collapse adjacent endpoints.
Collapsed steps are omitted, so the resulting length cannot increase. -/
theorem weak_walk (f : V → W)
    (hedge : ∀ {x y : V}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {u v : V} (p : G.Walk u v) :
    ∃ q : H.Walk (f u) (f v), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, by simp⟩
  | @cons u w v huw p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hedge huw with heq | hadj
    · rw [heq]
      refine ⟨q, ?_⟩
      simpa only [Walk.length_cons] using hq.trans (Nat.le_succ p.length)
    · refine ⟨Walk.cons hadj q, ?_⟩
      simpa only [Walk.length_cons] using Nat.succ_le_succ hq

theorem weak_reachable (f : V → W)
    (hedge : ∀ {x y : V}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {u v : V} (hr : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := hr
  obtain ⟨q, _⟩ := weak_walk f hedge p
  exact ⟨q⟩

/-- Reachability is essential here: graph distance on an unreachable pair is zero. -/
theorem weak_dist_le (f : V → W)
    (hedge : ∀ {x y : V}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {u v : V} (hr : G.Reachable u v) : H.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := weak_walk f hedge p
  exact ((SimpleGraph.dist_le q).trans hq).trans_eq hp

theorem weak_connected (f : V → W)
    (hedge : ∀ {x y : V}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    (hsurj : Function.Surjective f) (hc : G.Connected) : H.Connected := by
  have : Nonempty W := hc.nonempty.map f
  refine ⟨?_⟩
  intro x y
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  exact weak_reachable f hedge (hc u v)

theorem hom_dist_le (f : G →g H) {u v : V} (hr : G.Reachable u v) :
    H.dist (f u) (f v) ≤ G.dist u v :=
  weak_dist_le f (fun h => Or.inr (f.map_adj h)) hr

/-- The same two-way walk transport argument as the accepted
`GridExamples.iso_dist_eq`; kept here to avoid importing its concrete graph certificates. -/
theorem iso_dist_eq (e : G ≃g H) (hc : G.Connected) (u v : V) :
    H.dist (e u) (e v) = G.dist u v := by
  have hcH : H.Connected := e.connected_iff.mp hc
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
    calc
      H.dist (e u) (e v) ≤ (p.map e.toHom).length := SimpleGraph.dist_le _
      _ = p.length := SimpleGraph.Walk.length_map _ _
      _ = G.dist u v := hp
  · obtain ⟨p, hp⟩ := hcH.exists_walk_length_eq_dist (e u) (e v)
    have hle := SimpleGraph.dist_le (p.map e.symm.toHom)
    have hle' : G.dist u v ≤ p.length := by
      change G.dist (e.symm (e u)) (e.symm (e v)) ≤
        (p.map e.symm.toHom).length at hle
      simpa only [SimpleGraph.Walk.length_map, RelIso.symm_apply_apply] using hle
    exact hle'.trans_eq hp

/-- A weak edge retraction onto an induced subgraph makes that subgraph connected
and preserves every distance between its vertices, including coincident endpoints. -/
theorem induce_retract (G : SimpleGraph V) (s : Set V) (r : V → s)
    (hc : G.Connected) (hfix : ∀ x : s, r x.val = x)
    (hedge : ∀ {x y : V}, G.Adj x y →
      r x = r y ∨ (G.induce s).Adj (r x) (r y)) :
    (G.induce s).Connected ∧
      ∀ u v : s, (G.induce s).dist u v = G.dist u.val v.val := by
  have hsurj : Function.Surjective r := fun x => ⟨x.val, hfix x⟩
  have hs : (G.induce s).Connected := weak_connected r hedge hsurj hc
  refine ⟨hs, ?_⟩
  intro u v
  apply le_antisymm
  · have h := weak_dist_le r hedge (hc u.val v.val)
    rw [hfix u, hfix v] at h
    exact h
  · let inclusion : G.induce s →g G := (SimpleGraph.Embedding.induce (G := G) s).toHom
    exact hom_dist_le inclusion (hs u v)

/-- Any connected graph embedded as an induced subgraph of a DH graph has the
ambient distances. This avoids hand-written nested-subtype isomorphisms. -/
theorem embedding_dist_eq (hH : Challenge.IsDistanceHereditary H)
    (e : G ↪g H) (hc : G.Connected) (u v : V) :
    G.dist u v = H.dist (e u) (e v) := by
  let ei : G ≃g H.induce (Set.range e) := e.isoInduceRange
  have hci : (H.induce (Set.range e)).Connected := ei.connected_iff.mp hc
  have hiso := iso_dist_eq ei hc u v
  have hdh := hH.2 (Set.range e) hci (ei u) (ei v)
  change (H.induce (Set.range e)).dist (ei u) (ei v) = H.dist (e u) (e v) at hdh
  exact hiso.symm.trans hdh

#print axioms iso_dist_eq
#print axioms induce_retract
#print axioms embedding_dist_eq
end CodexPaper4.DHExtensionCore
