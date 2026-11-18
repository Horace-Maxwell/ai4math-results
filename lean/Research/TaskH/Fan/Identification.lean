import Research.TaskH.Fan.PathOperations

/-!
One actual fresh-root identification graph, its exact no-degree-loss transport,
and a real spoke lift from an exterior induced path. This does not yet extract
an exterior tail from an arbitrary simple walk in the identification graph.
-/
set_option autoImplicit false

universe u

namespace TaskH.Fan

open SimpleGraph

variable {V : Type u}

/-- None is the sole fresh root; every outside vertex remains separately tagged. -/
abbrev IdentificationVertex (S : Set V) := Option {a : V // a ∉ S}

/-- The actual simple quotient adjacency, with no edge at the fresh root itself. -/
def identificationAdj (G : SimpleGraph V) (S : Set V) :
    IdentificationVertex S → IdentificationVertex S → Prop
  | none, none => False
  | none, some b => ∃ a ∈ S, G.Adj a b.1
  | some a, none => ∃ b ∈ S, G.Adj a.1 b
  | some a, some b => G.Adj a.1 b.1

/-- Identifying S means existential real boundary adjacency, never a free root edge. -/
def identificationGraph (G : SimpleGraph V) (S : Set V) :
    SimpleGraph (IdentificationVertex S) where
  Adj := identificationAdj G S
  symm.symm a b hab := by
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hab
      | some b =>
        rcases hab with ⟨s, hs, hsb⟩
        exact ⟨s, hs, hsb.symm⟩
    | some a =>
      cases b with
      | none =>
        rcases hab with ⟨s, hs, has⟩
        exact ⟨s, hs, has.symm⟩
      | some b => exact G.adj_symm hab
  loopless.irrefl a := by
    cases a with
    | none => exact fun h => h
    | some a => exact G.irrefl

@[simp]
theorem identification_adj_none_some (G : SimpleGraph V) (S : Set V)
    (b : {a : V // a ∉ S}) :
    (identificationGraph G S).Adj none (some b) ↔ ∃ a ∈ S, G.Adj a b.1 :=
  Iff.rfl

@[simp]
theorem identification_adj_some_none (G : SimpleGraph V) (S : Set V)
    (a : {b : V // b ∉ S}) :
    (identificationGraph G S).Adj (some a) none ↔ ∃ b ∈ S, G.Adj a.1 b :=
  Iff.rfl

@[simp]
theorem identification_adj_some_some (G : SimpleGraph V) (S : Set V)
    (a b : {v : V // v ∉ S}) :
    (identificationGraph G S).Adj (some a) (some b) ↔ G.Adj a.1 b.1 :=
  Iff.rfl

/-- The vertex identification is not claimed to be a graph homomorphism. -/
noncomputable def identificationMap (S : Set V) (a : V) : IdentificationVertex S := by
  classical
  exact if ha : a ∈ S then none else some ⟨a, ha⟩

/-- With at most one actual S-neighbor, a retained vertex loses no degree at all. -/
theorem identification_neighbor_ncard (G : SimpleGraph V) (S : Set V)
    (u : {a : V // a ∉ S})
    (hunique : ∀ a b : V, a ∈ S → b ∈ S →
      G.Adj u.1 a → G.Adj u.1 b → a = b) :
    (G.neighborSet u.1).ncard =
      ((identificationGraph G S).neighborSet (some u)).ncard := by
  classical
  apply Set.ncard_congr (fun a _ => identificationMap S a)
  · intro a ha
    change G.Adj u.1 a at ha
    change (identificationGraph G S).Adj (some u) (identificationMap S a)
    by_cases haS : a ∈ S
    · simpa only [identificationMap, dite_eq_left haS, identificationGraph,
        identificationAdj] using (show ∃ b ∈ S, G.Adj u.1 b from ⟨a, haS, ha⟩)
    · simpa only [identificationMap, dite_eq_right haS, identificationGraph,
        identificationAdj] using ha
  · intro a b ha hb hab
    change G.Adj u.1 a at ha
    change G.Adj u.1 b at hb
    by_cases haS : a ∈ S
    · by_cases hbS : b ∈ S
      · exact hunique a b haS hbS ha hb
      · have he : (none : IdentificationVertex S) = some ⟨b, hbS⟩ := by
          simpa only [identificationMap, dite_eq_left haS, dite_eq_right hbS] using hab
        cases he
    · by_cases hbS : b ∈ S
      · have he : (some ⟨a, haS⟩ : IdentificationVertex S) = none := by
          simpa only [identificationMap, dite_eq_right haS, dite_eq_left hbS] using hab
        cases he
      · simpa only [identificationMap, dite_eq_right haS, dite_eq_right hbS,
          Option.some.injEq, Subtype.mk.injEq] using hab
  · intro b hb
    cases b with
    | none =>
      change ∃ a ∈ S, G.Adj u.1 a at hb
      rcases hb with ⟨a, haS, hua⟩
      refine ⟨a, hua, ?_⟩
      simp only [identificationMap, dite_eq_left haS]
    | some b =>
      change G.Adj u.1 b.1 at hb
      refine ⟨b.1, hb, ?_⟩
      simp only [identificationMap, dite_eq_right b.2]

/-- A real S-to-outside edge and an outside induced path lift to a genuine G-path. -/
theorem identification_spoke_lift
    (G : SimpleGraph V) (S : Set V) (u v : {a : V // a ∉ S})
    (p : (G.induce {a : V | a ∉ S}).Walk u v) (hp : p.IsPath)
    (hu : (identificationGraph G S).Adj none (some u)) :
    ∃ s ∈ S, ∃ q : G.Walk s v.1,
      q.IsPath ∧ q.length = p.length + 1 ∧
        ∀ a ∈ q.support, a = s ∨ a ∉ S := by
  rcases hu with ⟨s, hs, hsu⟩
  let f : G.induce {a : V | a ∉ S} →g G :=
    (SimpleGraph.Embedding.induce {a : V | a ∉ S}).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hp' : (p.map f).IsPath := (Walk.isPath_map_iff_of_injective hf).mpr hp
  have hs' : s ∉ (p.map f).support := by
    intro hmem
    rw [Walk.support_map] at hmem
    rcases List.mem_map.mp hmem with ⟨a, _ha, he⟩
    change a.1 = s at he
    exact a.2 (he.symm ▸ hs)
  have houtside : ∀ a ∈ (p.map f).support, a ∉ S := by
    intro a ha
    rw [Walk.support_map] at ha
    rcases List.mem_map.mp ha with ⟨b, _hb, he⟩
    change b.1 = a at he
    exact he ▸ b.2
  refine ⟨s, hs, Walk.cons hsu (p.map f), hp'.cons hs', ?_, ?_⟩
  · exact congrArg (fun n : ℕ => n + 1) (Walk.length_map (p := p) (f := f))
  · intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (houtside a ha)

#print axioms IdentificationVertex
#print axioms identificationAdj
#print axioms identificationGraph
#print axioms identification_adj_none_some
#print axioms identification_adj_some_none
#print axioms identification_adj_some_some
#print axioms identificationMap
#print axioms identification_neighbor_ncard
#print axioms identification_spoke_lift

end TaskH.Fan
