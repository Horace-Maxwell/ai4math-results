import Research.TaskH.Gao.G6FourTags
import Research.TaskH.Gao.IdentificationFamilyLift

/-! Actual paths in the four-tag G6 graph lift through its root-deleted graph.
The collapsed tag is never mapped as a graph homomorphism. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def g6ExteriorTag (H : Set V) (z : {q : G6Vertex H // q ≠ none}) : G6Retained H :=
  match z with
  | ⟨none, h⟩ => (h rfl).elim
  | ⟨some q, _⟩ => q

theorem g6ExteriorTag_injective (H : Set V) :
    Function.Injective (g6ExteriorTag H) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ he
  cases p with
  | none => exact (hp rfl).elim
  | some p =>
    cases q with
    | none => exact (hq rfl).elim
    | some q =>
      apply Subtype.ext
      exact congrArg Option.some he

def g6ExteriorHom (G : SimpleGraph V) (H A : Set V) (u w : V) :
    (g6Graph G H A u w).induce {q | q ≠ none} →g G where
  toFun z := g6Value H u w (g6ExteriorTag H z)
  map_rel' := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ e
    cases p with
    | none => exact (hp rfl).elim
    | some p =>
      cases q with
      | none => exact (hq rfl).elim
      | some q => exact e

theorem g6_root_free_path_lift (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w) (a b : G6Retained H)
    (p : (g6Graph G H A u w).Walk (some a) (some b))
    (hp : p.IsPath) (hn : none ∉ p.support) :
    ∃ q : G.Walk (g6Value H u w a) (g6Value H u w b),
      q.IsPath ∧ q.length = p.length ∧
        ∀ z ∈ q.support, z ∈ g6RetainedSet H u w := by
  let T : Set (G6Vertex H) := {q | q ≠ none}
  have hT : ∀ z ∈ p.support, z ∈ T := by
    intro z hz he
    subst z
    exact hn hz
  let pi := p.induce T hT
  have hm : pi.map (SimpleGraph.Embedding.induce T).toHom = p := Walk.map_induce p hT
  have hpi : pi.IsPath := Walk.IsPath.of_map (hm.symm ▸ hp)
  let f := g6ExteriorHom G H A u w
  have hf : Function.Injective f :=
    (g6Value_injective H u w hu hw huw).comp (g6ExteriorTag_injective H)
  refine ⟨pi.map f, (Walk.isPath_map_iff_of_injective (f := f) hf).mpr hpi, ?_, ?_⟩
  · have hlen := congrArg
      (fun r : (g6Graph G H A u w).Walk (some a) (some b) => r.length) hm
    exact (Walk.length_map (p := pi) (f := f)).trans
      ((Walk.length_map (p := pi) (f := (SimpleGraph.Embedding.induce T).toHom)).symm.trans hlen)
  · intro z hz
    have hzMapped : z ∈ (pi.map f).support := hz
    rw [Walk.support_map] at hzMapped
    obtain ⟨v, _hv, he⟩ := List.mem_map.mp hzMapped
    have hr : f v ∈ g6RetainedSet H u w :=
      (g6Value_range H u w).le ⟨g6ExteriorTag H v, rfl⟩
    exact Eq.mp (congrArg (fun t : V => t ∈ g6RetainedSet H u w) he) hr

theorem g6_tagged_path_lift (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w)
    (hST : Disjoint (g6Boundary G H A u) (g6RetainedSet H u w))
    (b : G6Retained H) (p : (g6Graph G H A u w).Walk none (some b))
    (hp : p.IsPath) :
    ∃ a ∈ g6Boundary G H A u, ∃ q : G.Walk a (g6Value H u w b),
      q.IsPath ∧ q.length = p.length ∧
        ∀ z ∈ q.support, z = a ∨ z ∈ g6RetainedSet H u w := by
  have hne : (none : G6Vertex H) ≠ some b := by intro he; cases he
  obtain ⟨c, e, t, rfl⟩ := Walk.exists_eq_cons_of_ne hne p
  cases c with
  | none => exact False.elim e
  | some c =>
    have ht := (Walk.cons_isPath_iff e t).mp hp
    obtain ⟨q, hqP, hqL, hqS⟩ :=
      g6_root_free_path_lift G H A u w hu hw huw c b t ht.1 ht.2
    have he : ∃ a ∈ g6Boundary G H A u, G.Adj a (g6Value H u w c) := e
    obtain ⟨a, ha, ea⟩ := he
    have han : a ∉ q.support := by
      intro h
      exact Set.disjoint_left.mp hST ha (hqS a h)
    refine ⟨a, ha, Walk.cons ea q, ?_, ?_, ?_⟩
    · exact (Walk.cons_isPath_iff ea q).mpr ⟨hqP, han⟩
    · exact (Walk.length_cons ea q).trans
        ((congrArg (fun n : ℕ => n + 1) hqL).trans (Walk.length_cons e t).symm)
    · intro z hz
      rw [Walk.support_cons] at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact Or.inl he
      · exact Or.inr (hqS z hz)

theorem g6_tagged_family_lift_to_u (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w)
    (hST : Disjoint (g6Boundary G H A u) (g6RetainedSet H u w))
    (r a d : ℕ)
    (p : Fin r → (g6Graph G H A u w).Walk (some (Sum.inr false)) none)
    (hp : AdmissiblePathFamily (g6Graph G H A u w) (some (Sum.inr false)) none r a d p) :
    ∃ v : Fin r → V, ∃ q : ∀ i, G.Walk (v i) u,
      (∀ i, v i ∈ g6Boundary G H A u) ∧
      EndpointPathFamily G r a d v (fun _ => u) q ∧
      (∀ i, (q i).length = (p i).length) ∧
      ∀ i z, z ∈ (q i).support → z = v i ∨ z ∈ g6RetainedSet H u w := by
  classical
  have hex : ∀ i : Fin r, ∃ v ∈ g6Boundary G H A u, ∃ q : G.Walk v u,
      q.IsPath ∧ q.length = (p i).length ∧
        ∀ z ∈ q.support, z = v ∨ z ∈ g6RetainedSet H u w := by
    intro i
    obtain ⟨v, hv, q, hqP, hqL, hqS⟩ := g6_tagged_path_lift G H A u w
      hu hw huw hST (Sum.inr false) (p i).reverse (hp.2.2 i).1.reverse
    refine ⟨v, hv, q, hqP, ?_, hqS⟩
    exact hqL.trans (Walk.length_reverse (p := p i))
  choose v hv q hqP hqL hqS using hex
  refine ⟨v, q, hv, ⟨hp.1, hp.2.1, ?_⟩, hqL, hqS⟩
  intro i
  exact ⟨hqP i, (hqL i).trans (hp.2.2 i).2⟩

#print axioms g6ExteriorTag
#print axioms g6ExteriorTag_injective
#print axioms g6ExteriorHom
#print axioms g6_root_free_path_lift
#print axioms g6_tagged_path_lift
#print axioms g6_tagged_family_lift_to_u
end TaskH.Gao
