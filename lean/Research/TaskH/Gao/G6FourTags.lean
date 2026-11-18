import Research.TaskH.Gao.IdentificationDegree

/-! The fresh tag collapses the ACTUAL H-neighbor boundary in Q1-u.
All other vertices are actual H vertices, actual u, and actual w. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

abbrev G6Retained (H : Set V) := H ⊕ Bool
abbrev G6Vertex (H : Set V) := Option (G6Retained H)

def g6Value (H : Set V) (u w : V) : G6Retained H → V := fun p =>
  match p with
  | Sum.inl h => h.1
  | Sum.inr false => u
  | Sum.inr true => w

def g6Boundary (G : SimpleGraph V) (H A : Set V) (u : V) : Set V :=
  {a | a ∈ A ∧ a ≠ u ∧ ∃ h ∈ H, G.Adj a h}

def g6RetainedSet (H : Set V) (u w : V) : Set V := H ∪ ({u, w} : Set V)

def g6Adj (G : SimpleGraph V) (H A : Set V) (u w : V) :
    G6Vertex H → G6Vertex H → Prop := fun p q =>
  match p, q with
  | none, none => False
  | none, some q => ∃ a ∈ g6Boundary G H A u, G.Adj a (g6Value H u w q)
  | some p, none => ∃ a ∈ g6Boundary G H A u, G.Adj (g6Value H u w p) a
  | some p, some q => G.Adj (g6Value H u w p) (g6Value H u w q)

def g6Graph (G : SimpleGraph V) (H A : Set V) (u w : V) : SimpleGraph (G6Vertex H) where
  Adj := g6Adj G H A u w
  symm.symm p q e := by
    cases p with
    | none =>
      cases q with
      | none => exact False.elim e
      | some q => obtain ⟨a, ha, ea⟩ := e; exact ⟨a, ha, ea.symm⟩
    | some p =>
      cases q with
      | none => obtain ⟨a, ha, ea⟩ := e; exact ⟨a, ha, ea.symm⟩
      | some q => exact e.symm
  loopless.irrefl p := by
    cases p with
    | none => exact fun e => e
    | some p => exact G.irrefl

theorem g6Value_injective (H : Set V) (u w : V)
    (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w) :
    Function.Injective (g6Value H u w) := by
  intro p q e
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (Subtype.ext e)
    | inr q =>
      cases q with
      | false =>
        have he : p.1 = u := e
        exact False.elim (hu (Eq.mp (congrArg (fun z : V => z ∈ H) he) p.2))
      | true =>
        have he : p.1 = w := e
        exact False.elim (hw (Eq.mp (congrArg (fun z : V => z ∈ H) he) p.2))
  | inr p =>
    cases p with
    | false =>
      cases q with
      | inl q =>
        have he : q.1 = u := e.symm
        exact False.elim (hu (Eq.mp (congrArg (fun z : V => z ∈ H) he) q.2))
      | inr q => cases q <;> first | rfl | exact False.elim (huw e)
    | true =>
      cases q with
      | inl q =>
        have he : q.1 = w := e.symm
        exact False.elim (hw (Eq.mp (congrArg (fun z : V => z ∈ H) he) q.2))
      | inr q => cases q <;> first | rfl | exact False.elim (huw e.symm)

theorem g6Value_range (H : Set V) (u w : V) :
    Set.range (g6Value H u w) = g6RetainedSet H u w := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    cases p with
    | inl p => exact Or.inl p.2
    | inr p => cases p <;> simp [g6Value, g6RetainedSet]
  · intro hv
    rcases hv with hv | hv
    · exact ⟨Sum.inl ⟨v, hv⟩, rfl⟩
    · rcases hv with hv | hv
      · exact ⟨Sum.inr false, hv.symm⟩
      · exact ⟨Sum.inr true, hv.symm⟩

theorem g6_tag_to_h (G : SimpleGraph V) (H A : Set V) (u w : V) (h : H) :
    (g6Graph G H A u w).Adj none (some (Sum.inl h)) ↔
      ∃ a ∈ A, a ≠ u ∧ G.Adj a h.1 := by
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ha.1, ha.2.1, e⟩
  · rintro ⟨a, ha, hau, e⟩
    exact ⟨a, ⟨ha, hau, h.1, h.2, e⟩, e⟩

theorem g6_tag_to_w (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hS : (g6Boundary G H A u).Nonempty)
    (hcross : ∀ a ∈ A, G.Adj a w) :
    (g6Graph G H A u w).Adj none (some (Sum.inr true)) := by
  obtain ⟨a, ha⟩ := hS
  exact ⟨a, ha, hcross a ha.1⟩

theorem g6_tag_not_to_u (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hu : u ∈ A) (hind : ∀ a ∈ A, ∀ b ∈ A, ¬G.Adj a b) :
    ¬(g6Graph G H A u w).Adj none (some (Sum.inr false)) := by
  rintro ⟨a, ha, e⟩
  exact hind a ha.1 u hu e

theorem g6_actual_u_w (G : SimpleGraph V) (H A : Set V) (u w : V)
    (e : G.Adj u w) :
    (g6Graph G H A u w).Adj (some (Sum.inr false)) (some (Sum.inr true)) := e

theorem g6Boundary_disjoint_retained (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hHA : Disjoint H A) (hwA : w ∉ A) :
    Disjoint (g6Boundary G H A u) (g6RetainedSet H u w) := by
  apply Set.disjoint_left.mpr
  intro a ha haT
  rcases haT with haH | haT
  · exact Set.disjoint_left.mp hHA haH ha.1
  · rcases haT with hau | haw
    · exact ha.2.1 hau
    · exact hwA (haw ▸ ha.1)

theorem g6_order (H : Set V) [Fintype H] :
    Fintype.card (G6Vertex H) = Fintype.card H + 3 := by
  simp only [G6Vertex, G6Retained, Fintype.card_option, Fintype.card_sum,
    Fintype.card_bool]

#print axioms G6Retained
#print axioms G6Vertex
#print axioms g6Value
#print axioms g6Boundary
#print axioms g6RetainedSet
#print axioms g6Adj
#print axioms g6Graph
#print axioms g6Value_injective
#print axioms g6Value_range
#print axioms g6_tag_to_h
#print axioms g6_tag_to_w
#print axioms g6_tag_not_to_u
#print axioms g6_actual_u_w
#print axioms g6Boundary_disjoint_retained
#print axioms g6_order
end TaskH.Gao
