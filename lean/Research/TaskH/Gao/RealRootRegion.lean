import Research.TaskH.Gao.GraphIsoTwoConnected
import Research.TaskH.Gao.OneRootExtension

/-! A real original vertex x is adjoined to B. Option tags only relabel that
actual induced graph; they are not a quotient of an empty boundary. -/
set_option autoImplicit false
universe u v
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u} {W : Type v}

def realRootGraph (G : SimpleGraph V) (B : Set V) (x : V) : SimpleGraph (B ∪ {x} : Set V) :=
  G.induce (B ∪ {x})

def realRootPoint (B : Set V) (x : V) : (B ∪ {x} : Set V) := ⟨x, Or.inr rfl⟩

def realRootBlockPoint (B : Set V) (x : V) (b : B) : (B ∪ {x} : Set V) :=
  ⟨b.1, Or.inl b.2⟩

noncomputable def realRootEquiv (B : Set V) (x : V) (hx : x ∉ B) :
    Option B ≃ (B ∪ {x} : Set V) := by
  classical
  exact {
    toFun := fun z => match z with
      | none => realRootPoint B x
      | some b => realRootBlockPoint B x b
    invFun := fun z => if hz : z.1 ∈ B then some ⟨z.1, hz⟩ else none
    left_inv := by
      intro z
      cases z with
      | none =>
        change (if hz : x ∈ B then some (⟨x, hz⟩ : B) else none) = none
        exact dite_eq_right hx
      | some b =>
        change (if hz : b.1 ∈ B then some (⟨b.1, hz⟩ : B) else none) = some b
        rw [dite_eq_left b.2]
    right_inv := by
      intro z
      by_cases hz : z.1 ∈ B
      · simp only [dite_eq_left hz]
        exact Subtype.ext rfl
      · simp only [dite_eq_right hz]
        apply Subtype.ext
        rcases z.2 with hzB | hzx
        · exact False.elim (hz hzB)
        · exact hzx.symm }

noncomputable def realRootTaggedGraph (G : SimpleGraph V) (B : Set V) (x : V) (hx : x ∉ B) :
    SimpleGraph (Option B) := (realRootGraph G B x).comap (realRootEquiv B x hx)

noncomputable def realRootGraphIso (G : SimpleGraph V) (B : Set V) (x : V) (hx : x ∉ B) :
    realRootTaggedGraph G B x hx ≃g realRootGraph G B x where
  toEquiv := realRootEquiv B x hx
  map_rel_iff' := by intro a b; rfl

theorem rootedTwoConnected_of_graphIso [iV : Fintype V] [iW : Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (a b : V)
    (hG : RootedTwoConnected G a b) : RootedTwoConnected H (e a) (e b) := by
  have et : (G ⊔ SimpleGraph.edge a b) ≃g (H ⊔ SimpleGraph.edge (e a) (e b)) := {
    toEquiv := e.toEquiv
    map_rel_iff' := by
      intro r s
      simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      change (H.Adj (e r) (e s) ∨
        ((e r = e a ∧ e s = e b ∨ e r = e b ∧ e s = e a) ∧ e r ≠ e s)) ↔
          (G.Adj r s ∨ ((r = a ∧ s = b ∨ r = b ∧ s = a) ∧ r ≠ s))
      constructor
      · rintro (hrs | ⟨hr, hne⟩)
        · exact Or.inl (e.map_rel_iff.mp hrs)
        · refine Or.inr ⟨?_, fun he => hne (congrArg e he)⟩
          rcases hr with ⟨hr, hs⟩ | ⟨hr, hs⟩
          · exact Or.inl ⟨e.toEquiv.injective hr, e.toEquiv.injective hs⟩
          · exact Or.inr ⟨e.toEquiv.injective hr, e.toEquiv.injective hs⟩
      · rintro (hrs | ⟨hr, hne⟩)
        · exact Or.inl (e.map_rel_iff.mpr hrs)
        · refine Or.inr ⟨?_, fun he => hne (e.toEquiv.injective he)⟩
          rcases hr with ⟨hr, hs⟩ | ⟨hr, hs⟩
          · exact Or.inl ⟨congrArg e hr, congrArg e hs⟩
          · exact Or.inr ⟨congrArg e hr, congrArg e hs⟩ }
  refine ⟨fun he => hG.1 (e.toEquiv.injective he), ?_⟩
  exact twoConnected_of_graphIso (G ⊔ SimpleGraph.edge a b)
    (H ⊔ SimpleGraph.edge (e a) (e b)) et hG.2

theorem realRoot_rooted_from_actual_spoke (G : SimpleGraph V) (B : Set V) (x : V)
    (hx : x ∉ B) [iB : Fintype B] [iT : Fintype (B ∪ {x} : Set V)]
    (b w : B) (hB : @TwoConnected B iB (G.induce B))
    (hspoke : G.Adj x w.1) (hwb : w ≠ b) :
    RootedTwoConnected (realRootGraph G B x) (realRootPoint B x) (realRootBlockPoint B x b) := by
  have hret : ∀ a d : B,
      (realRootTaggedGraph G B x hx).Adj (some a) (some d) ↔ (G.induce B).Adj a d := by
    intro a d
    rfl
  have hw : (realRootTaggedGraph G B x hx).Adj none (some w) := hspoke
  have htag := one_root_extension_rooted (G.induce B) (realRootTaggedGraph G B x hx)
    b w hB hret hw hwb
  exact rootedTwoConnected_of_graphIso (realRootTaggedGraph G B x hx) (realRootGraph G B x)
    (realRootGraphIso G B x hx) none (some b) htag

#print axioms realRootGraph
#print axioms realRootPoint
#print axioms realRootBlockPoint
#print axioms realRootEquiv
#print axioms realRootTaggedGraph
#print axioms realRootGraphIso
#print axioms rootedTwoConnected_of_graphIso
#print axioms realRoot_rooted_from_actual_spoke
end TaskH.Gao
