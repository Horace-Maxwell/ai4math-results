import Research.Backfill.Paper7.UnicyclicComponentAttachment
import Research.Backfill.Paper7.IntroDeletedVertexGap

/-! Deleting the unique outside attachment vertex separates every remaining
vertex of that outside component from the original core, without branch bounds. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCycleNeighborhood
open SimpleGraph BackfillPaper7.Challenge Paper7IntroCutGap

theorem deleted_attachment_walk_stays_outside_component
    {V : Type} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) (a : {v : V // v ∉ S})
    (hgate : ∀ (x : {v : V // v ∉ S}), x ∈ C.supp →
      ∀ y : S, G.Adj x.val y.val → x = a)
    {u z : {v : V // v ≠ a.val}} (p : (vertexDeletedGraph G a.val).Walk u z) :
    ∀ (hu : u.val ∉ S), (⟨u.val, hu⟩ : {v : V // v ∉ S}) ∈ C.supp →
      ∃ hz : z.val ∉ S, (⟨z.val, hz⟩ : {v : V // v ∉ S}) ∈ C.supp := by
  induction p with
  | nil =>
      intro hu huC
      exact ⟨hu, huC⟩
  | @cons u v z huv _p ih =>
      intro hu huC
      by_cases hv : v.val ∈ S
      · have he := hgate ⟨u.val, hu⟩ huC ⟨v.val, hv⟩ huv
        exact (u.property (congrArg Subtype.val he)).elim
      · have hvC : (⟨v.val, hv⟩ : {x : V // x ∉ S}) ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp huC huv
        exact ih hv hvC
#print axioms Paper7IntroCycleNeighborhood.deleted_attachment_walk_stays_outside_component

theorem deleted_attachment_component_disjoint_core
    {V : Type} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) (a : {v : V // v ∉ S})
    (hgate : ∀ (x : {v : V // v ∉ S}), x ∈ C.supp →
      ∀ y : S, G.Adj x.val y.val → x = a)
    (D : (vertexDeletedGraph G a.val).ConnectedComponent)
    (u : {v : V // v ≠ a.val}) (huD : u ∈ D.supp)
    (huS : u.val ∉ S) (huC : (⟨u.val, huS⟩ : {v : V // v ∉ S}) ∈ C.supp) :
    ∀ (x : S) (hx : x.val ≠ a.val), (⟨x.val, hx⟩ : {v : V // v ≠ a.val}) ∉ D.supp := by
  intro x hx hxD
  obtain ⟨p⟩ := D.reachable_of_mem_supp huD hxD
  obtain ⟨hxS, _hxC⟩ := deleted_attachment_walk_stays_outside_component
    G S C a hgate p huS huC
  exact hxS x.property
#print axioms Paper7IntroCycleNeighborhood.deleted_attachment_component_disjoint_core

end Paper7IntroCycleNeighborhood
