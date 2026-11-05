import Research.Backfill.Paper7.AlgebraicContracts
import Research.Backfill.Paper7.UnicyclicBasic

/-! Source-only candidate: every component outside the actual unique cycle
has one attachment edge, with both endpoints unique. Existence follows an
actual walk in the connected original graph. Uniqueness constructs a walk
avoiding a bridge. No degree, integrality, order or Sun hypothesis is used.
This package does not supply an IntroUnicyclic21 check. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicAttachment
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra

/-- Follow a walk until it first leaves the component of the complement. -/
theorem component_boundary_of_walk {V : Type} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) {u v : V} (p : G.Walk u v) :
    ∀ (hu : u ∉ S), (⟨u, hu⟩ : {v // v ∉ S}) ∈ C.supp → v ∈ S →
      ∃ (x : {v // v ∉ S}), x ∈ C.supp ∧ ∃ (y : S), G.Adj x.val y.val := by
  classical
  induction p with
  | nil =>
      intro hu _ hv
      exact (hu hv).elim
  | @cons u v _z hadj _p ih =>
      intro hu huC hz
      by_cases hv : v ∈ S
      · exact ⟨⟨u, hu⟩, huC, ⟨v, hv⟩, hadj⟩
      · have hvC : (⟨v, hv⟩ : {v // v ∉ S}) ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp huC hadj
        exact ih hv hvC hz
#print axioms Paper7UnicyclicAttachment.component_boundary_of_walk

/-- A connected graph has a boundary edge from each complementary component
to any nonempty vertex set. A component is already nonempty by definition. -/
theorem connected_component_boundary_exists {V : Type} (G : SimpleGraph V)
    (S : Set V) (hG : G.Connected) (hS : S.Nonempty)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    ∃ (x : {v // v ∉ S}), x ∈ C.supp ∧ ∃ (y : S), G.Adj x.val y.val := by
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨v, hv⟩ := hS
  obtain ⟨p⟩ := hG u.val v
  exact component_boundary_of_walk G S C p u.property hu hv
#print axioms Paper7UnicyclicAttachment.connected_component_boundary_exists

/-- Two boundary edges from one complementary component to a connected
induced subgraph have the same endpoints if the first edge is a bridge. -/
theorem bridge_boundary_endpoints_eq {V : Type} (G : SimpleGraph V) (S : Set V)
    (hS : (G.induce S).Preconnected) (C : (G.induce Sᶜ).ConnectedComponent)
    (x x' : {v // v ∉ S}) (y y' : S) (hx : x ∈ C.supp) (hx' : x' ∈ C.supp)
    (hb : G.IsBridge s(x.val, y.val)) (hxy' : G.Adj x'.val y'.val) :
    x = x' ∧ y = y' := by
  classical
  have hedge : s(x.val, y.val) = s(x'.val, y'.val) := by
    by_contra hne
    let D := G.deleteEdges ({s(x.val, y.val)} : Set (Sym2 V))
    let outside : G.induce Sᶜ →g D :=
      { toFun := Subtype.val
        map_rel' := by
          intro a b hab
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨hab, ?_⟩
          intro he
          rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact b.property (hb.symm ▸ y.property)
          · exact a.property (ha.symm ▸ y.property) }
    let inside : G.induce S →g D :=
      { toFun := Subtype.val
        map_rel' := by
          intro a b hab
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨hab, ?_⟩
          intro he
          rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with ⟨ha, _⟩ | ⟨_, hb⟩
          · exact x.property (ha ▸ a.property)
          · exact x.property (hb ▸ b.property) }
    have hsecond : D.Adj x'.val y'.val := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hxy', ?_⟩
      intro he
      exact hne (Set.mem_singleton_iff.mp he).symm
    have hout : D.Reachable x.val x'.val :=
      (C.reachable_of_mem_supp hx hx').map outside
    have hin : D.Reachable y'.val y.val := (hS y' y).map inside
    exact (SimpleGraph.isBridge_iff.mp hb)
      (hout.trans (hsecond.reachable.trans hin))
  rcases Sym2.eq_iff.mp hedge with ⟨hxv, hyv⟩ | ⟨hxv, _⟩
  · exact ⟨Subtype.ext hxv, Subtype.ext hyv⟩
  · exact (x.property (hxv.symm ▸ y'.property)).elim
#print axioms Paper7UnicyclicAttachment.bridge_boundary_endpoints_eq

/-- Every edge incident to an off-cycle vertex is a bridge. The original
unique-cycle condition proves this; bridge status is not an extra premise. -/
theorem unicyclic_off_cycle_edge_isBridge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (x y : V) (hx : x ∉ w.support) (hxy : G.Adj x y) :
    G.IsBridge s(x, y) := by
  apply (SimpleGraph.isBridge_iff_forall_cycle_notMem (G.mem_edgeSet.mpr hxy)).mpr
  intro u p hp hep
  obtain ⟨t, _ht, huniq⟩ := Paper7Unicyclic.unicyclic_cycle_unique_data hG
  have hwt : w.edges.toFinset = t :=
    (huniq b w.edges.toFinset ⟨r, w, hw, hlen, rfl⟩).2
  have hpt : p.edges.toFinset = t :=
    (huniq p.length p.edges.toFinset ⟨u, p, hp, rfl, rfl⟩).2
  have hew : s(x, y) ∈ w.edges := by
    apply List.mem_toFinset.mp
    rw [hwt, ← hpt]
    exact List.mem_toFinset.mpr hep
  exact hx (w.fst_mem_support_of_mem_edges hew)
#print axioms Paper7UnicyclicAttachment.unicyclic_off_cycle_edge_isBridge

/-- The unique oriented pair consists of an off-cycle endpoint in `C` and
an actual cycle vertex. Both singleton and larger components are included. -/
theorem unicyclic_component_attachment_endpoints {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃! p : {v // v ∉ w.support} × {v // v ∈ w.support},
      p.1 ∈ C.supp ∧ G.Adj p.1.val p.2.val := by
  obtain ⟨x, hx, y, hxy⟩ := connected_component_boundary_exists G
    {v | v ∈ w.support} hG.1 ⟨r, w.start_mem_support⟩ C
  refine ⟨(x, y), ⟨hx, hxy⟩, ?_⟩
  rintro ⟨x', y'⟩ ⟨hx', hxy'⟩
  have hb := unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen
    x.val y.val x.property hxy
  obtain ⟨hxx', hyy'⟩ := bridge_boundary_endpoints_eq G {v | v ∈ w.support}
    w.connected_induce_support.preconnected C x x' y y' hx hx' hb hxy'
  exact Prod.ext hxx'.symm hyy'.symm
#print axioms Paper7UnicyclicAttachment.unicyclic_component_attachment_endpoints

/-- The endpoint theorem also gives uniqueness of the actual unordered edge. -/
theorem unicyclic_component_attachment_edge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃! e : Sym2 V, ∃ (x : {v // v ∉ w.support}), x ∈ C.supp ∧
      ∃ (y : {v // v ∈ w.support}), G.Adj x.val y.val ∧ e = s(x.val, y.val) := by
  obtain ⟨⟨x, y⟩, ⟨hx, hxy⟩, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  refine ⟨s(x.val, y.val), ⟨x, hx, y, hxy, rfl⟩, ?_⟩
  rintro e ⟨x', hx', y', hxy', rfl⟩
  have hp := huniq (x', y') ⟨hx', hxy'⟩
  exact congrArg (fun p : {v // v ∉ w.support} × {v // v ∈ w.support} =>
    s(p.1.val, p.2.val)) hp
#print axioms Paper7UnicyclicAttachment.unicyclic_component_attachment_edge

/-- Attachment data retain actual walks from every component vertex to the
off-cycle endpoint. Mapping one of these walks into `G` and appending the
attachment edge gives an actual walk from that vertex to the cycle. -/
theorem unicyclic_component_attachment_data {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃ (a : {v // v ∉ w.support}) (c : {v // v ∈ w.support}),
      a ∈ C.supp ∧ G.Adj a.val c.val ∧
      (∀ (a' : {v // v ∉ w.support}) (c' : {v // v ∈ w.support}),
        a' ∈ C.supp → G.Adj a'.val c'.val → a' = a ∧ c' = c) ∧
      (∀ x, x ∈ C.supp →
        Nonempty ((deleteVertices G {v | v ∈ w.support}).Walk x a)) := by
  obtain ⟨⟨a, c⟩, ⟨ha, hac⟩, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  refine ⟨a, c, ha, hac, ?_, ?_⟩
  · intro a' c' ha' hac'
    have hp := huniq (a', c') ⟨ha', hac'⟩
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · intro x hx
    exact C.reachable_of_mem_supp hx ha
#print axioms Paper7UnicyclicAttachment.unicyclic_component_attachment_data

end Paper7UnicyclicAttachment
