import Research.Backfill.Paper7.UnicyclicOffCycleForest
import Research.Backfill.Paper7.UnicyclicComponentAttachment
import Research.Backfill.Paper7.TreeEndpointPath

/-! Source-only repair of the actual development489 failure. The three direct
imports now have successful producers recorded in this package metadata.
Under the explicit conditional bound on all off-cycle degrees, this file
orders each actual complementary component from its unique attachment.
Component indexing into lists and the global Sun isomorphism remain gaps.
No IntroUnicyclic21 check or spectral branching claim is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicComponentPaths
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

/-- Transfer acyclicity through the actual component inclusion. The graph
and vertex type are abstract here, so applying this helper does not ask
Lean to reduce a nested deleted/induced graph while elaborating `induce`. -/
theorem connected_component_isAcyclic {W : Type} (H : SimpleGraph W)
    (hH : H.IsAcyclic) (C : H.ConnectedComponent) : C.toSimpleGraph.IsAcyclic := by
  apply hH.comap C.toSimpleGraph_hom
  intro u v h
  apply Subtype.ext
  exact h
#print axioms Paper7UnicyclicComponentPaths.connected_component_isAcyclic

/-- Double subtype inclusion embeds the component's neighbor set into the
original graph's neighbor set; all actual induced edges are retained. -/
theorem deleted_component_degree_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (C : (deleteVertices G S).ConnectedComponent) (x : C) :
    C.toSimpleGraph.degree x ≤ G.degree x.val.val := by
  let f : C.toSimpleGraph.neighborSet x → G.neighborSet x.val.val :=
    fun y => ⟨y.val.val.val, y.property⟩
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : G.neighborSet x.val.val => t.val) h
  rw [← C.toSimpleGraph.card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f hf
#print axioms Paper7UnicyclicComponentPaths.deleted_component_degree_le

/-- An actual edge to a deleted vertex uses one of the at most two original
neighbors, leaving at most one neighbor within the complementary component. -/
theorem deleted_component_attachment_degree_le_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (C : (deleteVertices G S).ConnectedComponent) (a : C) (c : S)
    (hdeg : G.degree a.val.val ≤ 2) (hac : G.Adj a.val.val c.val) :
    C.toSimpleGraph.degree a ≤ 1 := by
  change (C.toSimpleGraph.neighborFinset a).card ≤ 1
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hax : G.Adj a.val.val x.val.val :=
    (C.toSimpleGraph.mem_neighborFinset a x).mp hx
  have hay : G.Adj a.val.val y.val.val :=
    (C.toSimpleGraph.mem_neighborFinset a y).mp hy
  have hcx : c.val ≠ x.val.val := by
    intro h
    exact x.val.property (h ▸ c.property)
  have heq := Paper7TreeEndpointPath.neighbor_eq_of_degree_le_two G
    a.val.val c.val x.val.val y.val.val hdeg hac hax hcx hay
  rcases heq with hyc | hyx
  · exact (y.val.property (hyc.symm ▸ c.property)).elim
  · exact Subtype.ext (Subtype.ext hyx.symm)
#print axioms Paper7UnicyclicComponentPaths.deleted_component_attachment_degree_le_one

/-- Assemble endpoint path data for an arbitrary deletion set before
instantiating that set with a concrete cycle support. All component-degree
transfers and finite-tree typeclass elaboration stay in this generic proof. -/
theorem deleted_component_endpoint_path_data {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hforest : (deleteVertices G S).IsAcyclic)
    (hdeg : ∀ v, v ∉ S → G.degree v ≤ 2)
    (C : (deleteVertices G S).ConnectedComponent) (a : C) (c : S)
    (hac : G.Adj a.val.val c.val) :
    ∃ (z : C) (p : C.toSimpleGraph.Walk a z),
      p.IsPath ∧ (∀ v : C, v ∈ p.support) ∧
      p.length + 1 = Fintype.card C ∧
      Function.Bijective (fun i : Fin (p.length + 1) => p.getVert i.val) ∧
      ∀ i j : Fin (p.length + 1),
        C.toSimpleGraph.Adj (p.getVert i.val) (p.getVert j.val) ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hacyc : C.toSimpleGraph.IsAcyclic :=
    connected_component_isAcyclic (deleteVertices G S) hforest C
  have hcomponent_degree : ∀ x : C, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    have hle : C.toSimpleGraph.degree x ≤ G.degree x.val.val :=
      deleted_component_degree_le G S C x
    exact Nat.le_trans hle (hdeg x.val.val x.val.property)
  have hroot_degree : C.toSimpleGraph.degree a ≤ 1 :=
    deleted_component_attachment_degree_le_one G S C a c
      (hdeg a.val.val a.val.property) hac
  exact Paper7TreeEndpointPath.finite_tree_endpoint_path_data C.toSimpleGraph
    C.connected_toSimpleGraph hacyc hcomponent_degree a hroot_degree
#print axioms Paper7UnicyclicComponentPaths.deleted_component_endpoint_path_data

/-- For every actual off-cycle component obtain its attachment endpoints,
the covering simple path starting at the off-cycle endpoint, and all path
coordinates. The outside-degree bound is an explicit helper hypothesis. -/
theorem unicyclic_component_rooted_path_data {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b)
    (hdeg : ∀ v, v ∉ w.support → G.degree v ≤ 2)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃ (a : C) (c : {v // v ∈ w.support}), G.Adj a.val.val c.val ∧
      (∀ (a' : C) (c' : {v // v ∈ w.support}),
        G.Adj a'.val.val c'.val → a' = a ∧ c' = c) ∧
      ∃ (z : C) (p : C.toSimpleGraph.Walk a z),
        p.IsPath ∧ (∀ v : C, v ∈ p.support) ∧
        p.length + 1 = Fintype.card C ∧
        Function.Bijective (fun i : Fin (p.length + 1) => p.getVert i.val) ∧
        ∀ i j : Fin (p.length + 1),
          C.toSimpleGraph.Adj (p.getVert i.val) (p.getVert j.val) ↔
            i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨ao, c, ha, hac, huniq, _hwalk⟩ :=
    Paper7UnicyclicAttachment.unicyclic_component_attachment_data G b hG r w hw hlen C
  let a : C := ⟨ao, ha⟩
  have hforest := Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen
  refine ⟨a, c, hac, ?_, ?_⟩
  · intro a' c' hadj
    have heq := huniq a'.val c' a'.property hadj
    exact ⟨Subtype.ext heq.1, heq.2⟩
  · simpa only [Fintype.card_eq_nat_card] using
      deleted_component_endpoint_path_data G {v | v ∈ w.support} hforest hdeg C a c hac
#print axioms Paper7UnicyclicComponentPaths.unicyclic_component_rooted_path_data

/-- A genuine path-graph coordinate system for the component, with its
positive pendant length equal to the number of component vertices. Internal
adjacency and every edge from this component to the cycle are characterized. -/
theorem unicyclic_component_path_coordinates {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b)
    (hdeg : ∀ v, v ∉ w.support → G.degree v ≤ 2)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃ (n : ℕ) (_hn : 0 < n) (e : pathGraph n ≃g C.toSimpleGraph)
      (c : {v // v ∈ w.support}), n = Fintype.card C ∧
      (∀ i j : Fin n, G.Adj (e i).val.val (e j).val.val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      (∀ (i : Fin n) (y : {v // v ∈ w.support}),
        G.Adj (e i).val.val y.val ↔ i.val = 0 ∧ y = c) := by
  obtain ⟨a, c, hac, huniq, z, p, _hp, _hcover, hcard, hbij, hadj⟩ :=
    unicyclic_component_rooted_path_data G b hG r w hw hlen hdeg C
  let coords : Fin (p.length + 1) ≃ C := Equiv.ofBijective _ hbij
  let e : pathGraph (p.length + 1) ≃g C.toSimpleGraph :=
    { toEquiv := coords
      map_rel_iff' := by
        intro i j
        change C.toSimpleGraph.Adj (p.getVert i.val) (p.getVert j.val) ↔
          (pathGraph (p.length + 1)).Adj i j
        rw [pathGraph_adj]
        exact hadj i j }
  have hn : 0 < p.length + 1 := Nat.succ_pos _
  have he0 : e ⟨0, hn⟩ = a := by
    change p.getVert 0 = a
    exact p.getVert_zero
  refine ⟨p.length + 1, hn, e, c, hcard, ?_, ?_⟩
  · intro i j
    change C.toSimpleGraph.Adj (e i) (e j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val
    rw [e.map_rel_iff, pathGraph_adj]
  · intro i y
    constructor
    · intro h
      obtain ⟨hei, hy⟩ := huniq (e i) y h
      have hi : i = ⟨0, hn⟩ := e.injective (hei.trans he0.symm)
      exact ⟨congrArg Fin.val hi, hy⟩
    · rintro ⟨hi, rfl⟩
      have hi0 : i = ⟨0, hn⟩ := Fin.ext hi
      rw [hi0, he0]
      exact hac
#print axioms Paper7UnicyclicComponentPaths.unicyclic_component_path_coordinates

end Paper7UnicyclicComponentPaths
