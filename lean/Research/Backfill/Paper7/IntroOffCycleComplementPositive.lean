import Research.Backfill.Paper7.IntroEvenSingleBridgeCycle
import Research.Backfill.Paper7.UnicyclicCoreCycle
import Research.Backfill.Paper7.UnicyclicComponentAttachment

/-! Route P: deleting a vertex outside the actual unique cycle leaves a
strictly supercritical complement to every component disjoint from that cycle.
No high vertex, terminal fan, Sun or concentrated attachment is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCycleComplement
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroCutGap Paper7IntroHighBranch Paper7IntroCycleNeighborhood
open Paper7UnicyclicAttachment

theorem zero_deleted_complement_core_boundary_at_deleted_vertex
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hzero : Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0)
    (S : Set V) (hv : v ∉ S)
    (hdisj : ∀ (x : S) (hx : x.val ≠ v),
      (⟨x.val, hx⟩ : {w : V // w ≠ v}) ∉ C.supp)
    (hdeg : ∀ x, (G.induce S).degree x = 2) :
    ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → j = v := by
  let K := (vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})
  let f : S → {x : {w : V // w ≠ v} // x ∉ C.supp} := fun x =>
    ⟨⟨x.val, fun h => hv (h ▸ x.property)⟩, hdisj x _⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {x : {w : V // w ≠ v} // x ∉ C.supp} => z.val.val) h)
  have hAdj : ∀ x y, (G.induce S).Adj x y ↔ K.Adj (f x) (f y) := by
    intro x y
    rfl
  intro i hi j hj hij
  by_contra hjv
  have hiv : i ≠ v := fun h => hv (h ▸ hi)
  have hjC : (⟨j, hjv⟩ : {w : V // w ≠ v}) ∉ C.supp := by
    intro hjC
    have hiC : (⟨i, hiv⟩ : {w : V // w ≠ v}) ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp hjC hij.symm
    exact hdisj ⟨i, hi⟩ hiv hiC
  let z : {x : {w : V // w ≠ v} // x ∉ C.supp} := ⟨⟨j, hjv⟩, hjC⟩
  have hz : ∀ x : S, z ≠ f x := by
    intro x h
    have hjx : j = x.val :=
      congrArg (fun q : {x : {w : V // w ≠ v} // x ∉ C.supp} => q.val.val) h
    exact hj (hjx.symm ▸ x.property)
  exact Ngt_two_zero_two_regular_no_boundary K hzero
    (G.induce S) f hf hAdj hdeg z hz ⟨i, hi⟩ hij.symm
#print axioms Paper7IntroCycleComplement.zero_deleted_complement_core_boundary_at_deleted_vertex

theorem unicyclic_single_outside_endpoint_has_single_crossing_edge
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (v : V) (hv : v ∉ w.support)
    (hboundary : ∀ i ∈ w.support, ∀ j ∉ w.support, G.Adj i j → j = v) :
    ∃ u, u ∈ w.support ∧ G.Adj u v ∧
      ∀ i ∈ w.support, ∀ j ∉ w.support, G.Adj i j → i = u ∧ j = v := by
  let D := (deleteVertices G {q | q ∈ w.support}).connectedComponentMk ⟨v, hv⟩
  obtain ⟨a, c, ha, hac, huniq, _hwalk⟩ :=
    unicyclic_component_attachment_data G b hG r w hw hlen D
  have hav : a.val = v := hboundary c.val c.property a.val a.property hac.symm
  have hcv : G.Adj c.val v := hav ▸ hac.symm
  refine ⟨c.val, c.property, hcv, ?_⟩
  intro i hi j hj hij
  have hjv : j = v := hboundary i hi j hj hij
  have hja : (⟨j, hj⟩ : {q : V // q ∉ w.support}) = a :=
    Subtype.ext (hjv.trans hav.symm)
  have hjD : (⟨j, hj⟩ : {q : V // q ∉ w.support}) ∈ D.supp := hja.symm ▸ ha
  have he := huniq ⟨j, hj⟩ ⟨i, hi⟩ hjD hij.symm
  exact ⟨congrArg Subtype.val he.2, hjv⟩
#print axioms Paper7IntroCycleComplement.unicyclic_single_outside_endpoint_has_single_crossing_edge

theorem intro21_even_off_cycle_component_complement_Ngt_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (v : V) (hv : v ∉ w.support)
    (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hdisj : ∀ (x : {q : V // q ∈ w.support}) (hx : x.val ≠ v),
      (⟨x.val, hx⟩ : {q : V // q ≠ v}) ∉ C.supp) :
    0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {q : V // q ≠ v})) 2 := by
  by_contra hnot
  have hzero : Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {q : V // q ≠ v})) 2 = 0 := by omega
  obtain ⟨e⟩ := Paper7SunAssembly.unicyclic_core_iso_cycle G b hG r w hw hlen
  have hd : ∀ x, (G.induce {q | q ∈ w.support}).degree x = 2 :=
    cycle_iso_degree_two (G.induce {q | q ∈ w.support}) b
      (Paper7Unicyclic.unicyclic_three_le hG) e.symm
  have hboundary := zero_deleted_complement_core_boundary_at_deleted_vertex
    G v C hzero {q | q ∈ w.support} hv hdisj (by
      intro x
      simpa only [← SimpleGraph.ncard_neighborSet] using hd x)
  obtain ⟨u, hu, huv, hcross⟩ :=
    unicyclic_single_outside_endpoint_has_single_crossing_edge G b hG r w hw hlen v hv hboundary
  exact intro21_even_no_single_bridge_cycle_side
    G b hG hI hn hb {q | q ∈ w.support} u v hu hv huv hcross e.symm
#print axioms Paper7IntroCycleComplement.intro21_even_off_cycle_component_complement_Ngt_pos

end Paper7IntroCycleComplement
