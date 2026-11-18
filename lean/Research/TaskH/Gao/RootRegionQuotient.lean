import Research.TaskH.Gao.CliqueCoreDegree
import Research.TaskH.Fan.IdentificationConnectivity
import Research.TaskH.Fan.AdjEqConnectivity

/-! Actual whole-graph map for a retained region with one exceptional root. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

noncomputable def rootRegionMap (N S : Set V) :
    V → IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S} := by
  classical
  exact fun v => if hv : v ∈ N ∪ S then
    identificationMap {z : (N ∪ S : Set V) | z.1 ∈ S} ⟨v, hv⟩ else none

theorem rootRegionMap_of_mem (N S : Set V) (v : V) (hv : v ∈ N ∪ S) :
    rootRegionMap N S v = identificationMap {z : (N ∪ S : Set V) | z.1 ∈ S} ⟨v, hv⟩ := by
  classical
  simp only [rootRegionMap, dite_eq_left hv]

theorem rootRegionMap_of_not_mem (N S : Set V) (v : V) (hv : v ∉ N ∪ S) :
    rootRegionMap N S v = none := by
  classical
  simp only [rootRegionMap, dite_eq_right hv]

theorem rootRegionMap_retained (N S : Set V)
    (r : {z : (N ∪ S : Set V) // z.1 ∉ S}) :
    rootRegionMap N S r.1.1 = some r := by
  classical
  rw [rootRegionMap_of_mem N S r.1.1 r.1.2]
  change (if hr : r.1.1 ∈ S then none else some ⟨r.1, hr⟩) = some r
  exact dite_eq_right r.2

theorem rootRegionMap_some_value (N S : Set V) (v : V)
    (r : {z : (N ∪ S : Set V) // z.1 ∉ S})
    (he : rootRegionMap N S v = some r) : v = r.1.1 := by
  classical
  by_cases hv : v ∈ N ∪ S
  · rw [rootRegionMap_of_mem N S v hv] at he
    change (if h : v ∈ S then none else some ⟨⟨v, hv⟩, h⟩) = some r at he
    by_cases hs : v ∈ S
    · rw [dite_eq_left hs] at he
      cases he
    · rw [dite_eq_right hs, Option.some.injEq] at he
      exact congrArg Subtype.val (congrArg Subtype.val he)
  · rw [rootRegionMap_of_not_mem N S v hv] at he
    cases he

theorem rootRegionMap_surjective (N S : Set V) (hS : S.Nonempty) :
    Function.Surjective (rootRegionMap N S) := by
  have hs : ({z : (N ∪ S : Set V) | z.1 ∈ S} : Set (N ∪ S : Set V)).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨⟨s, Or.inr hs⟩, hs⟩
  intro q
  obtain ⟨v, hv⟩ := identification_map_surjective {z : (N ∪ S : Set V) | z.1 ∈ S} hs q
  exact ⟨v.1, (rootRegionMap_of_mem N S v.1 v.2).trans hv⟩

theorem rootRegionMap_cross (G : SimpleGraph V) (N S : Set V)
    (hNS : Disjoint N S) (u : N)
    (hclose : ∀ a ∈ N, a ≠ u.1 → ∀ b, G.Adj a b → b ∈ N ∪ S)
    (a b : V) (ha : a ∈ N ∪ S) (hb : b ∉ N ∪ S) (e : G.Adj a b) :
    rootRegionMap N S a = rootRegionMap N S b ∨
      ((regionIdentificationGraph G N S) ⊔
        SimpleGraph.edge none (some (regionRetainedVertex N S hNS u))).Adj
        (rootRegionMap N S a) (rootRegionMap N S b) := by
  classical
  by_cases haS : a ∈ S
  · left
    rw [rootRegionMap_of_mem N S a ha, rootRegionMap_of_not_mem N S b hb]
    change (if h : a ∈ S then
      (none : IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S})
      else some ⟨⟨a, ha⟩, h⟩) = none
    exact dite_eq_left haS
  · have haN : a ∈ N := ha.elim id (fun h => False.elim (haS h))
    have hau : a = u.1 := by
      by_contra hn
      exact hb (hclose a haN hn b e)
    have hm : rootRegionMap N S a = some (regionRetainedVertex N S hNS u) := by
      rw [hau]
      exact rootRegionMap_retained N S (regionRetainedVertex N S hNS u)
    rw [hm, rootRegionMap_of_not_mem N S b hb]
    right
    exact Or.inr ((SimpleGraph.edge_adj none (some (regionRetainedVertex N S hNS u)) _ _).mpr
      ⟨Or.inr ⟨rfl, rfl⟩, by intro he; cases he⟩)

theorem rootRegionMap_adj_or_eq (G : SimpleGraph V) (N S : Set V)
    (hNS : Disjoint N S) (u : N)
    (hclose : ∀ a ∈ N, a ≠ u.1 → ∀ b, G.Adj a b → b ∈ N ∪ S)
    {a b : V} (e : G.Adj a b) :
    rootRegionMap N S a = rootRegionMap N S b ∨
      ((regionIdentificationGraph G N S) ⊔
        SimpleGraph.edge none (some (regionRetainedVertex N S hNS u))).Adj
        (rootRegionMap N S a) (rootRegionMap N S b) := by
  classical
  by_cases ha : a ∈ N ∪ S
  · by_cases hb : b ∈ N ∪ S
    · rw [rootRegionMap_of_mem N S a ha, rootRegionMap_of_mem N S b hb]
      rcases identification_map_adj_or_eq (G.induce (N ∪ S))
        {z : (N ∪ S : Set V) | z.1 ∈ S}
        (show (G.induce (N ∪ S)).Adj ⟨a, ha⟩ ⟨b, hb⟩ from e) with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · exact rootRegionMap_cross G N S hNS u hclose a b ha hb e
  · by_cases hb : b ∈ N ∪ S
    · rcases rootRegionMap_cross G N S hNS u hclose b a hb ha e.symm with he | he
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · left
      rw [rootRegionMap_of_not_mem N S a ha, rootRegionMap_of_not_mem N S b hb]

theorem rootRegion_delete_retained_connected (G : SimpleGraph V) (N S : Set V)
    (hNS : Disjoint N S) (u : N) (hS : S.Nonempty)
    (hclose : ∀ a ∈ N, a ≠ u.1 → ∀ b, G.Adj a b → b ∈ N ∪ S)
    (r : {z : (N ∪ S : Set V) // z.1 ∉ S})
    (hG : (G.induce {v : V | v ≠ r.1.1}).Connected) :
    (((regionIdentificationGraph G N S) ⊔
      SimpleGraph.edge none (some (regionRetainedVertex N S hNS u))).induce
      {v : IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S} | v ≠ some r}).Connected := by
  let f : {v : V // v ≠ r.1.1} →
      {v : IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S} // v ≠ some r} := fun a =>
    ⟨rootRegionMap N S a.1, fun he => a.2 (rootRegionMap_some_value N S a.1 r he)⟩
  have hs : Function.Surjective f := by
    intro q
    obtain ⟨a, ha⟩ := rootRegionMap_surjective N S hS q.1
    have har : a ≠ r.1.1 := by
      intro he
      have hmap : rootRegionMap N S a = some r := by
        rw [he]
        exact rootRegionMap_retained N S r
      exact q.2 (ha.symm.trans hmap)
    exact ⟨⟨a, har⟩, Subtype.ext ha⟩
  have hf : ∀ {a b : {v : V // v ≠ r.1.1}}, (G.induce {v : V | v ≠ r.1.1}).Adj a b →
      f a = f b ∨
      (((regionIdentificationGraph G N S) ⊔
        SimpleGraph.edge none (some (regionRetainedVertex N S hNS u))).induce
        {v : IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S} | v ≠ some r}).Adj (f a) (f b) := by
    intro a b e
    rcases rootRegionMap_adj_or_eq G N S hNS u hclose e with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  exact connected_of_surjective_adj_or_eq f hs hf hG

theorem rootRegion_quotient_rooted [Fintype V] (G : SimpleGraph V) (N S : Set V)
    (hNS : Disjoint N S) (u : N) (hS : S.Nonempty)
    (hN : (G.induce N).Connected) (hNcard : 2 ≤ N.ncard)
    (hclose : ∀ a ∈ N, a ≠ u.1 → ∀ b, G.Adj a b → b ∈ N ∪ S)
    (hG : TwoConnected G)
    [Fintype (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S})] :
    RootedTwoConnected (regionIdentificationGraph G N S) none
      (some (regionRetainedVertex N S hNS u)) := by
  let J := (regionIdentificationGraph G N S) ⊔
    SimpleGraph.edge none (some (regionRetainedVertex N S hNS u))
  have hcard : 3 ≤ Fintype.card (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) := by
    rw [Fintype.card_eq_nat_card, regionIdentification_card N S hNS]
    omega
  have hc : J.Connected := connected_of_surjective_adj_or_eq
    (rootRegionMap N S) (rootRegionMap_surjective N S hS)
    (rootRegionMap_adj_or_eq G N S hNS u hclose) hG.2.1
  constructor
  · intro he
    cases he
  · refine ⟨hcard, hc, ?_⟩
    intro z
    cases z with
    | some r => exact rootRegion_delete_retained_connected G N S hNS u hS hclose r (hG.2.2 r.1.1)
    | none =>
      let f : G.induce N →g J.induce {v | v ≠ none} := {
        toFun := fun a => ⟨some (regionRetainedVertex N S hNS a), by intro he; cases he⟩
        map_rel' := by intro a b e; exact Or.inl e }
      have hf : Function.Surjective f := by
        rintro ⟨z, hz⟩
        cases z with
        | none => exact False.elim (hz rfl)
        | some r =>
          have hrN : r.1.1 ∈ N := r.1.2.elim id (fun hs => False.elim (r.2 hs))
          exact ⟨⟨r.1.1, hrN⟩, Subtype.ext (congrArg Option.some (Subtype.ext (Subtype.ext rfl)))⟩
      exact SimpleGraph.Connected.map f hf hN

#print axioms rootRegionMap
#print axioms rootRegionMap_of_mem
#print axioms rootRegionMap_of_not_mem
#print axioms rootRegionMap_retained
#print axioms rootRegionMap_some_value
#print axioms rootRegionMap_surjective
#print axioms rootRegionMap_cross
#print axioms rootRegionMap_adj_or_eq
#print axioms rootRegion_delete_retained_connected
#print axioms rootRegion_quotient_rooted
end TaskH.Gao
