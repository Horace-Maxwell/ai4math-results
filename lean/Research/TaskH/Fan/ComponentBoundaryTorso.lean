import Research.TaskH.Fan.OutsideComponent
import Research.TaskH.Fan.TwoBoundaryTorso

/-! Crossing edges and the complete actual complement-torso induction step. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem connected_crossing_edge (G : SimpleGraph V) (S : Set V) (hG : G.Connected)
    (p q : V) (hp : p ∈ S) (hq : q ∉ S) :
    ∃ v ∈ S, ∃ w ∉ S, G.Adj v w := by
  classical
  by_contra hn
  have hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S := by
    intro v hv w e
    by_contra hw
    exact hn ⟨v, hv, w, hw, e⟩
  have hwalk : ∀ {v w : V}, G.Walk v w → v ∈ S → w ∈ S := by
    intro v w t
    induction t with
    | nil => exact fun h => h
    | cons e t ih =>
      intro hv
      exact ih (hclosed _ hv _ e)
  obtain ⟨t⟩ := hG p q
  exact hq (hwalk t hp)

theorem twoBoundary_neighbor [Fintype V] (G : SimpleGraph V) (C : Set V)
    (hG : TwoConnected G) (a b y w : V) (hy : y ∈ C) (hb : b ∉ C)
    (hw : w ∉ C) (hwb : w ≠ b)
    (hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = a ∨ z = b) :
    ∃ c ∈ C, G.Adj a c := by
  have hyb : y ≠ b := fun he => hb (he ▸ hy)
  obtain ⟨c, hc, z, hz, e⟩ := connected_crossing_edge
    (G.induce {v | v ≠ b}) {v | v.1 ∈ C} (hG.2.2 b)
    ⟨y, hyb⟩ ⟨w, hwb⟩ hy hw
  rcases hbound c.1 hc z.1 hz e with hza | hzb
  · exact ⟨c.1, hc, hza ▸ e.symm⟩
  · exact False.elim (z.2 hzb)

theorem twoBoundary_both_neighbors [Fintype V] (G : SimpleGraph V) (C : Set V)
    (hG : TwoConnected G) (x a y w : V) (hy : y ∈ C) (hx : x ∉ C)
    (ha : a ∉ C) (hw : w ∉ C) (hwx : w ≠ x) (hwa : w ≠ a)
    (hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = x ∨ z = a) :
    (∃ c ∈ C, G.Adj x c) ∧ (∃ c ∈ C, G.Adj a c) := by
  refine ⟨twoBoundary_neighbor G C hG x a y w hy ha hw hwa hbound, ?_⟩
  exact twoBoundary_neighbor G C hG a x y w hy hx hw hwx
    (fun c hc z hz e => (hbound c hc z hz e).elim Or.inr Or.inl)

theorem complement_nonroot_closed (G : SimpleGraph V) (C : Set V) (x a : V)
    (hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = x ∨ z = a) :
    ∀ v ∈ Cᶜ, v ≠ x → v ≠ a → ∀ w, G.Adj v w → w ∈ Cᶜ := by
  intro v hv hvx hva w e
  change w ∉ C
  intro hw
  rcases hbound w hw v hv e.symm with h | h
  · exact hvx h
  · exact hva h

theorem complement_nonroot_ncard (G : SimpleGraph V) (C : Set V) (x a : V)
    (hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = x ∨ z = a)
    (t : {z : V // z ∉ C}) (htx : t.1 ≠ x) (hta : t.1 ≠ a) :
    (G.neighborSet t.1).ncard = ((G.induce Cᶜ).neighborSet t).ncard := by
  apply Set.ncard_congr (fun z hz =>
    (⟨z, complement_nonroot_closed G C x a hbound t.1 t.2 htx hta z hz⟩ : {z : V // z ∉ C}))
  · intro z hz
    exact hz
  · intro z w hz hw he
    exact congrArg Subtype.val he
  · intro z hz
    exact ⟨z.1, hz, Subtype.ext rfl⟩

theorem component_complement_induction [Fintype V] (G : SimpleGraph V)
    (C : Set V) (hC : (G.induce C).Connected) (x a y : V)
    (hG : TwoConnected G) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hx : x ∉ C) (ha : a ∉ C) (hy : y ∈ C) (hxa : x ≠ a)
    [Fintype {z : V // z ∉ C}] (hcard : 3 ≤ Fintype.card {z : V // z ∉ C})
    (hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = x ∨ z = a)
    (hedge : ∃ c ∈ C, G.Adj a c)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  classical
  let _ : Fintype (Cᶜ : Set V) := ‹Fintype {z : V // z ∉ C}›
  let xr : {z : V // z ∉ C} := ⟨x, hx⟩
  let ar : {z : V // z ∉ C} := ⟨a, ha⟩
  have hxa' : xr ≠ ar := fun he => hxa (congrArg Subtype.val he)
  have htorso := twoBoundaryTorso_twoConnected G Cᶜ xr ar hxa' hcard hG
    (complement_nonroot_closed G C x a hbound)
  have hroot : RootedTwoConnected (G.induce Cᶜ) xr ar := ⟨hxa', htorso⟩
  have hdegree : NonrootDegreeAtLeast (G.induce Cᶜ) xr ar 3 := by
    intro t htx hta
    have htx' : t.1 ≠ x := fun he => htx (Subtype.ext he)
    have hta' : t.1 ≠ a := fun he => hta (Subtype.ext he)
    have hty : t.1 ≠ y := fun he => t.2 (he.symm ▸ hy)
    rw [← complement_nonroot_ncard G C x a hbound t htx' hta']
    exact hdeg t.1 htx' hty
  have hlt : Fintype.card {z : V // z ∉ C} < Fintype.card V :=
    Fintype.card_subtype_lt (p := fun v => v ∈ Cᶜ) (x := y) (fun h => h hy)
  obtain ⟨p, q, hpq⟩ := ih {z : V // z ∉ C} (G.induce Cᶜ) xr ar hlt hroot hdegree
  obtain ⟨r, hr, _hrl, hs⟩ := connectedSet_positive_tail G C hC a y ha hy hedge
  let f : G.induce Cᶜ →g G := (SimpleGraph.Embedding.induce Cᶜ).toHom
  have hm := twoPathWitness_map f Subtype.val_injective p q hpq
  have hpint : ∀ v, v ∈ (p.map f).support → v ∈ r.support → v = a := by
    intro v hvp hvr
    by_contra hva
    exact component_induced_support G Cᶜ p v hvp (hs v hvr hva)
  have hqint : ∀ v, v ∈ (q.map f).support → v ∈ r.support → v = a := by
    intro v hvq hvr
    by_contra hva
    exact component_induced_support G Cᶜ q v hvq (hs v hvr hva)
  exact ⟨(p.map f).append r, (q.map f).append r,
    twoPathWitness_append_of_support_intersection (p.map f) (q.map f) r hm hr hpint hqint⟩

#print axioms connected_crossing_edge
#print axioms twoBoundary_neighbor
#print axioms twoBoundary_both_neighbors
#print axioms complement_nonroot_closed
#print axioms complement_nonroot_ncard
#print axioms component_complement_induction
end TaskH.Fan
