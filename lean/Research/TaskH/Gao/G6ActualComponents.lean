import Research.TaskH.Gao.G6FourTags

/-! H is the union of the ACTUAL outside components touching the actual w. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def g6Outside (A B : Set V) (y : V) : Set V :=
  {v | v ∉ A ∪ B ∧ v ≠ y}

def g6SelectedRegion (G : SimpleGraph V) (A B : Set V) (y w : V) : Set V :=
  {v | ∃ hv : v ∈ g6Outside A B y, ∃ z : g6Outside A B y,
    G.Adj w z.1 ∧ (G.induce (g6Outside A B y)).Reachable ⟨v, hv⟩ z}

theorem g6Selected_subset_outside (G : SimpleGraph V) (A B : Set V) (y w : V) :
    g6SelectedRegion G A B y w ⊆ g6Outside A B y := by
  rintro v ⟨hv, _⟩
  exact hv

theorem g6Selected_iff_actual_component (G : SimpleGraph V) (A B : Set V) (y w v : V) :
    v ∈ g6SelectedRegion G A B y w ↔
      ∃ hv : v ∈ g6Outside A B y,
        ∃ C : (G.induce (g6Outside A B y)).ConnectedComponent,
          (⟨v, hv⟩ : g6Outside A B y) ∈ C.supp ∧
            ∃ z : g6Outside A B y, z ∈ C.supp ∧ G.Adj w z.1 := by
  constructor
  · rintro ⟨hv, z, ewz, hp⟩
    let C := (G.induce (g6Outside A B y)).connectedComponentMk ⟨v, hv⟩
    refine ⟨hv, C, rfl, z, ?_, ewz⟩
    exact ConnectedComponent.sound hp.symm
  · rintro ⟨hv, C, hvC, z, hzC, ewz⟩
    exact ⟨hv, z, ewz, C.reachable_of_mem_supp hvC hzC⟩

theorem g6Selected_contains_w_neighbor (G : SimpleGraph V) (A B : Set V) (y w v : V)
    (hv : v ∈ g6Outside A B y) (e : G.Adj w v) :
    v ∈ g6SelectedRegion G A B y w := ⟨hv, ⟨v, hv⟩, e, Reachable.rfl⟩

theorem g6Selected_closed_outside (G : SimpleGraph V) (A B : Set V) (y w : V)
    (v d : V) (hv : v ∈ g6SelectedRegion G A B y w)
    (hd : d ∈ g6Outside A B y) (e : G.Adj v d) :
    d ∈ g6SelectedRegion G A B y w := by
  obtain ⟨hv', z, ewz, hp⟩ := hv
  have edv : (G.induce (g6Outside A B y)).Adj ⟨d, hd⟩ ⟨v, hv'⟩ := e.symm
  exact ⟨hd, z, ewz, edv.reachable.trans hp⟩

theorem g6Selected_disjoint_core (G : SimpleGraph V) (A B : Set V) (y w : V) :
    Disjoint (g6SelectedRegion G A B y w) (A ∪ B) := by
  apply Set.disjoint_left.mpr
  intro v hv hvQ
  exact (g6Selected_subset_outside G A B y w hv).1 hvQ

theorem g6Selected_neighbor_cover (G : SimpleGraph V) (A B : Set V) (y w : V)
    (hNy : G.neighborSet y = A) :
    ∀ v ∈ g6SelectedRegion G A B y w, ∀ d, G.Adj v d →
      d ∈ g6SelectedRegion G A B y w ∨ d ∈ A ∪ B := by
  intro v hv d e
  by_cases hdQ : d ∈ A ∪ B
  · exact Or.inr hdQ
  · have hdy : d ≠ y := by
      intro he
      have hvA : v ∈ A := hNy ▸ (he ▸ e).symm
      exact (g6Selected_subset_outside G A B y w hv).1 (Or.inl hvA)
    exact Or.inl (g6Selected_closed_outside G A B y w v d hv ⟨hdQ, hdy⟩ e)

theorem g6Selected_neighbor_cover_without_x (G : SimpleGraph V) (A B : Set V)
    (x y w : V) (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A) :
    ∀ v ∈ g6SelectedRegion G A B y w, ∀ d, G.Adj v d →
      d ∈ g6SelectedRegion G A B y w ∨ d ∈ A ∨ d ∈ B \ ({x} : Set V) := by
  intro v hv d e
  rcases g6Selected_neighbor_cover G A B y w hNy v hv d e with hdH | hdQ
  · exact Or.inl hdH
  · rcases hdQ with hdA | hdB
    · exact Or.inr (Or.inl hdA)
    · have hdx : d ≠ x := by
        intro he
        have hvA : v ∈ A := hNx ▸ (he ▸ e).symm
        exact (g6Selected_subset_outside G A B y w hv).1 (Or.inl hvA)
      exact Or.inr (Or.inr ⟨hdB, hdx⟩)

theorem g6_w_neighbor_cover (G : SimpleGraph V) (A B : Set V) (y w : V)
    (hwB : w ∈ B)
    (hind : ∀ a ∈ B, ∀ b ∈ B, ¬G.Adj a b)
    (hNy : G.neighborSet y = A) (hAB : Disjoint A B) :
    G.neighborSet w ⊆ g6SelectedRegion G A B y w ∪ A := by
  intro v e
  by_cases hvA : v ∈ A
  · exact Or.inr hvA
  · have hvB : v ∉ B := fun hvB => hind w hwB v hvB e
    have hvy : v ≠ y := by
      intro he
      have hwA : w ∈ A := hNy ▸ (he ▸ e).symm
      exact Set.disjoint_left.mp hAB hwA hwB
    exact Or.inl (g6Selected_contains_w_neighbor G A B y w v
      ⟨fun hv => hv.elim hvA hvB, hvy⟩ e)

theorem g6_actual_boundary_nonempty (G : SimpleGraph V) (H A : Set V) (u : V)
    (h2 : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
      (∃ h ∈ H, G.Adj a h) ∧ ∃ h ∈ H, G.Adj b h) :
    (g6Boundary G H A u).Nonempty := by
  obtain ⟨a, ha, b, hb, hab, haH, hbH⟩ := h2
  by_cases hau : a = u
  · exact ⟨b, hb, fun hbu => hab (hau.trans hbu.symm), hbH⟩
  · exact ⟨a, ha, hau, haH⟩

#print axioms g6Outside
#print axioms g6SelectedRegion
#print axioms g6Selected_subset_outside
#print axioms g6Selected_iff_actual_component
#print axioms g6Selected_contains_w_neighbor
#print axioms g6Selected_closed_outside
#print axioms g6Selected_disjoint_core
#print axioms g6Selected_neighbor_cover
#print axioms g6Selected_neighbor_cover_without_x
#print axioms g6_w_neighbor_cover
#print axioms g6_actual_boundary_nonempty
end TaskH.Gao
