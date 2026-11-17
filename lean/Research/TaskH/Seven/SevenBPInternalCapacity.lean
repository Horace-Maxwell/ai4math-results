import Research.TaskH.Seven.SevenBPTwoEar
import Research.TaskH.Seven.SevenBPBoundaryBudget

/-! Actual cycle-support enumeration and internal-neighbor capacities for a
shortest long cycle. The numerical position sets are derived from actual
chord cycles and bipartite parity before being transported to graph neighbors. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def cycleSupport {a : V} (p : G.Walk a a) : Finset V := p.support.toFinset

theorem mem_cycleSupport {a : V} (p : G.Walk a a) (x : V) :
    x ∈ cycleSupport p ↔ x ∈ p.support := by
  simp only [cycleSupport, List.mem_toFinset]

theorem cycleSupport_eq_index_image {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    cycleSupport p = Finset.univ.image (fun i : Fin p.length => p.getVert i.val) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hnx, hn⟩ := Walk.mem_support_iff_exists_getVert.mp ((mem_cycleSupport p x).mp hx)
    by_cases hlt : n < p.length
    · exact Finset.mem_image.mpr ⟨⟨n, hlt⟩, Finset.mem_univ _, hnx⟩
    · have hnL : n = p.length := by omega
      have hxa : a = x := by simpa only [hnL, Walk.getVert_length] using hnx
      exact Finset.mem_image.mpr ⟨⟨0, by have hh := hp.three_le_length; omega⟩,
        Finset.mem_univ _, by simpa only [Walk.getVert_zero] using hxa⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_cycleSupport p _).mpr (p.getVert_mem_support i.val)

theorem cycleSupport_card {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    (cycleSupport p).card = p.length := by
  have hi : Function.Injective (fun i : Fin p.length => p.getVert i.val) := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) he
  rw [cycleSupport_eq_index_image p hp,
    Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

theorem cycleSupport_rotate {a : V} (p : G.Walk a a) (x : V) (hx : x ∈ p.support) :
    cycleSupport (p.rotate x hx) = cycleSupport p := by
  ext y
  simp only [mem_cycleSupport, Walk.mem_support_rotate_iff]

theorem shortestLongCycle_rotate {a : V} (p : G.Walk a a)
    (hp : ShortestLongCycle p) (x : V) (hx : x ∈ p.support) :
    ShortestLongCycle (p.rotate x hx) := by
  refine ⟨hp.1.rotate hx, ?_, ?_⟩
  · simpa only [Walk.length_rotate] using hp.2.1
  · intro b q hq h14
    simpa only [Walk.length_rotate] using hp.2.2 b q hq h14

theorem shortest_internal_neighbor_position (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (n : ℕ) (hn : n < p.length)
    (ha : G.Adj a (p.getVert n)) :
    n = 1 ∨ n + 1 = p.length ∨
      (n ≤ 11 ∧ p.length - n ≤ 11 ∧ n % 2 = 1) := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  have ho := adjacent_path_index_odd c p n (by omega) ha
  by_cases h1 : n = 1
  · exact Or.inl h1
  · by_cases hlast : n + 1 = p.length
    · exact Or.inr (Or.inl hlast)
    · have hd := shortest_cycle_chord_distances hb p hp n (by omega) (by omega) ha
      exact Or.inr (Or.inr ⟨hd.1, hd.2, ho⟩)

theorem internal_neighbor_card_of_positions [Fintype V] {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) (A : Finset ℕ)
    (hA : ∀ n < p.length, G.Adj a (p.getVert n) → n ∈ A) :
    (G.neighborFinset a ∩ cycleSupport p).card ≤ A.card := by
  have hsub : G.neighborFinset a ∩ cycleSupport p ⊆ A.image p.getVert := by
    intro y hy
    have ha := (G.mem_neighborFinset a y).mp (Finset.mem_inter.mp hy).1
    rw [cycleSupport_eq_index_image p hp] at hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
    have hn := hA i.val i.isLt (by simpa only [hi] using ha)
    exact Finset.mem_image.mpr ⟨i.val, hn, hi⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le (s := A) (f := p.getVert))

theorem shortest_internal_base_twenty [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 20) :
    (G.neighborFinset a ∩ cycleSupport p).card ≤ 4 := by
  have hh := internal_neighbor_card_of_positions p hp.1 ({1, 19, 9, 11} : Finset ℕ) (by
    intro n hn ha
    have hx := shortest_internal_neighbor_position hb p hp n hn ha
    have he : n = 1 ∨ n = 19 ∨ n = 9 ∨ n = 11 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he)
  have hc : ({1, 19, 9, 11} : Finset ℕ).card = 4 := by decide
  omega

theorem shortest_internal_base_twenty_two [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 22) :
    (G.neighborFinset a ∩ cycleSupport p).card ≤ 3 := by
  have hh := internal_neighbor_card_of_positions p hp.1 ({1, 21, 11} : Finset ℕ) (by
    intro n hn ha
    have hx := shortest_internal_neighbor_position hb p hp n hn ha
    have he : n = 1 ∨ n = 21 ∨ n = 11 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he)
  have hc : ({1, 21, 11} : Finset ℕ).card = 3 := by decide
  omega

theorem shortest_internal_base_at_least_twenty_four [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : 24 ≤ p.length) :
    (G.neighborFinset a ∩ cycleSupport p).card ≤ 2 := by
  have hh := internal_neighbor_card_of_positions p hp.1 ({1, p.length - 1} : Finset ℕ) (by
    intro n hn ha
    have hx := shortest_internal_neighbor_position hb p hp n hn ha
    have he : n = 1 ∨ n = p.length - 1 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he)
  have hc : ({1, p.length - 1} : Finset ℕ).card ≤ 2 := by
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  omega

theorem shortest_internal_capacity_twenty [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 20) :
    ∀ x ∈ cycleSupport p, (G.neighborFinset x ∩ cycleSupport p).card ≤ 4 := by
  intro x hx
  have hxs := (mem_cycleSupport p x).mp hx
  have hrot := shortestLongCycle_rotate p hp x hxs
  have hh := shortest_internal_base_twenty hb (p.rotate x hxs) hrot
    (by simpa only [Walk.length_rotate] using hl)
  simpa only [cycleSupport_rotate] using hh

theorem shortest_internal_capacity_twenty_two [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 22) :
    ∀ x ∈ cycleSupport p, (G.neighborFinset x ∩ cycleSupport p).card ≤ 3 := by
  intro x hx
  have hxs := (mem_cycleSupport p x).mp hx
  have hrot := shortestLongCycle_rotate p hp x hxs
  have hh := shortest_internal_base_twenty_two hb (p.rotate x hxs) hrot
    (by simpa only [Walk.length_rotate] using hl)
  simpa only [cycleSupport_rotate] using hh

theorem shortest_internal_capacity_at_least_twenty_four [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : 24 ≤ p.length) :
    ∀ x ∈ cycleSupport p, (G.neighborFinset x ∩ cycleSupport p).card ≤ 2 := by
  intro x hx
  have hxs := (mem_cycleSupport p x).mp hx
  have hrot := shortestLongCycle_rotate p hp x hxs
  have hh := shortest_internal_base_at_least_twenty_four hb (p.rotate x hxs) hrot
    (by simpa only [Walk.length_rotate] using hl)
  simpa only [cycleSupport_rotate] using hh

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.cycleSupport
#print axioms TaskH.Seven.BP.mem_cycleSupport
#print axioms TaskH.Seven.BP.cycleSupport_eq_index_image
#print axioms TaskH.Seven.BP.cycleSupport_card
#print axioms TaskH.Seven.BP.cycleSupport_rotate
#print axioms TaskH.Seven.BP.shortestLongCycle_rotate
#print axioms TaskH.Seven.BP.shortest_internal_neighbor_position
#print axioms TaskH.Seven.BP.internal_neighbor_card_of_positions
#print axioms TaskH.Seven.BP.shortest_internal_base_twenty
#print axioms TaskH.Seven.BP.shortest_internal_base_twenty_two
#print axioms TaskH.Seven.BP.shortest_internal_base_at_least_twenty_four
#print axioms TaskH.Seven.BP.shortest_internal_capacity_twenty
#print axioms TaskH.Seven.BP.shortest_internal_capacity_twenty_two
#print axioms TaskH.Seven.BP.shortest_internal_capacity_at_least_twenty_four
