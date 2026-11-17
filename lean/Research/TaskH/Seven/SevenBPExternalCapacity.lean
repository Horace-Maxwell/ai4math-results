import Research.TaskH.Seven.SevenBPCycleIndexShift

/-! At most two actual cycle neighbors for an outside vertex of a shortest
long cycle of length at least twenty. The finite support counts have only four
or three displayed positions; all forbidden pairs use real two-ear cycles. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem outside_common_neighbor_even_position (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (n : ℕ) (hn : n ≤ p.length)
    (haz : G.Adj a z) (hnz : G.Adj (p.getVert n) z) : n % 2 = 0 := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  have hc : c a ↔ c (p.getVert n) := by
    have h0 := c.valid haz
    have h1 := c.valid hnz
    cases ha : c a <;> cases hb : c (p.getVert n) <;> cases hz : c z <;> simp_all
  have he := (c.even_length_iff_congr (p.take n)).mpr hc
  have hnEven : Even n := by
    simpa only [Walk.take_length, inf_eq_left.mpr hn] using he
  exact Nat.even_iff.mp hnEven

theorem shortest_external_neighbor_position (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hz : z ∉ p.support)
    (haz : G.Adj a z) (n : ℕ) (hn : n < p.length) (hnz : G.Adj (p.getVert n) z) :
    n = 0 ∨ n = 2 ∨ n + 2 = p.length ∨
      (n ≤ 10 ∧ p.length - n ≤ 10 ∧ n % 2 = 0) := by
  have he := outside_common_neighbor_even_position hb p n (by omega) haz hnz
  have hL := Nat.even_iff.mp (closed_walk_even hb p)
  by_cases h0 : n = 0
  · exact Or.inl h0
  · by_cases h2 : n = 2
    · exact Or.inr (Or.inl h2)
    · by_cases hlast : n + 2 = p.length
      · exact Or.inr (Or.inr (Or.inl hlast))
      · have hd := shortest_cycle_external_ear_distances hb p hp hz n (by omega) (by omega) haz hnz
        exact Or.inr (Or.inr (Or.inr ⟨hd.1, hd.2, he⟩))

theorem external_neighbor_card_of_positions [Fintype V] {a z : V}
    (p : G.Walk a a) (hp : p.IsCycle) {q : ℕ} (A : Finset (Fin q)) (f : Fin q → ℕ)
    (hA : ∀ n < p.length, G.Adj (p.getVert n) z → ∃ i ∈ A, f i = n) :
    (G.neighborFinset z ∩ cycleSupport p).card ≤ A.card := by
  have hsub : G.neighborFinset z ∩ cycleSupport p ⊆ A.image (fun i => p.getVert (f i)) := by
    intro y hy
    have ha := (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hy).1
    rw [cycleSupport_eq_index_image p hp] at hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
    obtain ⟨i, hi, he⟩ := hA j.val j.isLt (by simpa only [hj] using ha.symm)
    exact Finset.mem_image.mpr ⟨i, hi, by simpa only [he] using hj⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le (s := A) (f := fun i => p.getVert (f i)))

def hookTwentyPosition : Fin 4 → ℕ := ![0, 2, 10, 18]

def hookLargePosition (L : ℕ) : Fin 3 → ℕ := ![0, 2, L - 2]

theorem four_hook_position_card (A : Finset (Fin 4))
    (h12 : ¬ (1 ∈ A ∧ 2 ∈ A)) (h13 : ¬ (1 ∈ A ∧ 3 ∈ A))
    (h23 : ¬ (2 ∈ A ∧ 3 ∈ A)) : A.card ≤ 2 := by
  have ht : ∀ A : Finset (Fin 4), ¬ (1 ∈ A ∧ 2 ∈ A) →
      ¬ (1 ∈ A ∧ 3 ∈ A) → ¬ (2 ∈ A ∧ 3 ∈ A) → A.card ≤ 2 := by decide +kernel
  exact ht A h12 h13 h23

theorem three_hook_position_card (A : Finset (Fin 3))
    (h12 : ¬ (1 ∈ A ∧ 2 ∈ A)) : A.card ≤ 2 := by
  have ht : ∀ A : Finset (Fin 3), ¬ (1 ∈ A ∧ 2 ∈ A) → A.card ≤ 2 := by decide +kernel
  exact ht A h12

theorem shortest_external_base_twenty [Fintype V] (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 20)
    (hz : z ∉ p.support) (haz : G.Adj a z) :
    (G.neighborFinset z ∩ cycleSupport p).card ≤ 2 := by
  let A : Finset (Fin 4) := Finset.univ.filter (fun i => G.Adj (p.getVert (hookTwentyPosition i)) z)
  have h12 : ¬ (1 ∈ A ∧ 2 ∈ A) := by
    rintro ⟨h1, h2⟩
    have ha : G.Adj (p.getVert 2) z := (Finset.mem_filter.mp h1).2
    have hb' : G.Adj (p.getVert 10) z := (Finset.mem_filter.mp h2).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 2 10
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have h13 : ¬ (1 ∈ A ∧ 3 ∈ A) := by
    rintro ⟨h1, h3⟩
    have ha : G.Adj (p.getVert 2) z := (Finset.mem_filter.mp h1).2
    have hb' : G.Adj (p.getVert 18) z := (Finset.mem_filter.mp h3).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 2 18
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have h23 : ¬ (2 ∈ A ∧ 3 ∈ A) := by
    rintro ⟨h2, h3⟩
    have ha : G.Adj (p.getVert 10) z := (Finset.mem_filter.mp h2).2
    have hb' : G.Adj (p.getVert 18) z := (Finset.mem_filter.mp h3).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 10 18
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have hc := four_hook_position_card A h12 h13 h23
  have hh := external_neighbor_card_of_positions p hp.1 A hookTwentyPosition (by
    intro n hn hnz
    have hx := shortest_external_neighbor_position hb p hp hz haz n hn hnz
    have he : n = 0 ∨ n = 2 ∨ n = 10 ∨ n = 18 := by omega
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩
    · exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩
    · exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩
    · exact ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩)
  omega

theorem shortest_external_base_at_least_twenty_two [Fintype V] (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : 22 ≤ p.length)
    (hz : z ∉ p.support) (haz : G.Adj a z) :
    (G.neighborFinset z ∩ cycleSupport p).card ≤ 2 := by
  let A : Finset (Fin 3) := Finset.univ.filter
    (fun i => G.Adj (p.getVert (hookLargePosition p.length i)) z)
  have h12 : ¬ (1 ∈ A ∧ 2 ∈ A) := by
    rintro ⟨h1, h2⟩
    have ha : G.Adj (p.getVert 2) z := (Finset.mem_filter.mp h1).2
    have hb' : G.Adj (p.getVert (p.length - 2)) z := (Finset.mem_filter.mp h2).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 2 (p.length - 2)
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have hc := three_hook_position_card A h12
  have hh := external_neighbor_card_of_positions p hp.1 A (hookLargePosition p.length) (by
    intro n hn hnz
    have hx := shortest_external_neighbor_position hb p hp hz haz n hn hnz
    have he : n = 0 ∨ n = 2 ∨ n = p.length - 2 := by omega
    rcases he with rfl | rfl | rfl
    · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩
    · exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩
    · exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩, rfl⟩)
  omega

theorem shortest_external_capacity [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : 20 ≤ p.length) :
    ∀ z ∈ Finset.univ \ cycleSupport p,
      (G.neighborFinset z ∩ cycleSupport p).card ≤ 2 := by
  intro z hz
  have hzout : z ∉ p.support := by
    intro h
    exact (Finset.mem_sdiff.mp hz).2 ((mem_cycleSupport p z).mpr h)
  by_cases hempty : G.neighborFinset z ∩ cycleSupport p = ∅
  · simp only [hempty, Finset.card_empty, Nat.zero_le]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hxs := (mem_cycleSupport p x).mp (Finset.mem_inter.mp hx).2
    have hax : G.Adj x z := ((G.mem_neighborFinset z x).mp (Finset.mem_inter.mp hx).1).symm
    have hrot := shortestLongCycle_rotate p hp x hxs
    have hzrot : z ∉ (p.rotate x hxs).support :=
      fun h => hzout ((Walk.mem_support_rotate_iff p x hxs).mp h)
    have hEven := Nat.even_iff.mp (closed_walk_even hb p)
    have hcase : p.length = 20 ∨ 22 ≤ p.length := by omega
    rcases hcase with h20 | h22
    · have hh := shortest_external_base_twenty hb (p.rotate x hxs) hrot
        (by simpa only [Walk.length_rotate] using h20) hzrot hax
      simpa only [cycleSupport_rotate] using hh
    · have hh := shortest_external_base_at_least_twenty_two hb (p.rotate x hxs) hrot
        (by simpa only [Walk.length_rotate] using h22) hzrot hax
      simpa only [cycleSupport_rotate] using hh

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.outside_common_neighbor_even_position
#print axioms TaskH.Seven.BP.shortest_external_neighbor_position
#print axioms TaskH.Seven.BP.external_neighbor_card_of_positions
#print axioms TaskH.Seven.BP.hookTwentyPosition
#print axioms TaskH.Seven.BP.hookLargePosition
#print axioms TaskH.Seven.BP.four_hook_position_card
#print axioms TaskH.Seven.BP.three_hook_position_card
#print axioms TaskH.Seven.BP.shortest_external_base_twenty
#print axioms TaskH.Seven.BP.shortest_external_base_at_least_twenty_two
#print axioms TaskH.Seven.BP.shortest_external_capacity
