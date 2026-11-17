import Research.TaskH.Seven.SevenBPEighteenChords

/-! True C18 attachment and boundary capacities. Each forbidden hook pair
uses actual two-ear cycles on the same original graph. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

noncomputable def eighteenOutsideHooks (G : SimpleGraph V) (u : Fin 18 → V) (z : V) :
    Finset (Fin 18) := Finset.univ.filter (fun i => G.Adj z (u i))

def hookEighteenPosition : Fin 5 → ℕ := ![0,2,8,10,16]

theorem five_hook_eighteen_position_card (A : Finset (Fin 5))
    (h12 : ¬ (1 ∈ A ∧ 2 ∈ A)) (h14 : ¬ (1 ∈ A ∧ 4 ∈ A))
    (h34 : ¬ (3 ∈ A ∧ 4 ∈ A)) : A.card ≤ 3 := by
  have ht : ∀ A : Finset (Fin 5), ¬ (1 ∈ A ∧ 2 ∈ A) →
      ¬ (1 ∈ A ∧ 4 ∈ A) → ¬ (3 ∈ A ∧ 4 ∈ A) → A.card ≤ 3 := by decide +kernel
  exact ht A h12 h14 h34

theorem shortest_external_base_eighteen [Fintype V] (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length = 18)
    (hz : z ∉ p.support) (haz : G.Adj a z) :
    (G.neighborFinset z ∩ cycleSupport p).card ≤ 3 := by
  let A : Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj (p.getVert (hookEighteenPosition i)) z)
  have h12 : ¬ (1 ∈ A ∧ 2 ∈ A) := by
    rintro ⟨h1,h2⟩
    have ha : G.Adj (p.getVert 2) z := (Finset.mem_filter.mp h1).2
    have hb' : G.Adj (p.getVert 8) z := (Finset.mem_filter.mp h2).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 2 8
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have h14 : ¬ (1 ∈ A ∧ 4 ∈ A) := by
    rintro ⟨h1,h4⟩
    have ha : G.Adj (p.getVert 2) z := (Finset.mem_filter.mp h1).2
    have hb' : G.Adj (p.getVert 16) z := (Finset.mem_filter.mp h4).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 2 16
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have h34 : ¬ (3 ∈ A ∧ 4 ∈ A) := by
    rintro ⟨h3,h4⟩
    have ha : G.Adj (p.getVert 10) z := (Finset.mem_filter.mp h3).2
    have hb' : G.Adj (p.getVert 16) z := (Finset.mem_filter.mp h4).2
    have hh := shortest_cycle_external_pair_distances hb p hp hz 10 16
      (by omega) (by omega) (by omega) (by omega) ha hb'
    omega
  have hc := five_hook_eighteen_position_card A h12 h14 h34
  have hh := external_neighbor_card_of_positions p hp.1 A hookEighteenPosition (by
    intro n hn hnz
    have hx := shortest_external_neighbor_position hb p hp hz haz n hn hnz
    have he : n=0 ∨ n=2 ∨ n=8 ∨ n=10 ∨ n=16 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩,rfl⟩
    · exact ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩,rfl⟩
    · exact ⟨2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩,rfl⟩
    · exact ⟨3,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩,rfl⟩
    · exact ⟨4,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩,rfl⟩)
  omega

theorem cycleSupport_eighteen_image (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    cycleSupport (cycleEighteenWalk G u hu.2) = Finset.univ.image u := by
  ext x
  simp only [mem_cycleSupport, Finset.mem_image, Finset.mem_univ, true_and]
  exact cycleEighteenWalk_support_range G u hu.2 x

theorem eighteen_actual_cycle_neighbor_card [Fintype V] (u : Fin 18 → V)
    (hu : Function.Injective u) (z : V) :
    (G.neighborFinset z ∩ Finset.univ.image u).card = (eighteenOutsideHooks G u z).card := by
  have him : (eighteenOutsideHooks G u z).image u = G.neighborFinset z ∩ Finset.univ.image u := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z (u i)).mpr (Finset.mem_filter.mp hi).2,
        Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    · intro hx
      obtain ⟨hn,hi⟩ := Finset.mem_inter.mp hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.mem_neighborFinset z (u i)).mp hn⟩,rfl⟩
  rw [← him,Finset.card_image_of_injective _ hu]

theorem eighteen_outside_hook_card_le_three [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (z : V) (hz : z ∉ Set.range u) :
    (eighteenOutsideHooks G u z).card ≤ 3 := by
  let p := cycleEighteenWalk G u hu.2
  have hp : ShortestLongCycle p := cycleEighteenWalk_shortest hb h14 h16 u hu
  have hzout : z ∉ p.support := fun h => hz ((cycleEighteenWalk_support_range G u hu.2 z).mp h)
  have hcard : (G.neighborFinset z ∩ cycleSupport p).card = (eighteenOutsideHooks G u z).card := by
    rw [cycleSupport_eighteen_image u hu]
    exact eighteen_actual_cycle_neighbor_card u hu.1 z
  by_cases hempty : eighteenOutsideHooks G u z = ∅
  · simp only [hempty,Finset.card_empty,Nat.zero_le]
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hxi : u i ∈ p.support := (cycleEighteenWalk_support_range G u hu.2 _).mpr ⟨i,rfl⟩
    have hrot := shortestLongCycle_rotate p hp (u i) hxi
    have hzr : z ∉ (p.rotate (u i) hxi).support :=
      fun h => hzout ((Walk.mem_support_rotate_iff p (u i) hxi).mp h)
    have ha : G.Adj (u i) z := (Finset.mem_filter.mp hi).2.symm
    have hh := shortest_external_base_eighteen hb (p.rotate (u i) hxi) hrot
      (by simpa only [Walk.length_rotate] using cycleEighteenWalk_length G u hu.2) hzr ha
    rw [cycleSupport_rotate,hcard] at hh
    exact hh

theorem shortest_internal_base_eighteen [Fintype V] (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hl : p.length=18) :
    (G.neighborFinset a ∩ cycleSupport p).card ≤ 5 := by
  have hh := internal_neighbor_card_of_positions p hp.1 ({1,17,7,9,11} : Finset ℕ) (by
    intro n hn ha
    have hx := shortest_internal_neighbor_position hb p hp n hn ha
    have he : n=1 ∨ n=17 ∨ n=7 ∨ n=9 ∨ n=11 := by omega
    simpa only [Finset.mem_insert,Finset.mem_singleton] using he)
  have hc : ({1,17,7,9,11} : Finset ℕ).card=5 := by decide
  omega

theorem eighteen_internal_degree_le_five [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    ∀ x ∈ Finset.univ.image u, (G.neighborFinset x ∩ Finset.univ.image u).card ≤ 5 := by
  have hbound (p : G.Walk (u 0) (u 0)) (hp : ShortestLongCycle p)
      (hl : p.length = 18) (hs : cycleSupport p = Finset.univ.image u) :
      ∀ x ∈ Finset.univ.image u, (G.neighborFinset x ∩ Finset.univ.image u).card ≤ 5 := by
    intro x hx
    have hxc : x ∈ cycleSupport p :=
      (congrArg (fun Q : Finset V => x ∈ Q) hs).mpr hx
    have hxs : x ∈ p.support := (mem_cycleSupport p x).mp hxc
    have hrot : ShortestLongCycle (p.rotate x hxs) :=
      shortestLongCycle_rotate p hp x hxs
    have hlen : (p.rotate x hxs).length = 18 :=
      (Walk.length_rotate p x hxs).trans hl
    have hh : (G.neighborFinset x ∩ cycleSupport (p.rotate x hxs)).card ≤ 5 :=
      shortest_internal_base_eighteen hb (p.rotate x hxs) hrot hlen
    have hsrot : cycleSupport (p.rotate x hxs) = Finset.univ.image u :=
      (cycleSupport_rotate p x hxs).trans hs
    exact (congrArg (fun Q : Finset V => (G.neighborFinset x ∩ Q).card ≤ 5) hsrot).mp hh
  exact hbound (cycleEighteenWalk G u hu.2) (cycleEighteenWalk_shortest hb h14 h16 u hu)
    (cycleEighteenWalk_length G u hu.2) (cycleSupport_eighteen_image u hu)

theorem eighteen_each_cycle_vertex_two_outside [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (hd : ∀ x : V,7≤G.degree x) :
    ∀ x ∈ Finset.univ.image u, 2 ≤ (G.neighborFinset x \ Finset.univ.image u).card := by
  intro x hx
  have hi := eighteen_internal_degree_le_five hb h14 h16 u hu x hx
  have hp := boundary_degree_partition (G:=G) (Finset.univ.image u) x
  have hdeg := hd x
  omega

theorem eighteen_outside_degree_ge_four [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (z : V) (hz : z ∉ Set.range u)
    (hd : 7≤G.degree z) : 4 ≤ (G.neighborFinset z \ Finset.univ.image u).card := by
  have hh := eighteen_outside_hook_card_le_three hb h14 h16 u hu z hz
  have hp := boundary_degree_partition (G:=G) (Finset.univ.image u) z
  rw [eighteen_actual_cycle_neighbor_card u hu.1 z] at hp
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteenOutsideHooks
#print axioms TaskH.Seven.BP.hookEighteenPosition
#print axioms TaskH.Seven.BP.five_hook_eighteen_position_card
#print axioms TaskH.Seven.BP.shortest_external_base_eighteen
#print axioms TaskH.Seven.BP.cycleSupport_eighteen_image
#print axioms TaskH.Seven.BP.eighteen_actual_cycle_neighbor_card
#print axioms TaskH.Seven.BP.eighteen_outside_hook_card_le_three
#print axioms TaskH.Seven.BP.shortest_internal_base_eighteen
#print axioms TaskH.Seven.BP.eighteen_internal_degree_le_five
#print axioms TaskH.Seven.BP.eighteen_each_cycle_vertex_two_outside
#print axioms TaskH.Seven.BP.eighteen_outside_degree_ge_four
