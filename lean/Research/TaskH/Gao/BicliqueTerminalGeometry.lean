import Research.TaskH.Gao.BicliqueSingletonFirstGeometry
import Research.TaskH.Gao.ComponentTerminalTail
import Research.TaskH.Gao.ActualSetCrossing
import Research.TaskH.Gao.RootRegionQuotient

/-! The actual terminal fragment and its real B-minus-x boundary, primary619--631. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def g4Block (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) : Set V :=
  componentRegion C (fragmentBlock I b)

def g4Boundary (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) : Set V :=
  {z | z ∈ B \ {x} ∧ ∃ d ∈ I, G.Adj (componentVertex C d) z}

theorem g4_root_mem (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) :
    componentVertex C b ∈ g4Block G A B y C I b := ⟨b, Or.inl rfl, rfl⟩

theorem g4_nonroot_interior (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (a : V)
    (ha : a ∈ g4Block G A B y C I b) (hab : a ≠ componentVertex C b) :
    ∃ d ∈ I, componentVertex C d = a := by
  obtain ⟨d, hd, he⟩ := ha
  rcases hd with hdb | hdI
  · exact False.elim (hab (he.symm.trans (congrArg (componentVertex C) hdb)))
  · exact ⟨d, hdI, he⟩

theorem g4_block_disjoint_core (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) :
    Disjoint (g4Block G A B y C I b) (bicliqueSingletonCore A B y) :=
  componentRegion_disjoint C (fragmentBlock I b)

theorem g4_block_boundary_disjoint (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) :
    Disjoint (g4Block G A B y C I b) (g4Boundary G A B x y C I) := by
  apply Set.disjoint_left.mpr
  intro z hzN hzS
  exact Set.disjoint_left.mp (g4_block_disjoint_core G A B y C I b) hzN
    (Or.inl (Or.inr hzS.1.1))

theorem g4_full_neighbor_cover (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a) :
    ∀ a ∈ g4Block G A B y C I b, a ≠ componentVertex C b →
      ∀ z, G.Adj a z → z ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I := by
  intro a ha hab z e
  rcases component_fragment_original_cover C I b hT a ha hab z e with hzN | hzK
  · exact Or.inl hzN
  · obtain ⟨d, hdI, he⟩ := g4_nonroot_interior G A B y C I b a ha hab
    have he' : d.1.1 = a := he
    have edz : G.Adj d.1.1 z := Eq.mpr (congrArg (fun v : V => G.Adj v z) he') e
    have hzA : z ∉ A := fun hzA => hnoA d hdI z hzA edz
    have hzx : z ≠ x := by
      intro heq
      have exd : G.Adj x d.1.1 :=
        Eq.mp (congrArg (fun v : V => G.Adj v d.1.1) heq) edz.symm
      have hdA : d.1.1 ∈ A :=
        Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNx) exd
      exact d.1.2 (Or.inl (Or.inl hdA))
    have hzy : z ≠ y := by
      intro heq
      have eyd : G.Adj y d.1.1 :=
        Eq.mp (congrArg (fun v : V => G.Adj v d.1.1) heq) edz.symm
      have hdA : d.1.1 ∈ A :=
        Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNy) eyd
      exact d.1.2 (Or.inl (Or.inl hdA))
    have hzB : z ∈ B := by
      rcases hzK with (hzA' | hzB) | hzY
      · exact False.elim (hzA hzA')
      · exact hzB
      · exact False.elim (hzy hzY)
    exact Or.inr ⟨⟨hzB, hzx⟩, d, hdI, edz⟩

theorem g4_boundary_nonempty [Fintype V] (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hG : TwoConnected G) (hx : x ∈ B)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a) :
    (g4Boundary G A B x y C I).Nonempty := by
  let U := componentRegion C I
  let br := componentVertex C b
  obtain ⟨d, hdI⟩ := hT.1
  have hdb : componentVertex C d ≠ br := by
    intro he
    have he' : d = b := componentVertex_injective C he
    exact hT.2.1 (Eq.mp (congrArg (fun v : C.supp => v ∈ I) he') hdI)
  have hxb : x ≠ br := by
    intro he
    have hbK : br ∈ bicliqueSingletonCore A B y :=
      Eq.mp (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inl (Or.inr hx))
    exact b.1.2 hbK
  let F := G.induce {v : V | v ≠ br}
  let U' : Set {v : V // v ≠ br} := {v | v.1 ∈ U}
  have hxU : x ∉ U := by
    intro hxU
    exact Set.disjoint_left.mp (componentRegion_disjoint C I) hxU (Or.inl (Or.inr hx))
  obtain ⟨a, ha, z, hz, e⟩ := reachable_crosses_vertex_set F U'
    ⟨componentVertex C d, hdb⟩ ⟨x, hxb⟩ ⟨d, hdI, rfl⟩ hxU
    ((hG.2.2 br) ⟨componentVertex C d, hdb⟩ ⟨x, hxb⟩)
  have haN : a.1 ∈ g4Block G A B y C I b := by
    obtain ⟨d', hd', he⟩ := ha
    exact ⟨d', Or.inr hd', he⟩
  rcases g4_full_neighbor_cover G A B x y C I b hT hNx hNy hnoA a.1 haN a.2 z.1 e with hzN | hzS
  · obtain ⟨d', hd', he⟩ := g4_nonroot_interior G A B y C I b z.1 hzN z.2
    exact False.elim (hz ⟨d', hd', he⟩)
  · exact ⟨z.1, hzS⟩

theorem g4_block_connected (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b) :
    (G.induce (g4Block G A B y C I b)).Connected := by
  exact (componentRegionGraphIso C (fragmentBlock I b)).connected_iff.mp hT.2.2.2.2.2.1

theorem g4_block_card_ge_two [Fintype V] (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b) :
    2 ≤ (g4Block G A B y C I b).ncard := by
  obtain ⟨d, hdI⟩ := hT.1
  have hdb : componentVertex C d ≠ componentVertex C b := by
    intro he
    exact hT.2.1 (Eq.mp (congrArg (fun v : C.supp => v ∈ I)
      (componentVertex_injective C he)) hdI)
  have hsub : ({componentVertex C d, componentVertex C b} : Set V) ⊆ g4Block G A B y C I b := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact ⟨d, Or.inr hdI, he.symm⟩
    · have he' : z = componentVertex C b := he
      exact ⟨b, Or.inl rfl, he'.symm⟩
  have hn := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hdb] at hn
  exact hn

theorem g4_boundary_card [Fintype V] (G : SimpleGraph V) (A B : Set V) (x y : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) (I : Set C.supp)
    (hx : x ∈ B) (hB : B.ncard = s + 1) :
    (g4Boundary G A B x y C I).ncard ≤ s := by
  have hn := Set.ncard_le_ncard (show g4Boundary G A B x y C I ⊆ B \ {x} from fun _ h => h.1)
  rw [Set.ncard_sdiff_singleton_of_mem hx, hB] at hn
  omega

#print axioms g4Block
#print axioms g4Boundary
#print axioms g4_root_mem
#print axioms g4_nonroot_interior
#print axioms g4_block_disjoint_core
#print axioms g4_block_boundary_disjoint
#print axioms g4_full_neighbor_cover
#print axioms g4_boundary_nonempty
#print axioms g4_block_connected
#print axioms g4_block_card_ge_two
#print axioms g4_boundary_card
end TaskH.Gao
