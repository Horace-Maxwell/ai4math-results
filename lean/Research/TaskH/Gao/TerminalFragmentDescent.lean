import Research.TaskH.Gao.TerminalFragment

/-!
Strict finite descent on actual deleted-vertex components. The complement
of the current interior is connected in the actual original graph, which
prevents a smaller component avoiding the boundary from escaping outside.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem exists_deleted_component_avoiding (G : SimpleGraph V) (c b : V)
    (hbc : b ≠ c) (hbad : ¬(G.induce {v | v ≠ c}).Connected) :
    ∃ D : (G.induce {v | v ≠ c}).ConnectedComponent, b ∉ deletedInterior G c D := by
  classical
  by_contra h
  apply hbad
  have hall : ∀ v : {w : V // w ≠ c},
      (G.induce {w | w ≠ c}).connectedComponentMk v =
        (G.induce {w | w ≠ c}).connectedComponentMk ⟨b, hbc⟩ := by
    intro v
    have hb : b ∈ deletedInterior G c
        ((G.induce {w | w ≠ c}).connectedComponentMk v) := by
      by_contra hb
      exact h ⟨_, hb⟩
    obtain ⟨_hb, hbC⟩ := hb
    exact hbC.symm
  refine { preconnected := ?_, nonempty := ⟨⟨b, hbc⟩⟩ }
  intro a d
  exact ConnectedComponent.exact ((hall a).trans (hall d).symm)

theorem deletedInterior_subset_of_complement_connected (G : SimpleGraph V)
    (I : Set V) (c b : V) (hc : c ∈ I) (hb : b ∉ I)
    (hcomp : (G.induce {v | v ∉ I}).Connected)
    (D : (G.induce {v | v ≠ c}).ConnectedComponent)
    (havoid : b ∉ deletedInterior G c D) : deletedInterior G c D ⊆ I := by
  intro a ha
  by_contra haI
  obtain ⟨hac, haC⟩ := ha
  have hbc : b ≠ c := by
    intro he
    exact hb (he.symm ▸ hc)
  let f : (G.induce {v | v ∉ I}) →g (G.induce {v | v ≠ c}) :=
    { toFun := fun v => ⟨v.1, by
        intro he
        exact v.2 (he.symm ▸ hc)⟩
      map_rel' := fun h => h }
  have hr : (G.induce {v | v ≠ c}).Reachable ⟨a, hac⟩ ⟨b, hbc⟩ :=
    (hcomp ⟨a, haI⟩ ⟨b, hb⟩).map f
  have he : (G.induce {v | v ≠ c}).connectedComponentMk ⟨a, hac⟩ =
      (G.induce {v | v ≠ c}).connectedComponentMk ⟨b, hbc⟩ :=
    ConnectedComponent.sound hr
  exact havoid ⟨hbc, he.symm.trans haC⟩

theorem deletedInterior_strict_descent [Fintype V] (G : SimpleGraph V)
    (I : Set V) (c b : V) (hc : c ∈ I) (hb : b ∉ I)
    (hcomp : (G.induce {v | v ∉ I}).Connected)
    (D : (G.induce {v | v ≠ c}).ConnectedComponent)
    (havoid : b ∉ deletedInterior G c D) :
    (deletedInterior G c D).ncard < I.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite I)
  refine ⟨deletedInterior_subset_of_complement_connected G I c b hc hb hcomp D havoid, ?_⟩
  intro hrev
  exact deletedInterior_root_not_mem G c D (hrev hc)

theorem minimal_deletedInterior_exists [Fintype V] (G : SimpleGraph V) (z : V)
    (C : (G.induce {v | v ≠ z}).ConnectedComponent) :
    ∃ (b : V) (D : (G.induce {v | v ≠ b}).ConnectedComponent),
      deletedInterior G b D ⊆ deletedInterior G z C ∧
        ∀ (c : V) (E : (G.induce {v | v ≠ c}).ConnectedComponent),
          deletedInterior G c E ⊆ deletedInterior G z C →
            (deletedInterior G b D).ncard ≤ (deletedInterior G c E).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (b : V) (D : (G.induce {v | v ≠ b}).ConnectedComponent),
      deletedInterior G b D ⊆ deletedInterior G z C ∧ (deletedInterior G b D).ncard = n
  have hex : ∃ n, P n := ⟨(deletedInterior G z C).ncard, z, C, Set.Subset.rfl, rfl⟩
  obtain ⟨b, D, hsub, hcard⟩ := Nat.find_spec hex
  refine ⟨b, D, hsub, ?_⟩
  intro c E hE
  exact hcard.le.trans (Nat.find_min' hex ⟨c, E, hE, rfl⟩)

theorem minimal_deletedInterior_noncut [Fintype V] (G : SimpleGraph V)
    (Z : Set V) (b : V) (D : (G.induce {v | v ≠ b}).ConnectedComponent)
    (hsub : deletedInterior G b D ⊆ Z)
    (hmin : ∀ (c : V) (E : (G.induce {v | v ≠ c}).ConnectedComponent),
      deletedInterior G c E ⊆ Z →
        (deletedInterior G b D).ncard ≤ (deletedInterior G c E).ncard)
    (hG : G.Connected) :
    ∀ c ∈ deletedInterior G b D, (G.induce {v | v ≠ c}).Connected := by
  intro c hc
  by_contra hbad
  have hb : b ∉ deletedInterior G b D := deletedInterior_root_not_mem G b D
  have hbc : b ≠ c := by
    intro he
    exact hb (he.symm ▸ hc)
  obtain ⟨E, havoid⟩ := exists_deleted_component_avoiding G c b hbc hbad
  have hcomp := deletedInterior_complement_connected G b D hG
  have hEsub := deletedInterior_subset_of_complement_connected G
    (deletedInterior G b D) c b hc hb hcomp E havoid
  have hlt := deletedInterior_strict_descent G
    (deletedInterior G b D) c b hc hb hcomp E havoid
  exact (not_lt_of_ge (hmin c E (hEsub.trans hsub))) hlt

#print axioms exists_deleted_component_avoiding
#print axioms deletedInterior_subset_of_complement_connected
#print axioms deletedInterior_strict_descent
#print axioms minimal_deletedInterior_exists
#print axioms minimal_deletedInterior_noncut
end TaskH.Gao
