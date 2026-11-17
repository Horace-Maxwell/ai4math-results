import Research.TaskH.Critical

/-!
An actual eight-clique in an originally eight-critical graph spans the graph.
No connectivity or vertex-coverage premise is added: a deleted coloring at any
putative outside point would inject eight mutually adjacent vertices into seven colors.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem critical_eight_clique_complete (hcrit : IsCriticalPlus 7 G)
    (S : Finset V) (hS : G.IsClique S) (hcard : S.card = 8) :
    IsCompleteOfOrder G 8 := by
  classical
  have hspan : ∀ w : V, w ∈ S := by
    intro w
    by_contra hw
    let f : S → {x : V | x ≠ w} := fun z =>
      ⟨z.val, fun he => hw (he ▸ z.property)⟩
    have hpair : Pairwise (fun i j : S =>
        (G.induce {x | x ≠ w}).Adj (f i) (f j)) := by
      intro i j hij
      exact hS i.property j.property (fun he => hij (Subtype.ext he))
    have hle := (critical_colorable_deletedVertex hcrit w).card_le_of_pairwise_adj f hpair
    have hc : Nat.card S = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
    omega
  have htop : G = ⊤ := by
    apply G.eq_top_iff_forall_ne_adj.mpr
    intro x y hxy
    exact hS (hspan x) (hspan y) hxy
  have hSu : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hspan
  have hn : Fintype.card V = 8 := by
    simpa only [hSu, Finset.card_univ] using hcard
  change Nonempty (G ≃g (⊤ : SimpleGraph (Fin 8)))
  rw [htop]
  exact ⟨SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq hn)⟩

end TaskH.Seven

#print axioms TaskH.Seven.critical_eight_clique_complete
