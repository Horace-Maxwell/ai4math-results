import Research.TaskH.Critical

/-!
A six-clique in a genuinely six-critical graph spans the graph. This uses
criticality for actual deleted vertices and an injective-coloring obstruction,
so it does not assume connectedness or a covering of the vertex set.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem critical_six_clique_complete (hcrit : IsCriticalPlus 5 G)
    (S : Finset V) (hS : G.IsClique S) (hcard : S.card = 6) :
    IsCompleteOfOrder G 6 := by
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
    have hc : Nat.card S = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
    omega
  have htop : G = ⊤ := by
    apply G.eq_top_iff_forall_ne_adj.mpr
    intro x y hxy
    exact hS (hspan x) (hspan y) hxy
  have hSu : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hspan
  have hn : Fintype.card V = 6 := by simpa only [hSu, Finset.card_univ] using hcard
  change Nonempty (G ≃g (⊤ : SimpleGraph (Fin 6)))
  rw [htop]
  exact ⟨SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq hn)⟩

end TaskH.Five

#print axioms TaskH.Five.critical_six_clique_complete
