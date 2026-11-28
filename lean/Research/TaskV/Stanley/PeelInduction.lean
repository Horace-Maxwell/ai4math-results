import Research.TaskV.Stanley.PeelReattach

namespace StanleyContinuation
open SimpleGraph
open scoped Classical
noncomputable section

private theorem colored_tree_induction (n : ℕ) :
    ∀ {V W : Type*} [Fintype V] [Fintype W] (J : SimpleGraph V) (K : SimpleGraph W)
      (w : V → ℕ) (z : W → ℕ), Fintype.card V = n → J.IsTree → K.IsTree →
      atMostOneRepeatedLeaf J w → SameInventory J w K z → ∃ e : J ≃g K, ∀ x, w x = z (e x) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V W _ _ J K w z size tree tree' few same
    cases subsingleton_or_nontrivial V with
    | inl small =>
      let fiber (c : ℕ) := Classical.choice (Finite.card_eq.mp (singleton_inventory same c))
      let f := Equiv.ofFiberEquiv fiber
      let e : J ≃g K := {
        toEquiv := f
        map_rel_iff' := by
          intro x y
          rw [small.elim x y]
          simp }
      exact ⟨e,fun x => (Equiv.ofFiberEquiv_map fiber x).symm⟩
    | inr nt =>
      let := nt
      obtain ⟨a,v,ua,av,la⟩ := choose_tagged_leaf tree few
      obtain ⟨b,u,bu,ab,ub,lb,uv,smaller⟩ := peel_step same ua av la
      have size' : Fintype.card (Away a) = n-1 := by
        change Fintype.card {x : V // ¬ x = a} = n-1
        rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,size]
      have hn : 1 < n := size ▸ Fintype.one_lt_card
      obtain ⟨e,colors⟩ := ih (n-1) (by omega) (pruned J a) (pruned K b) _ _ size'
        (tree_after_deletion tree av la) (tree_after_deletion tree' bu lb)
        (atMostOne_after_deletion few ua av la) smaller
      exact reattach_tagged_leaf av bu la lb ab ub uv e colors

/-- The connected-set color inventories distinguish any finite colored tree with at most
one leaf of repeated color from every finite colored tree. -/
theorem colored_tree_reconstruction {V W : Type*} [Fintype V] [Fintype W]
    {J : SimpleGraph V} {K : SimpleGraph W} {w : V → ℕ} {z : W → ℕ}
    (tree : J.IsTree) (tree' : K.IsTree) (few : atMostOneRepeatedLeaf J w)
    (same : SameInventory J w K z) : ∃ e : J ≃g K, ∀ x, w x = z (e x) :=
  colored_tree_induction _ J K w z rfl tree tree' few same

end
end StanleyContinuation
