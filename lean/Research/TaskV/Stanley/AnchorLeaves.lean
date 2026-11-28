import Research.TaskV.Stanley.AnchorCuts

namespace StanleyContinuation
open SimpleGraph Finset
open scoped BigOperators
noncomputable section

theorem tree_compl_singleton_iff_leaf {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) (hn : 2 ≤ n) (v : Fin n) :
    (G.induce ({v}ᶜ : Set (Fin n))).Connected ↔ v ∉ core G := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [outsideCore_iff_uniqueAdj]
  constructor
  · intro hc
    obtain ⟨u,hu⟩ := hG.connected.preconnected.exists_adj_of_nontrivial v
    refine ⟨u,hu,?_⟩
    intro w hw
    by_contra hwne
    let D := G.deleteEdges {s(v,u)}
    let m : G.induce ({v}ᶜ : Set (Fin n)) →g D :=
      { toFun := fun x => x.val
        map_rel' := by
          intro x y h
          refine SimpleGraph.deleteEdges_adj.mpr ⟨h,?_⟩
          have hx : x.val ≠ v := x.property
          have hy : y.val ≠ v := y.property
          simp [hx,hy] }
    have wu : D.Reachable w u := (hc.preconnected ⟨w,hw.ne.symm⟩ ⟨u,hu.ne.symm⟩).map m
    have hwalk : D.Adj v w := SimpleGraph.deleteEdges_adj.mpr ⟨hw,by
      simp [hwne,hu.ne]⟩
    exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hu))
      (hwalk.reachable.trans wu)
  · intro h
    exact hG.connected.induce_compl_singleton_of_degree_eq_one (G.degree_eq_one_iff_existsUnique_adj.mpr h)

theorem singleton_count_eq_leaf_count {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsTree) (hn : 2 ≤ n) :
    connectedCoefficient G 2 (binarySizes n 1) = (univ \ core G).card := by
  classical
  have hf (s : Finset (Fin n)) : Nat.card ↥s = s.card := by simp [Nat.card_eq_fintype_card]
  rw [connectedCoefficient_two, ← hf (univ \ core G)]
  apply Nat.card_congr
  let singletonCut : ↥(univ \ core G) → CutOfSize G 1 := fun x =>
    ⟨{x.val}, card_singleton _, by
      rw [coe_singleton]
      exact (SimpleGraph.connected_iff _).mpr ⟨fun _ _ => Reachable.of_subsingleton, inferInstance⟩,
      by
        rw [coe_singleton]
        exact (tree_compl_singleton_iff_leaf hG hn _).mpr (mem_sdiff.mp x.property).2⟩
  refine (Equiv.ofBijective singletonCut ⟨?_, ?_⟩).symm
  · intro x y he
    exact Subtype.ext (Finset.singleton_injective (congrArg Subtype.val he))
  · intro side
    obtain ⟨v,hv⟩ := card_eq_one.mp side.property.1
    have hcompl := side.property.2.2
    rw [hv, coe_singleton] at hcompl
    have leaf := (tree_compl_singleton_iff_leaf hG hn v).mp hcompl
    exact ⟨⟨v,mem_sdiff.mpr ⟨mem_univ _,leaf⟩⟩, Subtype.ext hv.symm⟩

theorem same_core_card {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.IsTree) (hH : H.IsTree) (hne : n=m) (hn : 2 ≤ n) (eq : SameConnected G H) :
    (core G).card = (core H).card := by
  subst m
  have h := eq 2 (binarySizes n 1)
  rw [singleton_count_eq_leaf_count G hG hn, singleton_count_eq_leaf_count H hH hn] at h
  have g := card_sdiff_add_card_eq_card (subset_univ (core G))
  have j := card_sdiff_add_card_eq_card (subset_univ (core H))
  omega

end
end StanleyContinuation
