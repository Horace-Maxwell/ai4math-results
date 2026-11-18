import Research.TaskH.Gao.BicliqueLexicographicSelection
import Research.TaskH.Gao.CasebiActualNoLeaf

/-! Exact original neighbor sets forced by a real y-leaf, an actual outside
x-neighbor, both genuine biclique cross edges, and the original root-degree
orientation. These local data are derived in the original-domain wrapper. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem actual_component_root_leaf_neighbor_cover (G : SimpleGraph V)
    (Q : Set V) (C : (G.induce Qᶜ).ConnectedComponent) (yr b : C.supp)
    (y : V) (hY : componentVertex C yr = y)
    (hleaf : C.toSimpleGraph.neighborSet yr = {b}) :
    ∀ z, G.Adj y z → z ∈ Q ∨ z = componentVertex C b := by
  classical
  subst y
  intro z eyz
  by_cases hz : z ∈ Q
  · exact Or.inl hz
  · have e : (G.induce Qᶜ).Adj yr.1 ⟨z, hz⟩ := eyz
    let zr : C.supp := ⟨⟨z, hz⟩, C.mem_supp_of_adj_mem_supp yr.2 e⟩
    have ez : zr ∈ C.toSimpleGraph.neighborSet yr := eyz
    rw [hleaf] at ez
    have he : zr = b := ez
    exact Or.inr (congrArg (componentVertex C) he)

theorem biclique_leaf_root_neighbor_sets [Fintype V]
    (G : SimpleGraph V) (A : Set V) (x y a b p : V)
    (hA : 2 ≤ A.ncard) (hxA : x ∉ A) (hpA : p ∉ A) (hbA : b ∉ A)
    (hax : a ≠ x) (hab : a ≠ b)
    (hxCross : ∀ u ∈ A, G.Adj x u) (haCross : ∀ u ∈ A, G.Adj a u)
    (exp : G.Adj x p)
    (hcover : ∀ z, G.Adj y z → z ∈ A ∨ z = a ∨ z = b)
    (htriY : CasebiNoRootTriangle G y x)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard) :
    G.neighborSet x = insert p A ∧ G.neighborSet y = insert b A := by
  classical
  have hsubX : insert p A ⊆ G.neighborSet x := by
    intro z hz
    rcases hz with he | hzA
    · exact Eq.mpr (congrArg (fun z : V => G.Adj x z) he) exp
    · exact hxCross z hzA
  have hcardP : (insert p A).ncard = A.ncard + 1 := Set.ncard_insert_of_notMem hpA
  have hlow : A.ncard + 1 ≤ (G.neighborSet x).ncard := by
    rw [← hcardP]
    exact Set.ncard_le_ncard hsubX
  have hya : ¬G.Adj y a := by
    intro eya
    have hnoA : ∀ u ∈ A, ¬G.Adj y u := by
      intro u hu eyu
      have hux : u ≠ x := fun he => hxA (Eq.mp (congrArg (fun z : V => z ∈ A) he) hu)
      exact htriY a u hax hux eya (haCross u hu) eyu.symm
    have hsub : G.neighborSet y ⊆ ({a, b} : Set V) := by
      intro z eyz
      rcases hcover z eyz with hzA | hza | hzb
      · exact False.elim (hnoA z hzA eyz)
      · exact Or.inl hza
      · exact Or.inr hzb
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hab] at hh
    omega
  have hsubY : G.neighborSet y ⊆ insert b A := by
    intro z eyz
    rcases hcover z eyz with hzA | hza | hzb
    · exact Or.inr hzA
    · exact False.elim (hya (Eq.mp (congrArg (fun z : V => G.Adj y z) hza) eyz))
    · exact Or.inl hzb
  have hcardB : (insert b A).ncard = A.ncard + 1 := Set.ncard_insert_of_notMem hbA
  have hhigh : (G.neighborSet y).ncard ≤ A.ncard + 1 := by
    rw [← hcardB]
    exact Set.ncard_le_ncard hsubY
  constructor
  · symm
    apply Set.eq_of_subset_of_ncard_le hsubX
    omega
  · apply Set.eq_of_subset_of_ncard_le hsubY
    omega

#print axioms actual_component_root_leaf_neighbor_cover
#print axioms biclique_leaf_root_neighbor_sets
end TaskH.Gao
