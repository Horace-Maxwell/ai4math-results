import Research.TaskH.Gao.BicliqueLexicographicSelection
import Research.TaskH.Gao.SingletonCliqueNeighbors
import Research.TaskH.Gao.BipartitePrefixFamily
import Research.TaskH.Gao.Challenge

/-! The actual singleton y-component internally forces both full root neighborhoods
and the original s bound. No root-neighborhood equality is a supplied oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_singleton_actual_root_neighbors [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (hQ : CasebiBiclique G x y A B)
    (hnoedge : ¬G.Adj x y) (htriY : CasebiNoRootTriangle G y x)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (hsmall : Nat.card ((G.induce (A ∪ B)ᶜ).connectedComponentMk
      ⟨y, hQ.2.2.2.1⟩).supp ≤ 1) :
    G.neighborSet x = A ∧ G.neighborSet y = A := by
  classical
  obtain ⟨hAB, hc, hx, hy, _hB, hBA⟩ := hQ
  have hAx : A ⊆ G.neighborSet x := fun a ha => (hc a ha x hx).symm
  have hAxcard := Set.ncard_le_ncard hAx
  have hNyQ := singleton_component_neighbors_subset G (A ∪ B) y hy hsmall
  have hnotB : ∀ b ∈ B, ¬G.Adj y b := by
    intro b hb eyb
    have hbx : b ≠ x := by
      intro he
      exact hnoedge ((he ▸ eyb).symm)
    have hnoneA : ∀ a ∈ A, ¬G.Adj y a := by
      intro a ha eya
      have hax : a ≠ x := fun he => Set.disjoint_left.mp hAB (he ▸ ha) hx
      exact htriY b a hbx hax eyb (hc a ha b hb).symm eya.symm
    have hsub : G.neighborSet y ⊆ B \ ({x} : Set V) := by
      intro z eyz
      refine ⟨?_, ?_⟩
      · rcases hNyQ eyz with hzA | hzB
        · exact False.elim (hnoneA z hzA eyz)
        · exact hzB
      · intro hzx
        have he : z = x := hzx
        exact hnoedge ((he ▸ eyz).symm)
    have hbnd := Set.ncard_le_ncard hsub
    have hBc := Set.ncard_sdiff_singleton_add_one hx
    omega
  have hNyA : G.neighborSet y ⊆ A := by
    intro z eyz
    rcases hNyQ eyz with hzA | hzB
    · exact hzA
    · exact False.elim (hnotB z hzB eyz)
  have hNy : G.neighborSet y = A :=
    Set.eq_of_subset_of_ncard_le hNyA (hAxcard.trans horder) (Set.toFinite A)
  have hNcard : (G.neighborSet x).ncard ≤ A.ncard := by
    rw [hNy] at horder
    exact horder
  have hNx : G.neighborSet x = A :=
    (Set.eq_of_subset_of_ncard_le hAx hNcard (Set.toFinite (G.neighborSet x))).symm
  exact ⟨hNx, hNy⟩

theorem biclique_singleton_actual_s_bound [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hQ : CasebiBiclique G x y A B) (hk : 3 ≤ k)
    (hB : B.ncard = s + 1) (hNy : G.neighborSet y = A)
    (hno : ¬HasAdmissiblePaths G x y k) : s ≤ k - 2 := by
  classical
  by_contra hbad
  have hAB := hQ.1
  have hc := hQ.2.1
  have hx : x ∈ B := hQ.2.2.1
  have hy : y ∉ A ∪ B := hQ.2.2.2.1
  have hBA : B.ncard ≤ A.ncard := hQ.2.2.2.2.2
  have hxy : x ≠ y := fun he => hy (Or.inr (he ▸ hx))
  have hyB : y ∉ B := fun hyB => hy (Or.inr hyB)
  have hAf : A.Finite := Set.toFinite A
  have hBf : (insert y B).Finite := Set.toFinite _
  let FA := hAf.toFinset
  let FB := hBf.toFinset
  have hFA : FA.card = A.ncard := (Set.ncard_eq_toFinset_card A hAf).symm
  have hFB : FB.card = B.ncard + 1 :=
    (Set.ncard_eq_toFinset_card (insert y B) hBf).symm.trans
      (Set.ncard_insert_of_notMem hyB)
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    have hzA' := hAf.mem_toFinset.mp hzA
    rcases hBf.mem_toFinset.mp hzB with hzy | hzB'
    · exact hy (Or.inl (hzy ▸ hzA'))
    · exact Set.disjoint_left.mp hAB hzA' hzB'
  have hcross : ∀ a ∈ FA, ∀ b ∈ FB, G.Adj a b := by
    intro a ha b hb
    have haA := hAf.mem_toFinset.mp ha
    rcases hBf.mem_toFinset.mp hb with hby | hbB
    · have eya : G.Adj y a := by
        change a ∈ G.neighborSet y
        rw [hNy]
        exact haA
      exact hby.symm ▸ eya.symm
    · exact hc a haA b hbB
  obtain ⟨p, hp⟩ := bipartite_even_prefix_family FA FB k x y hdis hcross
    (hBf.mem_toFinset.mpr (Set.mem_insert_of_mem y hx))
    (hBf.mem_toFinset.mpr (Set.mem_insert y B)) hxy (by omega) (by omega)
  apply hno
  refine ⟨2, 2, p, by omega, Or.inr rfl, ?_⟩
  intro i
  exact ⟨(hp i).1, by have hh := (hp i).2.1; omega⟩

#print axioms biclique_singleton_actual_root_neighbors
#print axioms biclique_singleton_actual_s_bound
end TaskH.Gao
