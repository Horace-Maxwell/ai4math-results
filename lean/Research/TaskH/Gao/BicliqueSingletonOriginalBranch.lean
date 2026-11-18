import Research.TaskH.Gao.BicliqueSingletonNormalization
import Research.TaskH.Gao.BicliqueG5OriginalSelectedH
import Research.TaskH.Gao.BicliqueThirdMatching
import Research.TaskH.Gao.BicliqueTerminalG6Attachment
import Research.TaskH.Gao.G6OriginalFamily

/-! Complete original singleton-y component branch. All normalization,
s>=2, selected H, native matching and terminal attachment are derived internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem componentSetTransport_surjective (G : SimpleGraph V) {U W : Set V} (h : U = W) :
    Function.Surjective (componentSetTransport G h) := by
  cases h
  intro C
  exact ⟨C, rfl⟩

theorem g4ComponentSetTransport_surjective (G : SimpleGraph V) {U W : Set V} (h : U = W) :
    Function.Surjective (g4ComponentSetTransport G h) := by
  cases h
  intro C
  exact ⟨C, rfl⟩

theorem biclique_singleton_original_branch [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y) (htriY : CasebiNoRootTriangle G y x)
    (hquad : CasebiNoTripleOnRootQuad G x y) (hk : 3 ≤ k)
    (hnoedge : ¬G.Adj x y)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (hsmall : Nat.card ((G.induce (A ∪ B)ᶜ).connectedComponentMk
      ⟨y, hmax.1.2.2.2.1⟩).supp ≤ 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases hfamily : HasAdmissiblePaths G x y k
  · exact hfamily
  · have hQ := hmax.1
    have hAB := hQ.1
    have hc := hQ.2.1
    have hx : x ∈ B := hQ.2.2.1
    have hy : y ∉ A ∪ B := hQ.2.2.2.1
    have hBtwo : 2 ≤ B.ncard := hQ.2.2.2.2.1
    obtain ⟨hNx, hNy⟩ := biclique_singleton_actual_root_neighbors G A B x y
      hQ hnoedge htriY horder hsmall
    let s := B.ncard - 1
    have hs : 1 ≤ s := by omega
    have hB : B.ncard = s + 1 := by omega
    have hsk := biclique_singleton_actual_s_bound G A B x y s k hQ hk hB hNy hfamily
    obtain ⟨hs2, hA, w, hw, _hw2, hH⟩ :=
      biclique_g5_original_selected_H G A B x y s k hG hmax htri hquad hs hsk hB
        hNx hNy hd ih hfamily
    have hcap : ∀ C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent,
        ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1 := by
      intro C d
      have hh := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad d.1.1 d.1.2
      exact hh.trans (le_of_eq hB)
    have hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
        g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C := by
      intro C _hTouch
      obtain ⟨D, rfl⟩ :=
        componentSetTransport_surjective G (biclique_core_compl_eq_g6Outside A B y) C
      exact biclique_singleton_actual_g6_matching G A B x y s k D hG hAB hc hx hy hs hsk
        (le_of_eq hA.symm) hB hNx hNy (hcap D) hd ih hfamily
    have hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
        g6ComponentTouches G A B y w C →
        ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
          ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a := by
      intro C _hTouch
      obtain ⟨D, rfl⟩ :=
        g4ComponentSetTransport_surjective G (g4_core_compl_eq_actual_outside A B y) C
      exact biclique_singleton_actual_g6_terminal_attachment G A B x y s k D hG hAB hc hx hy
        hs hsk (le_of_eq hA.symm) hB hNx hNy hd ih hfamily
    have hxw : x ≠ w := by
      intro he
      exact hw.2 (Set.mem_singleton_iff.mpr he.symm)
    obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite A)).mp (by omega : 0 < A.ncard)
    exact g6_original_normalized_branch G A B x y u w s k hQ htri hquad hu hw.1 hxw
      hA hB hs2 (by omega) hNx hNy hH hM hAttach hd ih

#print axioms componentSetTransport_surjective
#print axioms g4ComponentSetTransport_surjective
#print axioms biclique_singleton_original_branch
end TaskH.Gao
