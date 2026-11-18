import Research.TaskH.Gao.ActualCliqueFullBranch
import Research.TaskH.Gao.CaseTwoOriginalQuad
import Research.TaskH.Gao.CaseThreeOriginal
import Research.TaskH.Gao.BicliqueSingletonOriginalBranch
import Research.TaskH.Gao.CasebiOriginalNonsingletonExhaustion

/-! All cases of the ORIGINAL ordinary normalized k>=3 stage.
The root orientation is selected before selecting the actual lexmax biclique.
All forbidden patterns, the actual four-cycle, the actual biclique and the
actual y-component are selected inside the proof, not assumed by the endpoint. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_no_root_triangle_of_clique_card_bound [Fintype V]
    (G : SimpleGraph V) (x y : V)
    (hbound : ∀ K : Set V, G.IsClique K → x ∈ K → K.ncard ≤ 2) :
    CasebiNoRootTriangle G x y := by
  classical
  intro a b _hay _hby exa eab ebx
  have hcl : G.IsClique ({x, a, b} : Set V) := by
    intro r hr t ht hrt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ht
    rcases hr with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact False.elim (hrt rfl)
    · exact exa
    · exact ebx.symm
    · exact exa.symm
    · exact False.elim (hrt rfl)
    · exact eab
    · exact ebx
    · exact eab.symm
    · exact False.elim (hrt rfl)
  have hxAB : x ∉ ({a, b} : Set V) := by
    rintro (hxa | hxb)
    · exact exa.ne hxa
    · exact ebx.ne hxb.symm
  have hcard : ({x, a, b} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hxAB, Set.ncard_pair eab.ne]
  have hh := hbound ({x, a, b} : Set V) hcl (Or.inl rfl)
  omega

theorem casebi_neighbor_independent_of_no_root_triangle
    (G : SimpleGraph V) (x y : V) (hnoedge : ¬G.Adj x y)
    (htri : CasebiNoRootTriangle G x y) :
    G.IsIndepSet (G.neighborSet x) := by
  intro a ha b hb _hab eab
  have hay : a ≠ y := by
    intro he
    exact hnoedge (he ▸ ha)
  have hby : b ≠ y := by
    intro he
    exact hnoedge (he ▸ hb)
  exact htri a b hay hby ha eab hb.symm

theorem ordinary_normalized_sorted_admissible_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hnoedge : ¬G.Adj x y)
    (hk : 3 ≤ k) (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard) :
    HasAdmissiblePaths G x y k := by
  classical
  by_contra hcounter
  obtain ⟨hclX, hclY⟩ := no_large_clique_at_either_root_from_smaller_IH
    G x y k hG hxy (by omega) hnoedge hd ih hcounter
  have htri : CasebiNoRootTriangle G x y :=
    casebi_no_root_triangle_of_clique_card_bound G x y hclX
  have htriY : CasebiNoRootTriangle G y x :=
    casebi_no_root_triangle_of_clique_card_bound G y x hclY
  have hix : G.IsIndepSet (G.neighborSet x) :=
    casebi_neighbor_independent_of_no_root_triangle G x y hnoedge htri
  have hiy : G.IsIndepSet (G.neighborSet y) :=
    casebi_neighbor_independent_of_no_root_triangle G y x
      (fun e => hnoedge e.symm) htriY
  have hforbid := case3_original_no_triple_from_smaller_IH
    G x y k hG hxy hnoedge hk hix hiy horder hd ih hcounter
  have hquad : CasebiNoTripleOnRootQuad G x y := by
    intro a b c v hac hxb hay hby hcy exa eab ebc ecx
      hvx hva hvb hvc hvy eva evb evc
    exact hforbid a b c hac hxb hay hby hcy exa eab ebc ecx
      v hvx hva hvb hvc hvy ⟨eva, evc, evb⟩
  obtain ⟨_hxy, a, b, c, hac, hxb, hay, hby, hcy, exa, eab, ebc, ecx⟩ :=
    case2_original_root_quad G x y k hG hxy hnoedge hk hix horder hd ih hcounter
  obtain ⟨s, A, B, _hs, hmax, hBs, _hInduced, _hCaps⟩ :=
    casebi_from_actual_root_quad G x y a b c hac hxb hxy hay hby hcy
      exa eab ebc ecx htri hquad
  by_cases hlarge : 2 ≤ Nat.card ((G.induce (A ∪ B)ᶜ).connectedComponentMk
      ⟨y, hmax.1.2.2.2.1⟩).supp
  · exact hcounter (casebi_actual_y_component_nonsingleton_original_family
      G A B x y s k hmax hBs hk hG hnoedge htri htriY hquad hd horder ih hlarge)
  · have hsmall : Nat.card ((G.induce (A ∪ B)ᶜ).connectedComponentMk
        ⟨y, hmax.1.2.2.2.1⟩).supp ≤ 1 := by omega
    exact hcounter (biclique_singleton_original_branch
      G A B x y k hG hmax htri htriY hquad hk hnoedge horder hsmall hd ih)

theorem ordinary_normalized_admissible_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hnoedge : ¬G.Adj x y)
    (hk : 3 ≤ k) (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard
  · exact ordinary_normalized_sorted_admissible_from_smaller_IH
      G x y k hG hxy hnoedge hk hd ih horder
  · have hrev : HasAdmissiblePaths G y x k :=
      ordinary_normalized_sorted_admissible_from_smaller_IH
        G y x k hG hxy.symm (fun e => hnoedge e.symm) hk
        (fun v hvy hvx => hd v hvx hvy) ih (by omega)
    obtain ⟨a, d, p, hp⟩ := hrev
    exact ⟨a, d, (fun i => (p i).reverse), admissible_reverse hp⟩

#print axioms casebi_no_root_triangle_of_clique_card_bound
#print axioms casebi_neighbor_independent_of_no_root_triangle
#print axioms ordinary_normalized_sorted_admissible_from_smaller_IH
#print axioms ordinary_normalized_admissible_from_smaller_IH
end TaskH.Gao
