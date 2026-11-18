import Research.TaskH.Gao.BicliqueG5OriginalFamily
import Research.TaskH.Gao.BicliqueG5SingletonOne
import Research.TaskH.Gao.BicliqueG5SelectedRegion

/-! Original normalized counterexample: balanced core implies s>=2 and an
actual nonempty selected H. No desired H, child graph or family is supplied. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g5_balanced_s_ge_two [Fintype V] (G : SimpleGraph V)
    (A : Set V) (x y : V) (s k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : A.ncard = s + 1) (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) : 2 ≤ s := by
  by_contra hn
  have hs1 : s = 1 := by omega
  have hA2 : A.ncard = 2 := by omega
  exact hno (g5_two_neighbor_original_family G A x y k hG hxy (by omega) hA2 hNx hNy hd ih)

theorem biclique_g5_original_s_ge_two [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hG : TwoConnected G) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) : 2 ≤ s := by
  have hA := biclique_g5_original_balanced G A B x y s k hG hmax htri hquad hs hsk hB
    hNx hNy hd ih hno
  have hx : x ∈ B := hmax.1.2.2.1
  have hy : y ∉ A ∪ B := hmax.1.2.2.2.1
  have hxy : x ≠ y := fun he => hy (Or.inr (he ▸ hx))
  exact g5_balanced_s_ge_two G A x y s k hG hxy hs hsk hA hNx hNy hd ih hno

theorem biclique_g5_original_selected_H [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hG : TwoConnected G) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    2 ≤ s ∧ A.ncard = s + 1 ∧ ∃ w ∈ B \ {x},
      2 ≤ (G.neighborSet w ∩ g6SelectedRegion G A B y w).ncard ∧
        (g6SelectedRegion G A B y w).Nonempty := by
  classical
  have hA := biclique_g5_original_balanced G A B x y s k hG hmax htri hquad hs hsk hB
    hNx hNy hd ih hno
  obtain ⟨hAB, _hc, hx, hy, _hBtwo, _hBA⟩ := hmax.1
  have hxy : x ≠ y := fun he => hy (Or.inr (he ▸ hx))
  have hs2 := g5_balanced_s_ge_two G A x y s k hG hxy hs hsk hA hNx hNy hd ih hno
  have hindB := (casebi_parts_independent G x y A B hmax.1 htri hquad).2
  obtain ⟨w, hw⟩ := g5_nonroot_B_exists B x s hx hs hB
  exact ⟨hs2, hA, w, hw,
    g5_selected_two_neighbors G A B x y w s k hAB hy hw hindB hNy hA hs hsk hd,
    g5_selected_region_nonempty G A B x y w s k hAB hy hw hindB hNy hA hs hsk hd⟩

#print axioms g5_balanced_s_ge_two
#print axioms biclique_g5_original_s_ge_two
#print axioms biclique_g5_original_selected_H
end TaskH.Gao
