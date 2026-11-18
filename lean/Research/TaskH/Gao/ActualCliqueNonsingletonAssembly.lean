import Research.TaskH.Gao.ComponentTerminalCliqueDegree
import Research.TaskH.Gao.LargeCliqueAdmissible
import Research.TaskH.Gao.CliqueNonemptyInductionStep
import Research.TaskH.Gao.CliqueEmptyInductionStep
import Research.TaskH.Gao.Base

/-! The actual non-singleton G-K component branch. B, b, the tail, its
coverage and both smaller rooted graphs are chosen internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem actual_clique_nonsingleton_from_smaller_IH [iV : Fintype V]
    (G : SimpleGraph V) (K : Set V) (x y : V) (k : ℕ)
    (hG : @TwoConnected V iV G) (hK : Maximal G.IsClique K)
    (hx : x ∈ K) (hy : y ∉ K) (ht : 3 ≤ K.ncard) (hk : 1 ≤ k)
    (hC : 2 ≤ Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases hk2 : 2 ≤ k
  · by_cases hlarge : k + 1 ≤ K.ncard
    · exact large_clique_has_admissible_paths G K x y k hG hK.1 hx hy hk2 hlarge
    · have htk : K.ncard ≤ k := by omega
      let C := (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩
      let yr : C.supp := ⟨⟨y, hy⟩, rfl⟩
      let iC : Fintype C.supp := Fintype.ofFinite _
      have hCf : 2 ≤ Fintype.card C.supp := by
        simpa only [Fintype.card_eq_nat_card] using hC
      have hd : NonrootDegreeAtLeast G x (componentVertex C yr) (k + 1) := hdeg
      obtain ⟨B, b, hb, hBK, hBy, hcover, ⟨iB, hB⟩, R, hR, hRK, hRB⟩ :=
        actual_clique_component_fragment_tail C yr hCf x k hK hx htk hd
      let : Fintype B := iB
      let br : B := ⟨b, hb⟩
      by_cases hS : (cliqueBlockBoundary G B K x b).Nonempty
      · let iO : Fintype {z : (B ∪ cliqueBlockBoundary G B K x b : Set V) //
            z.1 ∉ cliqueBlockBoundary G B K x b} := Fintype.ofFinite _
        exact clique_nonempty_branch_from_smaller_IH G B K x y k hBK
          (iB := iB) br (iO := iO) hK hx ht htk hB hBy hS hdeg hcover
          R hR hRB hRK ih
      · let iT : Fintype (B ∪ {x} : Set V) := Fintype.ofFinite _
        have hSempty : cliqueBlockBoundary G B K x b = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hS
        have hRx : x ∉ R.support := fun hxR => hRK x hxR hx
        exact clique_empty_branch_from_smaller_IH G B K x y k
          (iB := iB) (iT := iT) br hG hB hBK hx ht hk hBy hdeg hSempty hcover
          R hR hRx hRB ih
  · have hk1 : k = 1 := by omega
    subst k
    have htwo : HasAdmissiblePaths G x y 2 :=
      large_clique_has_admissible_paths G K x y 2 hG hK.1 hx hy (by omega) ht
    exact has_admissible_initial_segment (by omega : 1 ≤ 2) htwo

theorem no_admissible_paths_clique_component_card_le_one [iV : Fintype V]
    (G : SimpleGraph V) (K : Set V) (x y : V) (k : ℕ)
    (hG : @TwoConnected V iV G) (hK : Maximal G.IsClique K)
    (hx : x ∈ K) (hy : y ∉ K) (ht : 3 ≤ K.ncard) (hk : 1 ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell)
    (hno : ¬HasAdmissiblePaths G x y k) :
    Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1 := by
  by_contra hcard
  have hC : 2 ≤ Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp := by omega
  exact hno (actual_clique_nonsingleton_from_smaller_IH G K x y k
    hG hK hx hy ht hk hC hdeg ih)

#print axioms actual_clique_nonsingleton_from_smaller_IH
#print axioms no_admissible_paths_clique_component_card_le_one
end TaskH.Gao
