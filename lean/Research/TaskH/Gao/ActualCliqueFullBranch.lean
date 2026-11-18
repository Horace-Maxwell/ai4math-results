import Research.TaskH.Gao.ActualCliqueNonsingletonAssembly
import Research.TaskH.Gao.SingletonG1InductionAndFamily
import Research.TaskH.Gao.SingletonG2ConnectivityAndInduction

/-! Original ordinary-graph D1: every internal component/G1/G2 case is selected in the proof. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem actual_clique_full_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (K : Set V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hK : Maximal G.IsClique K)
    (hx : x ∈ K) (hy : y ∉ K) (ht : 3 ≤ K.ncard) (hk : 1 ≤ k)
    (hnoedge : ¬G.Adj x y) (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases hk3 : 3 ≤ k
  · by_cases hfamily : HasAdmissiblePaths G x y k
    · exact hfamily
    · have htk : K.ncard ≤ k := clique_card_le_of_no_admissible_paths
        G K x y k hG hK.1 hx hy (by omega) hfamily
      by_cases hC : 2 ≤ Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp
      · exact actual_clique_nonsingleton_from_smaller_IH G K x y k
          hG hK hx hy ht hk hC hdeg ih
      · have hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1 := by omega
        have hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
            D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
            (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
              ∃ d : D.supp, G.Adj x d.1.1 := by
          intro D hother htouch
          by_contra hxD
          obtain ⟨v, eyv, d, evd⟩ := htouch
          have hvK : v ∈ K := singleton_component_neighbors_subset G K y hy hsmall eyv
          have hv : v ∈ singletonG1Boundary G K D := ⟨hvK, d, evd.symm⟩
          exact hfamily (singleton_g1_branch_from_smaller_IH G K D x y v k
            hG hK.1 hx hy ht htk hother hv hxD eyv.symm hdeg ih)
        have ihNat : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
            Nat.card W < Nat.card V → 1 ≤ ell → RootedTwoConnected H s t →
            NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell := by
          intro W iW H s t ell hcard hell hroot hd
          exact ih W H s t ell
            (by simpa only [Fintype.card_eq_nat_card] using hcard) hell hroot hd
        exact singleton_g2_actual_branch G K x y k hG hx hy hK.1 ht htk
          hnoedge hdeg hsmall hG1 ihNat
  · have htwo : HasAdmissiblePaths G x y 2 :=
      large_clique_has_admissible_paths G K x y 2 hG hK.1 hx hy (by omega) ht
    exact has_admissible_initial_segment (by omega : k ≤ 2) htwo

theorem no_large_clique_at_either_root_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hk : 1 ≤ k)
    (hnoedge : ¬G.Adj x y) (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell)
    (hno : ¬HasAdmissiblePaths G x y k) :
    (∀ K : Set V, G.IsClique K → x ∈ K → K.ncard ≤ 2) ∧
      (∀ K : Set V, G.IsClique K → y ∈ K → K.ncard ≤ 2) := by
  classical
  have hbound : ∀ (s t : V), s ≠ t → ¬G.Adj s t →
      NonrootDegreeAtLeast G s t (k + 1) → ¬HasAdmissiblePaths G s t k →
      ∀ K : Set V, G.IsClique K → s ∈ K → K.ncard ≤ 2 := by
    intro s t hst hnot hd hn K hcl hsK
    by_contra hcard
    have htK : 3 ≤ K.ncard := by omega
    obtain ⟨M, hKM, hM⟩ := Finite.exists_le_maximal hcl
    have hsM : s ∈ M := hKM hsK
    have htM : t ∉ M := fun htM => hnot (hM.1 hsM htM hst)
    have hcM : 3 ≤ M.ncard := le_trans htK (Set.ncard_le_ncard hKM)
    exact hn (actual_clique_full_from_smaller_IH G M s t k
      hG hM hsM htM hcM hk hnot hd ih)
  have hrev : ¬HasAdmissiblePaths G y x k := by
    intro hp
    obtain ⟨a, d, p, hp⟩ := hp
    exact hno ⟨a, d, (fun i => (p i).reverse),
      (admissible_family_reverse G y x k a d p hp).1⟩
  have hdrev : NonrootDegreeAtLeast G y x (k + 1) := by
    intro v hvy hvx
    exact hdeg v hvx hvy
  exact ⟨hbound x y hxy hnoedge hdeg hno,
    hbound y x hxy.symm (fun e => hnoedge e.symm) hdrev hrev⟩

#print axioms actual_clique_full_from_smaller_IH
#print axioms no_large_clique_at_either_root_from_smaller_IH
end TaskH.Gao
