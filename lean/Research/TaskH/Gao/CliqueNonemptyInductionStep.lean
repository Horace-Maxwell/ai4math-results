import Research.TaskH.Gao.CliqueFamilyTransport
import Research.TaskH.Gao.CliqueBoundaryRooted

/-! A genuine proper-order IH caller for the actual nonempty-S D1 branch. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

attribute [local instance] regionIdentificationFintype

theorem clique_nonempty_branch_from_smaller_IH [iV : Fintype V]
    (G : SimpleGraph V) (B K : Set V) (x y : V) (k : ℕ)
    (hBK : Disjoint B K) [iB : Fintype B] (b : B)
    [iO : Fintype {z : (B ∪ cliqueBlockBoundary G B K x b.1 : Set V) //
      z.1 ∉ cliqueBlockBoundary G B K x b.1}]
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hB : @TwoConnected B iB (G.induce B)) (hBy : y ∈ B → y = b.1)
    (hS : (cliqueBlockBoundary G B K x b.1).Nonempty)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K)
    (R : G.Walk b.1 y) (hR : R.IsPath)
    (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1)
    (hRK : ∀ z ∈ R.support, z ∉ K)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths G x y k := by
  classical
  have hroot := cliqueBlock_quotient_rooted G B K x hBK (iB := iB) b (iO := iO) hB hS
  have hd := cliqueBlock_quotient_nonroot_degree G B K x y b.1 k hBK hK hx b.2 hBy
    ht htk hdeg hcover
  have hltNat := cliqueBlock_quotient_strict_order G B K x b.1 hBK ht
  have hlt : Fintype.card (IdentificationVertex
      {z : (B ∪ cliqueBlockBoundary G B K x b.1 : Set V) |
        z.1 ∈ cliqueBlockBoundary G B K x b.1}) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  have hell : 1 ≤ k - K.ncard + 2 := by omega
  have hparam : (k - K.ncard + 2) + 1 = k - K.ncard + 3 := by omega
  have hchildDeg : NonrootDegreeAtLeast
      (regionIdentificationGraph G B (cliqueBlockBoundary G B K x b.1)) none
      (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b.1)
        (cliqueBlock_boundary_disjoint G B K x b.1 hBK) b)) ((k - K.ncard + 2) + 1) := by
    rw [hparam]
    exact hd
  have hchild := ih (IdentificationVertex
      {z : (B ∪ cliqueBlockBoundary G B K x b.1 : Set V) |
        z.1 ∈ cliqueBlockBoundary G B K x b.1})
    (regionIdentificationGraph G B (cliqueBlockBoundary G B K x b.1)) none
    (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b.1)
      (cliqueBlock_boundary_disjoint G B K x b.1 hBK) b))
    (k - K.ncard + 2) hlt hell hroot hchildDeg
  exact clique_quotient_family_transport G B K x y b k hBK hK.1 hx ht htk
    R hR hRB hRK hchild

#print axioms clique_nonempty_branch_from_smaller_IH
end TaskH.Gao
