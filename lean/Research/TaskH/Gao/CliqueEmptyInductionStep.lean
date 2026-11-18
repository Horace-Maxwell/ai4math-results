import Research.TaskH.Gao.CliqueEmptyRealRoot
import Research.TaskH.Gao.FamilyOperations

/-! The empty-boundary branch uses the real x-vertex and a strict smaller-order IH. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem clique_empty_branch_from_smaller_IH [iV : Fintype V]
    (G : SimpleGraph V) (B K : Set V) (x y : V) (k : ℕ)
    [iB : Fintype B] [iT : Fintype (B ∪ {x} : Set V)] (b : B)
    (hG : @TwoConnected V iV G) (hB : @TwoConnected B iB (G.induce B))
    (hBK : Disjoint B K) (hx : x ∈ K) (ht : 3 ≤ K.ncard) (hk : 1 ≤ k)
    (hBy : y ∈ B → y = b.1) (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (hS : cliqueBlockBoundary G B K x b.1 = ∅)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K)
    (R : G.Walk b.1 y) (hR : R.IsPath) (hRx : x ∉ R.support)
    (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths G x y k := by
  classical
  have hroot := clique_empty_real_rooted G B K x b hG hB hBK hx ht hS hcover
  have hd := clique_empty_real_nonroot_degree G B K x y b k hBK hx hBy hdeg hS hcover
  have hltNat := clique_empty_real_strict_order B K x hBK ht
  have hlt : Fintype.card (B ∪ {x} : Set V) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  have hchild := ih (B ∪ {x} : Set V) (realRootGraph G B x)
    (realRootPoint B x) (realRootBlockPoint B x b) k hlt hk hroot hd
  obtain ⟨a, d, p, hp⟩ := hchild
  let f : realRootGraph G B x →g G := (Embedding.induce (B ∪ {x} : Set V)).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hm := (admissible_family_map (realRootGraph G B x) G f hf
    (realRootPoint B x) (realRootBlockPoint B x b) k a d p hp).1
  let q : Fin k → G.Walk x b.1 := fun i => (p i).map f
  have hq : AdmissiblePathFamily G x b.1 k a d q := hm
  have hregion : ∀ i z, z ∈ (q i).support → z ∈ B ∨ z = x := by
    intro i z hz
    change z ∈ ((p i).map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w, _hw, he⟩ := List.mem_map.mp hz
    have he' : w.1 = z := he
    rcases w.2 with hwB | hwx
    · exact Or.inl (he' ▸ hwB)
    · exact Or.inr (he'.symm.trans hwx)
  have hmeet : ∀ i z, z ∈ (q i).support → z ∈ R.support → z = b.1 := by
    intro i z hz hzR
    rcases hregion i z hz with hzB | hzx
    · exact hRB z hzR hzB
    · exact False.elim (hRx (hzx ▸ hzR))
  have hout := (admissible_family_append_fixed_tail G x b.1 y k a d q R hq hR hmeet).1
  exact ⟨a + R.length, d, (fun i => (q i).append R), hout⟩

#print axioms clique_empty_branch_from_smaller_IH
end TaskH.Gao
