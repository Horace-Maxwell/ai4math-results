import Research.TaskH.Fan.RootedCutBranch
import Research.TaskH.Gao.FamilyOperations
import Research.TaskH.Gao.Base

/-! Arbitrary positive family counts across an actual root-separating cut.
Only the large-side size guard uses degree three; the IH retains degree k+1. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem rootedCutSide_nonroot_degree_uniform [Fintype V] (G : SimpleGraph V)
    (x y b : V) (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (d : ℕ)
    (hdeg : NonrootDegreeAtLeast G x y d) :
    NonrootDegreeAtLeast (G.induce (rootedCutSide G b x hx))
      (⟨x, Or.inr ⟨hx, rfl⟩⟩ : rootedCutSide G b x hx)
      (⟨b, Or.inl rfl⟩ : rootedCutSide G b x hx) d := by
  intro t htx htb
  have htx' : t.1 ≠ x := fun he => htx (Subtype.ext he)
  have htb' : t.1 ≠ b := fun he => htb (Subtype.ext he)
  have hty' : t.1 ≠ y := by
    intro he
    exact rootedCutSide_other_root_not_mem G x y b hroot hx hy hbad (he ▸ t.2)
  rw [← rootedCutSide_neighbor_ncard G b x hx t htb']
  exact hdeg t.1 htx' hty'

theorem rooted_cut_large_side_admissible_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y b : V) (k : ℕ)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hk : 1 ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    [Fintype (rootedCutSide G b x hx)]
    (hcard : 3 ≤ Fintype.card (rootedCutSide G b x hx))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c (ell + 1) → HasAdmissiblePaths J a c ell) :
    HasAdmissiblePaths G x y k := by
  classical
  let S := rootedCutSide G b x hx
  let T := rootedCutSide G b y hy
  let xr : S := ⟨x, Or.inr ⟨hx, rfl⟩⟩
  let br : S := ⟨b, Or.inl rfl⟩
  have hr : RootedTwoConnected (G.induce S) xr br :=
    rootedCutSide_twoConnected G x y b hroot hx hy hbad hcard
  have hd : NonrootDegreeAtLeast (G.induce S) xr br (k + 1) :=
    rootedCutSide_nonroot_degree_uniform G x y b hroot hx hy hbad (k + 1) hdeg
  have hlt : Fintype.card S < Fintype.card V :=
    rootedCutSide_card_lt G x y b hroot hx hy hbad
  obtain ⟨a, d, p, hp⟩ := ih S (G.induce S) xr br k hlt hk hr hd
  let bt : T := ⟨b, Or.inl rfl⟩
  let yt : T := ⟨y, Or.inr ⟨hy, rfl⟩⟩
  have hT := rootedCutSide_connected G b y hy (rooted_original_connected hroot)
  obtain ⟨r, hrp⟩ := (hT bt yt).exists_isPath
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  let g : G.induce T →g G := (SimpleGraph.Embedding.induce T).toHom
  have hpG : AdmissiblePathFamily G x b k a d (fun i => (p i).map f) :=
    (admissible_family_map (G.induce S) G f Subtype.val_injective xr br k a d p hp).1
  have hrG : (r.map g).IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hrp
  have hinter : ∀ v ∈ S, v ∈ T → v = b := by
    intro v hvS hvT
    have hv : v ∈ S ∩ T := ⟨hvS, hvT⟩
    rw [rootedCutSide_inter G x y b hroot hx hy hbad] at hv
    exact Set.mem_singleton_iff.mp hv
  have hmeet : ∀ i v, v ∈ ((p i).map f).support → v ∈ (r.map g).support → v = b := by
    intro i v hvp hvr
    exact hinter v (inducedWalk_support_mem G S (p i) v hvp)
      (inducedWalk_support_mem G T r v hvr)
  have hout := (admissible_family_append_fixed_tail G x b y k a d
    (fun i => (p i).map f) (r.map g) hpG hrG hmeet).1
  exact ⟨a + (r.map g).length, d, (fun i => ((p i).map f).append (r.map g)), hout⟩

theorem rooted_cut_admissible_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y b : V) (k : ℕ)
    (hroot : RootedTwoConnected G x y)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hk : 1 ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c (ell + 1) → HasAdmissiblePaths J a c ell) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases hk2 : 2 ≤ k
  · have hx : x ≠ b := (rooted_cut_ne_left G x y b hroot hbad).symm
    have hy : y ≠ b := (rooted_cut_ne_right G x y b hroot hbad).symm
    let : Fintype (rootedCutSide G b x hx) := Fintype.ofFinite _
    let : Fintype (rootedCutSide G b y hy) := Fintype.ofFinite _
    have hd3 : NonrootDegreeAtLeast G x y 3 := by
      intro v hvx hvy
      have hd := hdeg v hvx hvy
      omega
    rcases rootedCutSide_one_large G x y b hroot hx hy hbad hd3 with hc | hc
    · exact rooted_cut_large_side_admissible_from_smaller_IH
        G x y b k hroot hx hy hbad hk hdeg hc ih
    · have hd' : NonrootDegreeAtLeast G y x (k + 1) :=
        fun v hvy hvx => hdeg v hvx hvy
      obtain ⟨a, d, p, hp⟩ := rooted_cut_large_side_admissible_from_smaller_IH
        G y x b k (rooted_two_connected_symm hroot) hy hx hbad hk hd' hc ih
      exact ⟨a, d, (fun i => (p i).reverse), admissible_reverse hp⟩
  · have hk1 : k = 1 := by omega
    subst k
    exact rooted_has_admissible_one hroot

theorem ordinary_twoConnected_of_no_admissible_with_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hroot : RootedTwoConnected G x y) (hk : 1 ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c (ell + 1) → HasAdmissiblePaths J a c ell)
    (hno : ¬HasAdmissiblePaths G x y k) : TwoConnected G := by
  refine ⟨hroot.2.1, rooted_original_connected hroot, ?_⟩
  intro b
  by_contra hbad
  exact hno (rooted_cut_admissible_from_smaller_IH G x y b k hroot hbad hk hdeg ih)

#print axioms rootedCutSide_nonroot_degree_uniform
#print axioms rooted_cut_large_side_admissible_from_smaller_IH
#print axioms rooted_cut_admissible_from_smaller_IH
#print axioms ordinary_twoConnected_of_no_admissible_with_smaller_IH
end TaskH.Gao
