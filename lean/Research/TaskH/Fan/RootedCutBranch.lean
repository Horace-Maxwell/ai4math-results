import Research.TaskH.Fan.RootedCutTorso
import Research.TaskH.Fan.PathOperations

/-! The actual cut branch under vertex-card strong induction, not a full theorem oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem rootedCutSide_one_large [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hdeg : NonrootDegreeAtLeast G x y 3)
    [Fintype (rootedCutSide G b x hx)] [Fintype (rootedCutSide G b y hy)] :
    3 ≤ Fintype.card (rootedCutSide G b x hx) ∨
      3 ≤ Fintype.card (rootedCutSide G b y hy) := by
  classical
  have hd := hdeg b hx.symm hy.symm
  rw [G.ncard_neighborSet b] at hd
  have hlt := G.degree_lt_card_verts b
  have hcard : 4 ≤ Fintype.card V := by omega
  have hc := Set.ncard_union_add_ncard_inter
    (rootedCutSide G b x hx) (rootedCutSide G b y hy)
  rw [rootedCutSide_cover G x y b hroot hx hy,
    rootedCutSide_inter G x y b hroot hx hy hbad] at hc
  have hc' : Fintype.card V + 1 = Fintype.card (rootedCutSide G b x hx) +
      Fintype.card (rootedCutSide G b y hy) := by
    rw [Set.ncard_univ, Set.ncard_singleton, Nat.card_eq_fintype_card] at hc
    rw [Set.fintypeCard_eq_ncard (rootedCutSide G b x hx),
      Set.fintypeCard_eq_ncard (rootedCutSide G b y hy)]
    exact hc
  omega

theorem inducedWalk_support_mem (G : SimpleGraph V) (S : Set V)
    {a b : S} (p : (G.induce S).Walk a b) :
    ∀ v ∈ (p.map (SimpleGraph.Embedding.induce S).toHom).support, v ∈ S := by
  intro v hv
  rw [Walk.support_map] at hv
  obtain ⟨w, _hw, hwv⟩ := List.mem_map.mp hv
  exact hwv ▸ w.2

theorem rootedCutSide_left_branch [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hdeg : NonrootDegreeAtLeast G x y 3)
    [Fintype (rootedCutSide G b x hx)]
    (hcard : 3 ≤ Fintype.card (rootedCutSide G b x hx))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c 3 → HasTwoPaths J a c) : HasTwoPaths G x y := by
  let S := rootedCutSide G b x hx
  let T := rootedCutSide G b y hy
  let xr : S := ⟨x, Or.inr ⟨hx, rfl⟩⟩
  let br : S := ⟨b, Or.inl rfl⟩
  obtain ⟨hr, hd, hc⟩ := rootedCutSide_recursion_hypotheses G x y b hroot hx hy hbad hdeg hcard
  obtain ⟨p, q, hpq⟩ := ih S (G.induce S) xr br hc hr hd
  let bt : T := ⟨b, Or.inl rfl⟩
  let yt : T := ⟨y, Or.inr ⟨hy, rfl⟩⟩
  have hT := rootedCutSide_connected G b y hy (rooted_original_connected hroot)
  obtain ⟨r, hrp⟩ := (hT bt yt).exists_isPath
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  let g : G.induce T →g G := (SimpleGraph.Embedding.induce T).toHom
  have hmap := twoPathWitness_map f Subtype.val_injective p q hpq
  have hrmap : (r.map g).IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hrp
  have hinter : ∀ v ∈ S, v ∈ T → v = b := by
    intro v hvS hvT
    have hv : v ∈ S ∩ T := ⟨hvS, hvT⟩
    rw [rootedCutSide_inter G x y b hroot hx hy hbad] at hv
    exact Set.mem_singleton_iff.mp hv
  have hpr : ∀ v, v ∈ (p.map f).support → v ∈ (r.map g).support → v = b := by
    intro v hvp hvr
    exact hinter v (inducedWalk_support_mem G S p v hvp)
      (inducedWalk_support_mem G T r v hvr)
  have hqr : ∀ v, v ∈ (q.map f).support → v ∈ (r.map g).support → v = b := by
    intro v hvq hvr
    exact hinter v (inducedWalk_support_mem G S q v hvq)
      (inducedWalk_support_mem G T r v hvr)
  exact ⟨(p.map f).append (r.map g), (q.map f).append (r.map g),
    twoPathWitness_append_of_support_intersection (p.map f) (q.map f) (r.map g)
      hmap hrmap hpr hqr⟩

theorem rootedCut_vertex_induction_branch [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hdeg : NonrootDegreeAtLeast G x y 3)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c 3 → HasTwoPaths J a c) : HasTwoPaths G x y := by
  classical
  have hx : x ≠ b := (rooted_cut_ne_left G x y b hroot hbad).symm
  have hy : y ≠ b := (rooted_cut_ne_right G x y b hroot hbad).symm
  let : Fintype (rootedCutSide G b x hx) := Fintype.ofFinite _
  let : Fintype (rootedCutSide G b y hy) := Fintype.ofFinite _
  rcases rootedCutSide_one_large G x y b hroot hx hy hbad hdeg with hc | hc
  · exact rootedCutSide_left_branch G x y b hroot hx hy hbad hdeg hc ih
  · have hdeg' : NonrootDegreeAtLeast G y x 3 := fun v hvy hvx => hdeg v hvx hvy
    exact hasTwoPaths_reverse (rootedCutSide_left_branch G y x b
      (rooted_two_connected_symm hroot) hy hx hbad hdeg' hc ih)

#print axioms rootedCutSide_one_large
#print axioms inducedWalk_support_mem
#print axioms rootedCutSide_left_branch
#print axioms rootedCut_vertex_induction_branch
end TaskH.Fan
