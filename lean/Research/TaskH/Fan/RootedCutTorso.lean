import Research.TaskH.Fan.TwoBoundaryTorso
import Research.TaskH.Fan.RootedCutSide

/-! The real cut side satisfies the torso hypotheses internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem augmentation_induce_of_missing_right (G : SimpleGraph V) (x y : V)
    (S : Set V) (hy : y ∉ S) :
    (G ⊔ SimpleGraph.edge x y).induce S = G.induce S := by
  ext a b
  change (G.Adj a.1 b.1 ∨ (SimpleGraph.edge x y).Adj a.1 b.1) ↔ G.Adj a.1 b.1
  constructor
  · rintro (hG | he)
    · exact hG
    · rcases (SimpleGraph.edge_adj x y a.1 b.1).mp he with ⟨he, _hne⟩
      rcases he with he | he
      · exact False.elim (hy (he.2 ▸ b.2))
      · exact False.elim (hy (he.1 ▸ a.2))
  · exact Or.inl

theorem rootedCutSide_twoConnected [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected)
    [Fintype (rootedCutSide G b x hx)]
    (hcard : 3 ≤ Fintype.card (rootedCutSide G b x hx)) :
    RootedTwoConnected (G.induce (rootedCutSide G b x hx))
      (⟨x, Or.inr ⟨hx, rfl⟩⟩ : rootedCutSide G b x hx)
      (⟨b, Or.inl rfl⟩ : rootedCutSide G b x hx) := by
  let S := rootedCutSide G b x hx
  let xr : S := ⟨x, Or.inr ⟨hx, rfl⟩⟩
  let br : S := ⟨b, Or.inl rfl⟩
  have hxb : xr ≠ br := fun he => hx (congrArg Subtype.val he)
  have hyS : y ∉ S := rootedCutSide_other_root_not_mem G x y b hroot hx hy hbad
  have hc : ∀ v ∈ S, v ≠ xr.1 → v ≠ br.1 →
      ∀ w, (G ⊔ SimpleGraph.edge x y).Adj v w → w ∈ S := by
    intro v hv hvx hvb w hvw
    rcases hvw with hG | he
    · exact rootedCutSide_closed G b x hx v hv hvb w hG
    · rcases (SimpleGraph.edge_adj x y v w).mp he with ⟨he, _hne⟩
      rcases he with he | he
      · exact False.elim (hvx he.1)
      · exact False.elim (hyS (he.1 ▸ hv))
  have hT := twoBoundaryTorso_twoConnected (G ⊔ SimpleGraph.edge x y) S xr br hxb
    hcard hroot.2 hc
  rw [augmentation_induce_of_missing_right G x y S hyS] at hT
  exact ⟨hxb, hT⟩

theorem rootedCutSide_recursion_hypotheses [Fintype V] (G : SimpleGraph V)
    (x y b : V) (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hdeg : NonrootDegreeAtLeast G x y 3)
    [Fintype (rootedCutSide G b x hx)]
    (hcard : 3 ≤ Fintype.card (rootedCutSide G b x hx)) :
    RootedTwoConnected (G.induce (rootedCutSide G b x hx))
        (⟨x, Or.inr ⟨hx, rfl⟩⟩ : rootedCutSide G b x hx)
        (⟨b, Or.inl rfl⟩ : rootedCutSide G b x hx) ∧
      NonrootDegreeAtLeast (G.induce (rootedCutSide G b x hx))
        (⟨x, Or.inr ⟨hx, rfl⟩⟩ : rootedCutSide G b x hx)
        (⟨b, Or.inl rfl⟩ : rootedCutSide G b x hx) 3 ∧
      Fintype.card (rootedCutSide G b x hx) < Fintype.card V := by
  exact ⟨rootedCutSide_twoConnected G x y b hroot hx hy hbad hcard,
    rootedCutSide_nonroot_degree G x y b hroot hx hy hbad hdeg,
    rootedCutSide_card_lt G x y b hroot hx hy hbad⟩

theorem rootedCutSide_connected (G : SimpleGraph V) (b x : V) (hx : x ≠ b)
    (hG : G.Connected) : (G.induce (rootedCutSide G b x hx)).Connected := by
  classical
  let S := rootedCutSide G b x hx
  let br : S := ⟨b, Or.inl rfl⟩
  apply torsoRetraction_connected G S (G.induce S) br ?_ hG
  have hcross : ∀ v ∈ S, ∀ w ∉ S, G.Adj v w → v = b := by
    intro v hv w hw hvw
    by_contra hvb
    exact hw (rootedCutSide_closed G b x hx v hv hvb w hvw)
  intro v w hvw
  by_cases hv : v ∈ S
  · by_cases hw : w ∈ S
    · right
      rw [torsoRetraction_mem S br v hv, torsoRetraction_mem S br w hw]
      exact hvw
    · left
      rw [torsoRetraction_mem S br v hv, torsoRetraction_not_mem S br w hw]
      exact Subtype.ext (hcross v hv w hw hvw)
  · by_cases hw : w ∈ S
    · left
      rw [torsoRetraction_not_mem S br v hv, torsoRetraction_mem S br w hw]
      exact Subtype.ext (hcross w hw v hv hvw.symm).symm
    · left
      rw [torsoRetraction_not_mem S br v hv, torsoRetraction_not_mem S br w hw]

#print axioms augmentation_induce_of_missing_right
#print axioms rootedCutSide_twoConnected
#print axioms rootedCutSide_recursion_hypotheses
#print axioms rootedCutSide_connected
end TaskH.Fan
