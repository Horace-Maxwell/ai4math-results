import Research.TaskH.Gao.UnorderedLinkage.AuxiliaryRoot

/-! Complete original unordered two-set linkage, including shared endpoints.
The output may pair the two endpoint sets either way and allows singleton zero paths. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u}

/-- No pairing, common cycle, block or linkage witness is supplied as a hypothesis. -/
theorem ordinary_two_connected_unordered_two_set_linkage [Fintype V]
    (G : SimpleGraph V) (hG : _root_.TaskH.Fan.TwoConnected G)
    (a b w y : V) (hab : a ≠ b) (hwy : w ≠ y) :
    (∃ (P : G.Walk a w) (Q : G.Walk b y),
      P.IsPath ∧ Q.IsPath ∧ P.support.Disjoint Q.support) ∨
    (∃ (P : G.Walk a y) (Q : G.Walk b w),
      P.IsPath ∧ Q.IsPath ∧ P.support.Disjoint Q.support) := by
  classical
  let K := pairRootGraph G a b
  let S : Set (Option V) := {some w, some y}
  have hKS : _root_.TaskH.Fan.TwoConnected K := pairRootGraph_two_connected G a b hG hab
  have hnone : (none : Option V) ∉ S := by simp [S]
  have hS : ∃ u ∈ S, ∃ v ∈ S, u ≠ v := by
    refine ⟨some w, by simp [S], some y, by simp [S], ?_⟩
    exact fun he => hwy (Option.some.inj he)
  obtain ⟨u, hu, v, hv, huv, Ru, Rv, hRu, hRv, hmeet, _, _⟩ :=
    ordinary_two_connected_rooted_fan K hKS none S hnone hS
  have hordered : ∃ (Rw : K.Walk none (some w)) (Ry : K.Walk none (some y)),
      Rw.IsPath ∧ Ry.IsPath ∧ MeetsOnly Rw Ry none := by
    change u = some w ∨ u = some y at hu
    change v = some w ∨ v = some y at hv
    rcases hu with rfl | rfl
    · rcases hv with rfl | rfl
      · exact False.elim (huv rfl)
      · exact ⟨Ru, Rv, hRu, hRv, hmeet⟩
    · rcases hv with rfl | rfl
      · refine ⟨Rv, Ru, hRv, hRu, ?_⟩
        intro z hzv hzu
        exact hmeet z hzu hzv
      · exact False.elim (huv rfl)
  obtain ⟨Rw, Ry, hRw, hRy, hmeet⟩ := hordered
  obtain ⟨c, hc, P, hP, hPsub⟩ := pairRoot_arm_to_original G a b w Rw hRw
  obtain ⟨d, hd, Q, hQ, hQsub⟩ := pairRoot_arm_to_original G a b y Ry hRy
  have hcd : c ≠ d := by
    intro he
    have hcR : some c ∈ Rw.support := hPsub c P.start_mem_support
    have hdR : some d ∈ Ry.support := hQsub d Q.start_mem_support
    have hcRy : some c ∈ Ry.support := by rw [he]; exact hdR
    have hn := hmeet (some c) hcR hcRy
    cases hn
  have hdisj : P.support.Disjoint Q.support := by
    rw [List.disjoint_left]
    intro z hzP hzQ
    have hn := hmeet (some z) (hPsub z hzP) (hQsub z hzQ)
    cases hn
  rcases hc with rfl | rfl
  · rcases hd with rfl | rfl
    · exact False.elim (hcd rfl)
    · exact Or.inl ⟨P, Q, hP, hQ, hdisj⟩
  · rcases hd with rfl | rfl
    · exact Or.inr ⟨Q, P, hQ, hP, hdisj.symm⟩
    · exact False.elim (hcd rfl)
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.ordinary_two_connected_unordered_two_set_linkage
