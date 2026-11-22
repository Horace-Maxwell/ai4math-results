import Research.TaskN.Antichain.Challenge

namespace TaskN.Antichain

open Polynomial SimpleGraph

theorem iso_indep_finset {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s : Finset V) :
    H.IsIndepSet ((s.map e.toEquiv.toEmbedding : Finset W) : Set W) ↔
      G.IsIndepSet (s : Set V) := by
  classical
  constructor
  · intro h i hi j hj hne hadj
    apply h (x := e i) (Finset.mem_map.mpr ⟨_,hi,rfl⟩)
      (y := e j) (Finset.mem_map.mpr ⟨_,hj,rfl⟩) (fun he ↦ hne (e.injective he))
    exact e.map_rel_iff.mpr hadj
  · intro h i hi j hj hne hadj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hj
    exact h ha hb (fun he ↦ hne (congrArg e he)) (e.map_rel_iff.mp hadj)

theorem iso_ip {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Challenge.independencePolynomial H = Challenge.independencePolynomial G := by
  classical
  unfold Challenge.independencePolynomial
  rw [← (e.toEquiv.finsetCongr).sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Equiv.finsetCongr_apply, Finset.card_map, iso_indep_finset]

end TaskN.Antichain
