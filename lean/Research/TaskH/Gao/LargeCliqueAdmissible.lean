import Research.TaskH.Gao.ActualCliqueComponentEntry
import Research.TaskH.Gao.CliquePrefixFamily
import Research.TaskH.Fan.PathOperations

/-! A large actual clique yields the full k-path conclusion with no IH or tail oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem large_clique_has_admissible_paths [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (k : ℕ) (hG : TwoConnected G) (hK : G.IsClique K)
    (hx : x ∈ K) (hy : y ∉ K) (hk : 2 ≤ k) (hlarge : k + 1 ≤ K.ncard) :
    HasAdmissiblePaths G x y k := by
  classical
  let C := (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩
  let yr : C.supp := ⟨⟨y, hy⟩, rfl⟩
  have hcard : 3 ≤ K.ncard := by omega
  obtain ⟨u, huK, hux, R, hR, hRl, hRK⟩ :=
    actual_component_clique_entry_tail G K C x yr hG hx (by omega : 2 ≤ K.ncard)
  have hxu : x ≠ u := fun he => hux he.symm
  obtain ⟨p, hp⟩ := clique_prefix_family K hK hcard x u hx huK hxu
  have hidx : ∀ i : Fin k, i.val < K.ncard - 1 := by
    intro i
    have hi := i.isLt
    omega
  let q : Fin k → G.Walk x y := fun i => (p ⟨i.val, hidx i⟩).append R
  refine ⟨1 + R.length, 1, q, ?_, Or.inl rfl, ?_⟩
  · omega
  · intro i
    have hpi := hp ⟨i.val, hidx i⟩
    have hmeet : ∀ z, z ∈ (p ⟨i.val, hidx i⟩).support → z ∈ R.support → z = u := by
      intro z hz hzR
      exact hRK z hzR (hpi.2.2 z hz)
    refine ⟨isPath_append_of_support_intersection _ R hpi.1 hR hmeet, ?_⟩
    change ((p ⟨i.val, hidx i⟩).append R).length = (1 + R.length) + i.val * 1
    have hpiLen : (p ⟨i.val, hidx i⟩).length = i.val + 1 := hpi.2.1
    rw [Walk.length_append, hpiLen]
    omega

theorem clique_card_le_of_no_admissible_paths [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (k : ℕ) (hG : TwoConnected G) (hK : G.IsClique K)
    (hx : x ∈ K) (hy : y ∉ K) (hk : 2 ≤ k)
    (hno : ¬HasAdmissiblePaths G x y k) : K.ncard ≤ k := by
  by_contra hlarge
  exact hno (large_clique_has_admissible_paths G K x y k hG hK hx hy hk (by omega))

#print axioms large_clique_has_admissible_paths
#print axioms clique_card_le_of_no_admissible_paths
end TaskH.Gao
