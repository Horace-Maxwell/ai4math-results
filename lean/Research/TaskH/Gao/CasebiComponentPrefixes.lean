import Research.TaskH.Gao.BipartitePrefixFamily
import Research.TaskH.Gao.BicliqueLexicographicSelection
import Research.TaskH.Gao.ActualCliqueComponentEntry
import Research.TaskH.Gao.FamilyOperations

/-! Actual original Casebi prefixes and the strict positive-count budget. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_set_odd_prefix [Finite V] (G : SimpleGraph V)
    (A B : Set V) (r : ℕ) (x z : V) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hz : z ∈ A) (hA : r ≤ A.ncard) (hB : r ≤ B.ncard) :
    ∃ P : Fin r → G.Walk x z, ∀ i, (P i).IsPath ∧
      (P i).length = 1 + i.val * 2 ∧ ∀ w ∈ (P i).support, w ∈ A ∪ B := by
  classical
  let FA := (Set.toFinite A).toFinset
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard := (Set.ncard_eq_toFinset_card A (Set.toFinite A)).symm
  have hFB : FB.card = B.ncard := (Set.ncard_eq_toFinset_card B (Set.toFinite B)).symm
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    exact Set.disjoint_left.mp hAB ((Set.toFinite A).mem_toFinset.mp hwA)
      ((Set.toFinite B).mem_toFinset.mp hwB)
  obtain ⟨P, hP⟩ := bipartite_odd_prefix_family FA FB r x z hdis
    (fun a ha b hb => hc a ((Set.toFinite A).mem_toFinset.mp ha)
      b ((Set.toFinite B).mem_toFinset.mp hb))
    ((Set.toFinite B).mem_toFinset.mpr hx) ((Set.toFinite A).mem_toFinset.mpr hz)
    (by omega) (by omega)
  refine ⟨P, ?_⟩
  intro i
  obtain ⟨hp, hl, hs⟩ := hP i
  refine ⟨hp, by omega, ?_⟩
  intro w hw
  exact (hs w hw).elim
    (fun h => Or.inl ((Set.toFinite A).mem_toFinset.mp h))
    (fun h => Or.inr ((Set.toFinite B).mem_toFinset.mp h))

theorem casebi_set_even_prefix [Finite V] (G : SimpleGraph V)
    (A B : Set V) (r : ℕ) (x z : V) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hz : z ∈ B) (hxz : x ≠ z)
    (hA : r ≤ A.ncard) (hB : r + 1 ≤ B.ncard) :
    ∃ P : Fin r → G.Walk x z, ∀ i, (P i).IsPath ∧
      (P i).length = 2 + i.val * 2 ∧ ∀ w ∈ (P i).support, w ∈ A ∪ B := by
  classical
  let FA := (Set.toFinite A).toFinset
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard := (Set.ncard_eq_toFinset_card A (Set.toFinite A)).symm
  have hFB : FB.card = B.ncard := (Set.ncard_eq_toFinset_card B (Set.toFinite B)).symm
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    exact Set.disjoint_left.mp hAB ((Set.toFinite A).mem_toFinset.mp hwA)
      ((Set.toFinite B).mem_toFinset.mp hwB)
  obtain ⟨P, hP⟩ := bipartite_even_prefix_family FA FB r x z hdis
    (fun a ha b hb => hc a ((Set.toFinite A).mem_toFinset.mp ha)
      b ((Set.toFinite B).mem_toFinset.mp hb))
    ((Set.toFinite B).mem_toFinset.mpr hx) ((Set.toFinite B).mem_toFinset.mpr hz) hxz
    (by omega) (by omega)
  refine ⟨P, ?_⟩
  intro i
  obtain ⟨hp, hl, hs⟩ := hP i
  refine ⟨hp, by omega, ?_⟩
  intro w hw
  exact (hs w hw).elim
    (fun h => Or.inl ((Set.toFinite A).mem_toFinset.mp h))
    (fun h => Or.inr ((Set.toFinite B).mem_toFinset.mp h))

theorem casebi_prefix_and_actual_tail (G : SimpleGraph V) (Q : Set V)
    (x z y : V) (r a d : ℕ) (P : Fin r → G.Walk x z)
    (hP : ∀ i, (P i).IsPath ∧ (P i).length = a + i.val * d ∧
      ∀ w ∈ (P i).support, w ∈ Q)
    (hd : d = 1 ∨ d = 2) (R : G.Walk z y) (hR : R.IsPath)
    (hRQ : ∀ w ∈ R.support, w ∈ Q → w = z) (ha : 2 ≤ a + R.length) :
    HasAdmissiblePaths G x y r := by
  refine ⟨a + R.length, d, (fun i => (P i).append R), ha, hd, ?_⟩
  intro i
  constructor
  · exact append_isPath_of_only_common_endpoint (hP i).1 hR
      (fun w hwP hwR => hRQ w hwR ((hP i).2.2 w hwP))
  · rw [Walk.length_append, (hP i).2.1]
    omega

theorem casebi_counterexample_part_lt_k [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hQ : CasebiBiclique G x y A B) (hBs : B.ncard = s + 1)
    (hG : TwoConnected G) (hno : ¬HasAdmissiblePaths G x y k) : s < k := by
  classical
  let Q := A ∪ B
  have hyQ : y ∉ Q := hQ.2.2.2.1
  let C := (G.induce Qᶜ).connectedComponentMk ⟨y, hyQ⟩
  let yr : C.supp := ⟨⟨y, hyQ⟩, rfl⟩
  have hQcard : 2 ≤ Q.ncard := le_trans hQ.2.2.2.2.1
    (Set.ncard_le_ncard (show B ⊆ Q from Set.subset_union_right))
  obtain ⟨z, hzQ, hzx, R, hR, hRpos, hRQ⟩ :=
    actual_component_clique_entry_tail G Q C x yr hG (Or.inr hQ.2.2.1) hQcard
  by_contra hn
  have hks : k ≤ s := by omega
  rcases hzQ with hzA | hzB
  · obtain ⟨P, hP⟩ := casebi_set_odd_prefix G A B k x z hQ.1 hQ.2.1 hQ.2.2.1 hzA
      (by have hh := hQ.2.2.2.2.2; omega) (by omega)
    exact hno (casebi_prefix_and_actual_tail G Q x z y k 1 2 P hP (Or.inr rfl)
      R hR hRQ (by omega))
  · obtain ⟨P, hP⟩ := casebi_set_even_prefix G A B k x z hQ.1 hQ.2.1 hQ.2.2.1 hzB hzx.symm
      (by have hh := hQ.2.2.2.2.2; omega) (by omega)
    exact hno (casebi_prefix_and_actual_tail G Q x z y k 2 2 P hP (Or.inr rfl)
      R hR hRQ (by omega))

#print axioms casebi_set_odd_prefix
#print axioms casebi_set_even_prefix
#print axioms casebi_prefix_and_actual_tail
#print axioms casebi_counterexample_part_lt_k
end TaskH.Gao
