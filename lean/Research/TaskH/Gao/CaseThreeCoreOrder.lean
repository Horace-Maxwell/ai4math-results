import Research.TaskH.Gao.CaseThreeCorePaths
import Research.TaskH.Gao.ActualCliqueComponentEntry
import Research.TaskH.Gao.FamilyOperations

/-! The original counterexample internally forces t<k; no positive-IH count oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_actual_k_core_prefix [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (ht : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (k : ℕ) (hk : k ≤ K.ncard) (u : V)
    (hu : u ∈ insert x (insert p (insert q K))) (hux : u ≠ x) :
    ∃ a : ℕ, ∃ r : Fin k → G.Walk x u,
      AdmissiblePathFamily G x u k a 1 r ∧
        ∀ i z, z ∈ (r i).support → z ∈ insert x (insert p (insert q K)) := by
  classical
  have build : ∀ a : ℕ, 2 ≤ a →
      (∀ i : Fin k, ∃ r : G.Walk x u, r.IsPath ∧ r.length = a + i.val ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K))) →
      ∃ r : Fin k → G.Walk x u, AdmissiblePathFamily G x u k a 1 r ∧
        ∀ i z, z ∈ (r i).support → z ∈ insert x (insert p (insert q K)) := by
    intro a ha hex
    choose r hp hl hs using hex
    refine ⟨r, ⟨ha, Or.inl rfl, ?_⟩, hs⟩
    intro i
    refine ⟨hp i, ?_⟩
    have hh := hl i
    omega
  rcases hu with hux' | hup | huq | huK
  · exact False.elim (hux hux')
  · subst u
    have hex : ∀ i : Fin k, ∃ r : G.Walk x p, r.IsPath ∧ r.length = 3 + i.val ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
      intro i
      have hii := i.isLt
      obtain ⟨r, hr, hl, hs⟩ := case3_core_path_to_neighbor G x y p q K hK hsub ht
        exp exq hpq (3 + i.val) (by omega) (by omega)
      exact ⟨r, hr, hl, hs⟩
    obtain ⟨r, hr, hs⟩ := build 3 (by omega) hex
    exact ⟨3, r, hr, hs⟩
  · subst u
    have hswap : K ⊆ case3CoreDomain G x y q p := by
      rw [case3CoreDomain_swap G x y p q]
      exact hsub
    have hex : ∀ i : Fin k, ∃ r : G.Walk x q, r.IsPath ∧ r.length = 3 + i.val ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
      intro i
      have hii := i.isLt
      obtain ⟨r, hr, hl, hs⟩ := case3_core_path_to_neighbor G x y q p K hK hswap ht
        exq exp hpq.symm (3 + i.val) (by omega) (by omega)
      have hs' : ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
        intro z hz
        rcases hs z hz with he | he | he | hzK
        · exact Or.inl he
        · exact Or.inr (Or.inr (Or.inl he))
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr hzK))
      exact ⟨r, hr, hl, hs'⟩
    obtain ⟨r, hr, hs⟩ := build 3 (by omega) hex
    exact ⟨3, r, hr, hs⟩
  · have hex : ∀ i : Fin k, ∃ r : G.Walk x u, r.IsPath ∧ r.length = 2 + i.val ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
      intro i
      have hii := i.isLt
      exact case3_core_path_to_member G x y p q K hK hsub ht exp exq hpq u huK
        (2 + i.val) (by omega) (by omega)
    obtain ⟨r, hr, hs⟩ := build 2 (by omega) hex
    exact ⟨2, r, hr, hs⟩

theorem case3_actual_large_core_family [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (ht : 2 ≤ K.ncard)
    (hG : TwoConnected G) (hxy : x ≠ y) (hpy : p ≠ y) (hqy : q ≠ y)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (k : ℕ) (hk : k ≤ K.ncard) : HasAdmissiblePaths G x y k := by
  classical
  let T : Set V := insert x (insert p (insert q K))
  have hyT : y ∉ T := by
    rintro (hyx | hyp | hyq | hyK)
    · exact hxy hyx.symm
    · exact hpy hyp.symm
    · exact hqy hyq.symm
    · exact (hsub hyK).2.1 rfl
  have hKT : K ⊆ T := fun _ hz => Or.inr (Or.inr (Or.inr hz))
  have hTcard : 2 ≤ T.ncard := le_trans ht (Set.ncard_le_ncard hKT)
  let C := (G.induce Tᶜ).connectedComponentMk ⟨y, hyT⟩
  let yr : C.supp := ⟨⟨y, hyT⟩, rfl⟩
  obtain ⟨u, huT, hux, R, hR, _hRl, hRT⟩ :=
    actual_component_clique_entry_tail G T C x yr hG (Or.inl rfl) hTcard
  obtain ⟨a, r, hr, hs⟩ := case3_actual_k_core_prefix G x y p q K hK hsub ht
    exp exq hpq k hk u huT hux
  have hmeet : ∀ i z, z ∈ (r i).support → z ∈ R.support → z = u := by
    intro i z hz hzR
    exact hRT z hzR (hs i z hz)
  have hf := admissible_family_append_fixed_tail G x u y k a 1 r R hr hR hmeet
  exact ⟨a + R.length, 1, (fun i => (r i).append R), hf.1⟩

theorem case3_actual_core_card_lt_k [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (ht : 2 ≤ K.ncard)
    (hG : TwoConnected G) (hxy : x ≠ y) (hpy : p ≠ y) (hqy : q ≠ y)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (k : ℕ) (hno : ¬HasAdmissiblePaths G x y k) : K.ncard < k := by
  by_contra hn
  exact hno (case3_actual_large_core_family G x y p q K hK hsub ht hG hxy hpy hqy
    exp exq hpq k (by omega))

#print axioms case3_actual_k_core_prefix
#print axioms case3_actual_large_core_family
#print axioms case3_actual_core_card_lt_k
end TaskH.Gao
