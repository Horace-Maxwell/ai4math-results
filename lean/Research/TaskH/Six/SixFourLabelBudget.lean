import Mathlib

/-!
Finite four-label excess bound for the degree-ten split branch. These are
conditional finite-set helpers; the original graph application must derive
the label intersection restriction and every three-clone bound from actual
rainbow hexagons before using them. No graph premise is added to CaseSix.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open scoped Classical

theorem disjoint_two_label_family_card_le_two
    (K : Finset (Finset (Fin 4)))
    (hsize : ∀ S ∈ K, S.card = 2)
    (hdisjoint : (K : Set (Finset (Fin 4))).PairwiseDisjoint id) : K.card ≤ 2 := by
  have hu := Finset.card_biUnion hdisjoint
  have hsum : (∑ S ∈ K, S.card) = 2 * K.card := by
    calc
      (∑ S ∈ K, S.card) = ∑ _S ∈ K, 2 := Finset.sum_congr rfl hsize
      _ = 2 * K.card := by simp [Nat.mul_comm]
  have hb : (K.biUnion id).card ≤ 4 := by
    simpa using (Finset.card_le_univ (K.biUnion id))
  rw [hu] at hb
  change (∑ S ∈ K, S.card) ≤ 4 at hb
  rw [hsum] at hb
  omega

theorem disjoint_large_and_double_labels_impossible
    (S T : Finset (Fin 4)) (hS : 3 ≤ S.card) (hT : 2 ≤ T.card)
    (hdisjoint : Disjoint S T) : False := by
  have hcard := Finset.card_union_of_disjoint hdisjoint
  have hbound : (S ∪ T).card ≤ 4 := by
    simpa using (Finset.card_le_univ (S ∪ T))
  omega

theorem four_label_total_weight_le_card_add_six
    {V : Type u} (T : Finset V) (L : V → Finset (Fin 4))
    (hintersection : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      2 ≤ (L x).card → 2 ≤ (L y).card →
      Disjoint (L x) (L y) ∨ (L x = L y ∧ (L x).card = 2))
    (hclones : ∀ S : Finset (Fin 4), S.card = 2 →
      (T.filter (fun x => L x = S)).card ≤ 3) :
    (∑ x ∈ T, (L x).card) ≤ T.card + 6 := by
  classical
  by_cases hlarge : ∃ z ∈ T, 3 ≤ (L z).card
  · obtain ⟨z, hz, hsz⟩ := hlarge
    have hother : ∀ x ∈ T, x ≠ z → (L x).card ≤ 1 := by
      intro x hx hxz
      by_contra hbad
      have hsx : 2 ≤ (L x).card := by omega
      rcases hintersection z hz x hx hxz.symm (by omega) hsx with hd | he
      · exact disjoint_large_and_double_labels_impossible (L z) (L x) hsz hsx hd
      · omega
    have hbound : ∀ x ∈ T, (L x).card ≤ 1 + if x = z then 3 else 0 := by
      intro x hx
      by_cases h : x = z
      · subst x
        have hc : (L z).card ≤ 4 := by simpa using (Finset.card_le_univ (L z))
        simpa using hc
      · simpa [h] using hother x hx h
    calc
      (∑ x ∈ T, (L x).card) ≤ ∑ x ∈ T, (1 + if x = z then 3 else 0) :=
        Finset.sum_le_sum hbound
      _ = T.card + 3 := by rw [Finset.sum_add_distrib]; simp [hz]
      _ ≤ T.card + 6 := by omega
  · have hle : ∀ x ∈ T, (L x).card ≤ 2 := by
      intro x hx
      by_contra hb
      exact hlarge ⟨x, hx, by omega⟩
    let M := T.filter (fun x => 2 ≤ (L x).card)
    let K := M.image L
    have hMT : M ⊆ T := Finset.filter_subset _ _
    have hMsize : ∀ x ∈ M, (L x).card = 2 := by
      intro x hx
      have hl := (Finset.mem_filter.mp hx).2
      have hu := hle x (hMT hx)
      omega
    have hKsize : ∀ S ∈ K, S.card = 2 := by
      intro S hS
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
      exact hMsize x hx
    have hKdisjoint : (K : Set (Finset (Fin 4))).PairwiseDisjoint id := by
      intro S hS U hU hne
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hU
      have hxy : x ≠ y := by intro he; subst y; exact hne rfl
      rcases hintersection x (hMT hx) y (hMT hy) hxy
        (hMsize x hx).ge (hMsize y hy).ge with hd | he
      · exact hd
      · exact False.elim (hne he.1)
    have hKcard := disjoint_two_label_family_card_le_two K hKsize hKdisjoint
    have hMf : ∀ S ∈ K, (M.filter (fun x => L x = S)).card ≤ 3 := by
      intro S hS
      apply (Finset.card_le_card ?_).trans (hclones S (hKsize S hS))
      intro x hx
      exact Finset.mem_filter.mpr ⟨hMT (Finset.mem_filter.mp hx).1,
        (Finset.mem_filter.mp hx).2⟩
    have hMcard : M.card ≤ 6 := by
      have hc := Finset.card_eq_sum_card_image L M
      have hs := Finset.sum_le_sum hMf
      have he : (∑ _S ∈ K, 3) = 3 * K.card := by simp [Nat.mul_comm]
      change M.card = ∑ S ∈ K, (M.filter (fun x => L x = S)).card at hc
      rw [← hc, he] at hs
      omega
    have hbound : ∀ x ∈ T, (L x).card ≤ 1 + if x ∈ M then 1 else 0 := by
      intro x hx
      by_cases hm : x ∈ M
      · simpa [hm] using hle x hx
      · have hs : ¬ 2 ≤ (L x).card := by
          intro hb
          exact hm (Finset.mem_filter.mpr ⟨hx, hb⟩)
        simp only [hm, ite_false, add_zero]
        omega
    have hind : (∑ x ∈ T, if x ∈ M then 1 else 0) = M.card := by
      have he : T.filter (fun x => x ∈ M) = M := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hMT h, h⟩⟩
      rw [← Finset.sum_filter]
      simp [he]
    calc
      (∑ x ∈ T, (L x).card) ≤ ∑ x ∈ T, (1 + if x ∈ M then 1 else 0) :=
        Finset.sum_le_sum hbound
      _ = T.card + M.card := by rw [Finset.sum_add_distrib, hind]; simp
      _ ≤ T.card + 6 := by omega

end TaskH.Six

#print axioms TaskH.Six.disjoint_two_label_family_card_le_two
#print axioms TaskH.Six.disjoint_large_and_double_labels_impossible
#print axioms TaskH.Six.four_label_total_weight_le_card_add_six
