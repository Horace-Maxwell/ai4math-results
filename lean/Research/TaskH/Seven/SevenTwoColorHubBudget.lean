import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-! Finite two-hub argument with the coincident-hub cases retained. The
actual graph transport into its forbidden-label premise is supplied separately. -/

set_option autoImplicit false
universe u v
namespace TaskH.Seven
open scoped Classical
variable {W : Type u} {L : Type v}

theorem twoColor_three_labels_avoid_one (s : Finset L) (hs : 3 ≤ s.card) (l : L) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ i ≠ l ∧ j ≠ l := by
  classical
  have htwo : 1 < (s.erase l).card := by
    by_cases hl : l ∈ s
    · have hc := Finset.card_erase_add_one hl
      omega
    · rw [Finset.erase_eq_of_notMem hl]
      omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
  exact ⟨i, (Finset.mem_erase.mp hi).2, j, (Finset.mem_erase.mp hj).2,
    hij, (Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp hj).1⟩

theorem twoColor_hub_labels_subset (U T : Finset W) (S : W → Finset L)
    (hforbid : ∀ z ∈ U, ∀ t ∈ T, z ≠ t →
      ∀ i ∈ S z, ∀ j ∈ S z, i ≠ j → ∀ l ∈ S t, l ≠ i → l ≠ j → False)
    {z t : W} (hz : z ∈ U) (ht : t ∈ T) (hzt : z ≠ t)
    (hcard : 2 ≤ (S z).card) : S t ⊆ S z := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (S z).card)
  intro l hl
  by_contra hn
  have hli : l ≠ i := fun he => hn (he.symm ▸ hi)
  have hlj : l ≠ j := fun he => hn (he.symm ▸ hj)
  exact hforbid z hz t ht hzt i hi j hj hij l hl hli hlj

theorem twoColor_two_hubs_own_pool_card_le_one
    (U T : Finset W) (S : W → Finset L)
    (hU : U.card ≤ 2) (hcover : 4 ≤ (U.biUnion S).card)
    (hT : ∀ t ∈ T, (S t).Nonempty)
    (hforbid : ∀ z ∈ U, ∀ t ∈ T, z ≠ t →
      ∀ i ∈ S z, ∀ j ∈ S z, i ≠ j → ∀ l ∈ S t, l ≠ i → l ≠ j → False) :
    T.card ≤ 1 := by
  classical
  by_cases hbig : ∃ z ∈ U, 3 ≤ (S z).card
  · obtain ⟨z, hz, hzcard⟩ := hbig
    have heq : ∀ t ∈ T, t = z := by
      intro t ht
      by_contra htz
      obtain ⟨l, hl⟩ := hT t ht
      obtain ⟨i, hi, j, hj, hij, hil, hjl⟩ := twoColor_three_labels_avoid_one (S z) hzcard l
      exact hforbid z hz t ht (Ne.symm htz) i hi j hj hij l hl
        (Ne.symm hil) (Ne.symm hjl)
    apply Finset.card_le_one.mpr
    intro t ht t' ht'
    exact (heq t ht).trans (heq t' ht').symm
  · have hsmall : ∀ z ∈ U, (S z).card ≤ 2 := by
      intro z hz
      by_contra hn
      exact hbig ⟨z, hz, by omega⟩
    have hbound := Finset.card_biUnion_le_card_mul U S 2 hsmall
    have hUtwo : U.card = 2 := by omega
    obtain ⟨z, z', hzz', hUeq⟩ := Finset.card_eq_two.mp hUtwo
    have hz : z ∈ U := by rw [hUeq]; simp
    have hz' : z' ∈ U := by rw [hUeq]; simp
    have hunion : 4 ≤ (S z ∪ S z').card := by simpa [hUeq] using hcover
    have hsz := hsmall z hz
    have hsz' := hsmall z' hz'
    have hule := Finset.card_union_le (S z) (S z')
    have hsz2 : (S z).card = 2 := by omega
    have hsz'2 : (S z').card = 2 := by omega
    have hc := Finset.card_union_add_card_inter (S z) (S z')
    have hinter : (S z ∩ S z').card = 0 := by omega
    have hd : Disjoint (S z) (S z') :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter)
    have hempty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨l, hl⟩ := hT t ht
      have hlz : l ∈ S z := by
        by_cases htz : t = z
        · simpa only [htz] using hl
        · exact twoColor_hub_labels_subset U T S hforbid hz ht (Ne.symm htz) hsz2.ge hl
      have hlz' : l ∈ S z' := by
        by_cases htz' : t = z'
        · simpa only [htz'] using hl
        · exact twoColor_hub_labels_subset U T S hforbid hz' ht (Ne.symm htz') hsz'2.ge hl
      exact Finset.disjoint_left.mp hd hlz hlz'
    simp only [hempty, Finset.card_empty]
    omega

end TaskH.Seven
#print axioms TaskH.Seven.twoColor_three_labels_avoid_one
#print axioms TaskH.Seven.twoColor_hub_labels_subset
#print axioms TaskH.Seven.twoColor_two_hubs_own_pool_card_le_one
