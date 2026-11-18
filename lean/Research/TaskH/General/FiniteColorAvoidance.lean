import Mathlib

/-! Choosing an actual finite ordered color list from a palette complement.
The list is constructed from a real subset of the actual complement. -/

set_option autoImplicit false

namespace TaskH.General

theorem exists_color_list_avoiding_palette {k s : ℕ} (S : Finset (Fin k))
    (hcap : s + S.card ≤ k) :
    ∃ D : Fin s → Fin k, Function.Injective D ∧ ∀ i, D i ∉ S := by
  classical
  have hcard : (Sᶜ).card = k - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hs : s ≤ (Sᶜ).card := by rw [hcard]; omega
  obtain ⟨T, hT, hTs⟩ := Finset.exists_subset_card_eq hs
  let e : T ≃ Fin s := Finset.equivFinOfCardEq hTs
  let D : Fin s → Fin k := fun i => (e.symm i).val
  refine ⟨D, ?_, ?_⟩
  · intro i j he
    apply e.symm.injective
    exact Subtype.ext he
  · intro i
    exact Finset.mem_compl.mp (hT (e.symm i).property)

end TaskH.General

#print axioms TaskH.General.exists_color_list_avoiding_palette
