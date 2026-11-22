import Research.TaskR.A7.Challenge
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.SuccPred

namespace TaskR.A7

open Challenge

theorem fromMatching (a : Fin 2520 ≃ G) (h0 : a 0 = 1) (σ : Fin 2519 ≃ Fin 2519)
    (hm : ∀ i, difference a i = a (σ i).succ ∨ difference a i = (a (σ i).succ)⁻¹) :
    HasTerrace := by
  classical
  refine ⟨a, h0, ?_⟩
  intro g hg
  let s : Finset G := {g, g⁻¹}
  have orbit (i : Fin 2519) :
      (difference a i = g ∨ difference a i = g⁻¹) ↔ a (σ i).succ ∈ s := by
    simp only [s, Finset.mem_insert, Finset.mem_singleton]
    rcases hm i with h | h
    · rw [h]
    · rw [h]
      constructor
      · rintro (H|H)
        · exact Or.inr (by simpa using congrArg Inv.inv H)
        · exact Or.inl (by simpa using congrArg Inv.inv H)
      · rintro (H|H)
        · exact Or.inr (congrArg Inv.inv H)
        · exact Or.inl (by simp [H])
  let f (i : {i : Fin 2519 // difference a i = g ∨ difference a i = g⁻¹}) :
      ↥s := ⟨a (σ i.val).succ, (orbit i.val).mp i.property⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    exact Subtype.ext (σ.injective (Fin.succ_injective _ (a.injective h)))
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x.val ≠ 1 := by
      have h := x.property
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h|h <;> simpa [h] using hg
    have hn : a.symm x.val ≠ 0 := by
      intro h
      exact hx ((a.apply_symm_apply x.val).symm.trans ((congrArg a h).trans h0))
    obtain ⟨j,hj⟩ := Fin.exists_succ_eq_of_ne_zero hn
    have he : a (σ (σ.symm j)).succ = x.val := by
      rw [σ.apply_symm_apply, hj, a.apply_symm_apply]
    refine ⟨⟨σ.symm j, (orbit _).mpr (he ▸ x.property)⟩, Subtype.ext he⟩
  rw [Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Fintype.card_coe]
  by_cases h : g = g⁻¹
  · rw [ite_eq_left h]
    change ({g, g⁻¹} : Finset G).card = 1
    rw [← h, Finset.insert_eq_of_mem (Finset.mem_singleton_self g), Finset.card_singleton]
  · simp [s, h]

end TaskR.A7
