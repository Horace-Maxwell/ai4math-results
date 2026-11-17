import Research.TaskH.Seven.SevenK6CliqueLocal
import Research.TaskH.Six.SixOpenNeighborhoodPacking

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Six
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def sixCliqueSet (q : Fin 6 → V) : Finset V := Finset.univ.image q

noncomputable def sixCliqueSevenSet (q : Fin 6 → V) (y : V) : Finset V :=
  insert y (sixCliqueSet q)

noncomputable def sixCliqueHooks (G : SimpleGraph V) (q : Fin 6 → V) (y : V) :
    Finset (Fin 6) := Finset.univ.filter (fun i => G.Adj y (q i))

theorem mem_sixCliqueSet (q : Fin 6 → V) (x : V) :
    x ∈ sixCliqueSet q ↔ ∃ i : Fin 6, q i = x := by
  simp only [sixCliqueSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem sixCliqueSet_card (q : Fin 6 → V) (hq : Function.Injective q) :
    (sixCliqueSet q).card = 6 := by
  rw [sixCliqueSet, Finset.card_image_of_injective _ hq]
  simp

theorem sixCliqueSevenSet_eq_image (q : Fin 6 → V) (y : V) :
    sixCliqueSevenSet q y = Finset.univ.image (sixCliqueWithPoint q y) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
    · obtain ⟨i, hi⟩ := (mem_sixCliqueSet q x).mp hx
      exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _,
        (sixCliqueWithPoint_castSucc q y i).trans hi⟩
  · intro hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_self _ _

theorem sixCliqueSevenSet_card (q : Fin 6 → V) (hq : Function.Injective q)
    (y : V) (hy : ∀ i, y ≠ q i) : (sixCliqueSevenSet q y).card = 7 := by
  classical
  have hyQ : y ∉ sixCliqueSet q := by
    intro hm
    obtain ⟨i, hi⟩ := (mem_sixCliqueSet q y).mp hm
    exact hy i hi.symm
  rw [sixCliqueSevenSet, Finset.card_insert_of_notMem hyQ, sixCliqueSet_card q hq]

theorem sixCliqueSet_reindex (q : Fin 6 → V) (ρ : Equiv.Perm (Fin 6)) :
    sixCliqueSet (q ∘ ρ) = sixCliqueSet q := by
  classical
  ext x
  simp only [mem_sixCliqueSet, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ρ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨ρ.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

theorem sixCliqueSevenSet_reindex (q : Fin 6 → V) (ρ : Equiv.Perm (Fin 6)) (y : V) :
    sixCliqueSevenSet (q ∘ ρ) y = sixCliqueSevenSet q y := by
  rw [sixCliqueSevenSet, sixCliqueSevenSet, sixCliqueSet_reindex]

variable [Fintype V] [DecidableRel G.Adj]

omit [Fintype V] in
theorem sixCliqueTwoNeighbors_image (e : Fin 7 → V) (z : V) :
    packingNeighborsIn G (Finset.univ.image e) z =
      (sixCliqueTwoNeighborIndices G e z).image e := by
  classical
  ext x
  simp only [packingNeighborsIn, sixCliqueTwoNeighborIndices, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hzi⟩
    exact ⟨i, hzi, rfl⟩
  · rintro ⟨i, hzi, rfl⟩
    exact ⟨⟨i, rfl⟩, hzi⟩

omit [Fintype V] in
theorem sixCliqueTwoNeighbors_card (e : Fin 7 → V) (he : Function.Injective e) (z : V) :
    (packingNeighborsIn G (Finset.univ.image e) z).card =
      (sixCliqueTwoNeighborIndices G e z).card := by
  rw [sixCliqueTwoNeighbors_image, Finset.card_image_of_injective _ he]

end TaskH.Seven

#print axioms TaskH.Seven.sixCliqueSet
#print axioms TaskH.Seven.sixCliqueSevenSet
#print axioms TaskH.Seven.sixCliqueHooks
#print axioms TaskH.Seven.mem_sixCliqueSet
#print axioms TaskH.Seven.sixCliqueSet_card
#print axioms TaskH.Seven.sixCliqueSevenSet_eq_image
#print axioms TaskH.Seven.sixCliqueSevenSet_card
#print axioms TaskH.Seven.sixCliqueSet_reindex
#print axioms TaskH.Seven.sixCliqueSevenSet_reindex
#print axioms TaskH.Seven.sixCliqueTwoNeighbors_image
#print axioms TaskH.Seven.sixCliqueTwoNeighbors_card
