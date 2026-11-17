import Research.TaskH.Six.SixFiveCliqueLocal
import Research.TaskH.Six.SixOpenNeighborhoodPacking

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def fiveCliqueSet (q : Fin 5 → V) : Finset V := Finset.univ.image q

noncomputable def fiveCliqueSixSet (q : Fin 5 → V) (y : V) : Finset V :=
  insert y (fiveCliqueSet q)

noncomputable def fiveCliqueHooks (G : SimpleGraph V) (q : Fin 5 → V) (y : V) :
    Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj y (q i))

theorem mem_fiveCliqueSet (q : Fin 5 → V) (x : V) :
    x ∈ fiveCliqueSet q ↔ ∃ i : Fin 5, q i = x := by
  simp only [fiveCliqueSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem fiveCliqueSet_card (q : Fin 5 → V) (hq : Function.Injective q) :
    (fiveCliqueSet q).card = 5 := by
  rw [fiveCliqueSet, Finset.card_image_of_injective _ hq]
  simp

theorem fiveCliqueSixSet_eq_image (q : Fin 5 → V) (y : V) :
    fiveCliqueSixSet q y = Finset.univ.image (fiveCliqueWithPoint q y) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
    · obtain ⟨i, hi⟩ := (mem_fiveCliqueSet q x).mp hx
      exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _,
        (fiveCliqueWithPoint_castSucc q y i).trans hi⟩
  · intro hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_self _ _

theorem fiveCliqueSixSet_card (q : Fin 5 → V) (hq : Function.Injective q)
    (y : V) (hy : ∀ i, y ≠ q i) : (fiveCliqueSixSet q y).card = 6 := by
  classical
  have hyQ : y ∉ fiveCliqueSet q := by
    intro hm
    obtain ⟨i, hi⟩ := (mem_fiveCliqueSet q y).mp hm
    exact hy i hi.symm
  rw [fiveCliqueSixSet, Finset.card_insert_of_notMem hyQ, fiveCliqueSet_card q hq]

theorem fiveCliqueSet_reindex (q : Fin 5 → V) (ρ : Equiv.Perm (Fin 5)) :
    fiveCliqueSet (q ∘ ρ) = fiveCliqueSet q := by
  classical
  ext x
  simp only [mem_fiveCliqueSet, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ρ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨ρ.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

theorem fiveCliqueSixSet_reindex (q : Fin 5 → V) (ρ : Equiv.Perm (Fin 5)) (y : V) :
    fiveCliqueSixSet (q ∘ ρ) y = fiveCliqueSixSet q y := by
  rw [fiveCliqueSixSet, fiveCliqueSixSet, fiveCliqueSet_reindex]

variable [Fintype V] [DecidableRel G.Adj]

omit [Fintype V] in
theorem fiveCliqueTwoNeighbors_image (e : Fin 6 → V) (z : V) :
    packingNeighborsIn G (Finset.univ.image e) z =
      (fiveCliqueTwoNeighborIndices G e z).image e := by
  classical
  ext x
  simp only [packingNeighborsIn, fiveCliqueTwoNeighborIndices, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hzi⟩
    exact ⟨i, hzi, rfl⟩
  · rintro ⟨i, hzi, rfl⟩
    exact ⟨⟨i, rfl⟩, hzi⟩

omit [Fintype V] in
theorem fiveCliqueTwoNeighbors_card (e : Fin 6 → V) (he : Function.Injective e) (z : V) :
    (packingNeighborsIn G (Finset.univ.image e) z).card =
      (fiveCliqueTwoNeighborIndices G e z).card := by
  rw [fiveCliqueTwoNeighbors_image, Finset.card_image_of_injective _ he]

end TaskH.Six

#print axioms TaskH.Six.fiveCliqueSet
#print axioms TaskH.Six.fiveCliqueSixSet
#print axioms TaskH.Six.fiveCliqueHooks
#print axioms TaskH.Six.mem_fiveCliqueSet
#print axioms TaskH.Six.fiveCliqueSet_card
#print axioms TaskH.Six.fiveCliqueSixSet_eq_image
#print axioms TaskH.Six.fiveCliqueSixSet_card
#print axioms TaskH.Six.fiveCliqueSet_reindex
#print axioms TaskH.Six.fiveCliqueSixSet_reindex
#print axioms TaskH.Six.fiveCliqueTwoNeighbors_image
#print axioms TaskH.Six.fiveCliqueTwoNeighbors_card
