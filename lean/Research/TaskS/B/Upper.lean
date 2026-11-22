import Research.TaskS.B.BasisCoordinates
import Research.TaskS.B.Hull
import Research.TaskS.B.Balanced

open scoped BigOperators
open Finset
namespace TaskS.B.Upper
open Challenge

theorem upper (n i : ℕ) (hi : 0 < i) (_hin : i ≤ n)
    (p : Space n →ₗ[ℝ] Space i) (hp : LatticeProjection p) : Covers p ((i : ℝ)/2) := by
  intro y
  obtain ⟨t, rfl⟩ := hp.1 y
  obtain ⟨x, rfl⟩ := Coordinates.decompose n t
  obtain ⟨b, A, he⟩ := Coordinates.intcoords p hp
  obtain ⟨h, hh, hcost⟩ := round_matrix A (Coordinates.balanced p b A he (Hull.sum_vertex n)) x
  let a := fun j => Int.fract (x j + h j)
  obtain ⟨v,hv,heq⟩ := Hull.scaled a (fun j => Int.fract_nonneg _) (by positivity) hcost
  obtain ⟨z,hz⟩ := Coordinates.lift_int (fun j => ⌊x j + h j⌋)
  refine ⟨z,v,hv,?_⟩
  rw [← map_smul, heq, hz, ← map_add]
  have hh' := Coordinates.annihilates p b A he h hh
  have hs : (∑ j, (⌊x j + h j⌋ : ℝ) • vertex n j) + (∑ j, a j • vertex n j) =
      (∑ j, x j • vertex n j) + (∑ j, h j • vertex n j) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp only [← add_smul, a, Int.floor_add_fract]
  rw [hs, map_add, hh', add_zero]

end TaskS.B.Upper
