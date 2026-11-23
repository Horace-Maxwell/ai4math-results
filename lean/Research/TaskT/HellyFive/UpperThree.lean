import Research.TaskT.HellyFive.UpperThreeTable
import Research.TaskT.HellyFive.UpperGeom

namespace TaskT.HellyFive.UpperFive
open FiniteGeometry

theorem indexedWeight_perm {n : ℕ} (f : Fin 5 → Color n) (e : Equiv.Perm (Fin 5))
    (r : Color n) : indexedWeight (f ∘ e) r = indexedWeight f r := by
  unfold indexedWeight
  conv_rhs => rw [← Finset.map_univ_equiv e]
  rw [Finset.powersetCard_map, Finset.filter_map, Finset.card_map]
  congr 1

theorem three_capacity (f : Fin 5 → Color 3) :
    ∑ r, capacity (indexedWeight f r) ≤ 23 := by
  let g : Fin 5 → Fin 8 := fun i => encode (f i)
  let e := Tuple.sort g
  let u := g ∘ e
  have inc : Monotone u := Tuple.monotone_sort g
  have h := sorted_table (u 0) (u 1) (u 2) (u 3) (u 4)
    (inc (by decide : (0 : Fin 5) ≤ 1)) (inc (by decide : (1 : Fin 5) ≤ 2))
    (inc (by decide : (2 : Fin 5) ≤ 3)) (inc (by decide : (3 : Fin 5) ≤ 4))
  have he : ![unpack (u 0),unpack (u 1),unpack (u 2),unpack (u 3),unpack (u 4)] = f ∘ e := by
    funext i
    fin_cases i <;> exact unpack_encode _
  unfold boundCode at h
  simpa only [he, indexedWeight_perm] using h

theorem three_upper (V : Finset (Grid 3)) (hk : (otherGrid V).ncard ≤ 5) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ 23 := by
  apply apply_bound V hk
  intro s X hX h
  obtain ⟨f,hf⟩ := indexed_cover (by decide : 0 < 3) X hX
  calc
    s.card = ∑ r : Color 3, (fiber s r).card := card_sum_fibers _
    _ ≤ ∑ r, capacity (indexedWeight f r) :=
      Finset.sum_le_sum fun r _ => card_le_capacity ((charge r h).trans (hf r)) (indexedWeight_le_ten _ _)
    _ ≤ _ := three_capacity f

theorem upper_of_poly {n : ℕ} (hn : 3 ≤ n) (V : Finset (Grid n)) (hk : (otherGrid V).ncard ≤ 5) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ value n + 5 := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact three_upper V hk
  · simpa [value, show n ≠ 1 by omega,show n ≠ 2 by omega,show n ≠ 3 by omega, Nat.add_assoc] using high_upper V hk

end TaskT.HellyFive.UpperFive
