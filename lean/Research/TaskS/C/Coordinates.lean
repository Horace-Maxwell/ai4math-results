import Research.TaskS.C.Challenge

namespace TaskS.C

open Challenge Set
open scoped BigOperators

theorem origin_row {d : ℕ} (v : Fin (d+1) → Space d) (β : Fin (d+1) → ℝ)
    (hs : ∑ i, β i = 1) (hz : ∑ i, β i • v i = 0) :
    (∑ k, β k • Fin.cons (1 : ℝ) (v k)) = Fin.cons (1 : ℝ) (0 : Space d) := by
  ext j
  refine Fin.cases ?_ (fun a => ?_) j
  · simpa [Finset.sum_apply] using hs
  · simpa [Finset.sum_apply] using congrFun hz a

/-- A full-dimensional simplex with an interior origin supplies strictly positive
coordinates for zero and a representation of every real point. -/
theorem coordinates {d : ℕ} (v : Fin (d+1) → Space d)
    (hi : (0 : Space d) ∈ interior (simplex v)) :
    ∃ β : Fin (d+1) → ℝ, (∀ i, 0 < β i) ∧ ∑ i, β i = 1 ∧
      (∑ i, β i • v i = 0) ∧ ∀ y : Space d, ∃ a : Fin (d+1) → ℝ, ∑ i, a i • v i = y := by
  have ht : affineSpan ℝ (range v) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp ⟨0, hi⟩
  have hind : AffineIndependent ℝ v := by
    rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ v (Fintype.card_fin _),
      ← direction_affineSpan, ht, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let b : AffineBasis (Fin (d+1)) ℝ (Space d) := ⟨v, hind, ht⟩
  change (0 : Space d) ∈ interior (convexHull ℝ (range b)) at hi
  rw [b.interior_convexHull] at hi
  exact ⟨fun i => b.coord i 0, hi, b.sum_coord_apply_eq_one 0,
    b.linear_combination_coord_eq_self 0, fun y =>
      ⟨fun i => b.coord i y, b.linear_combination_coord_eq_self y⟩⟩

end TaskS.C
