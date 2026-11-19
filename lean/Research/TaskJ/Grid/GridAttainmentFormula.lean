import Research.TaskJ.Grid.GridUpper

namespace Grid.Attainment

open Challenge

/-- Twice the radial deficit of an optimal open path with k nonzero binary sign coordinates. -/
def evenCost (k : ℕ) : ℤ := 2*k + 2*((2:ℤ)^(k-1)-1)

def requiredCost (ds : List ℕ) : ℤ := 2*(mass ds - optimumFormula ds)

theorem from_cost {ds : List ℕ} {p : List Point} {cost : ℤ}
    (hc : 2*(pathLength p : ℤ) + cost = 2*mass ds) (hf : requiredCost ds = cost) :
    (pathLength p : ℤ) = optimumFormula ds := by
  unfold requiredCost at hf
  linarith

theorem witness_at_cost {ds : List ℕ} {cost : ℤ}
    (w : ∃ p, Order ds p ∧ 2*(pathLength p : ℤ) + cost = 2*mass ds)
    (hf : requiredCost ds = cost) :
    ∃ p, Order ds p ∧ (pathLength p : ℤ) = optimumFormula ds := by
  obtain ⟨p,hp,he⟩ := w
  exact ⟨p,hp,from_cost he hf⟩

theorem empty_order : ∃ p, Order [] p ∧ (pathLength p : ℤ) = optimumFormula [] :=
  ⟨[[]], List.Perm.refl _, rfl⟩

theorem single_cost (d : ℕ) (hd : 1 < d) : requiredCost [d] = 2 := by
  rw [requiredCost, optimum_one d hd]
  ring

theorem high_odd {ds : List ℕ} (h : PositiveSides ds) (ha : 3 ≤ activeCount ds)
    (he : evenCount ds = 0) : requiredCost ds = 2 := by
  simp [requiredCost, optimum_high h ha, he]

theorem high_even {ds : List ℕ} (h : PositiveSides ds) (ha : 3 ≤ activeCount ds)
    (he : evenCount ds ≠ 0) : requiredCost ds = evenCost (evenCount ds) := by
  simp [requiredCost, optimum_high h ha, evenCost, he]
  ring

theorem plane_odd {ds : List ℕ} (h : PositiveSides ds) (ha : activeCount ds = 2)
    (he : evenCount ds = 0) : requiredCost ds = 2 := by
  simp [requiredCost, optimumFormula, raw_multi h (by omega), gapFormula, ha, he]

theorem plane_even {ds : List ℕ} (h : PositiveSides ds) (ha : activeCount ds = 2)
    (he : evenCount ds = 2) : requiredCost ds = evenCost 2 := by
  simp [requiredCost, optimumFormula, raw_multi h (by omega), gapFormula, ha, he, evenCost]
  ring

theorem plane_wide {ds : List ℕ} (h : PositiveSides ds) (ha : activeCount ds = 2)
    (he : evenCount ds = 1) (hw : ∃ d ∈ ds, d%2=0 ∧ 4 ≤ d) : requiredCost ds = 2 := by
  simp [requiredCost, optimumFormula, raw_multi h (by omega), gapFormula, ha, he, hw]

theorem plane_narrow {ds : List ℕ} (h : PositiveSides ds) (ha : activeCount ds = 2)
    (he : evenCount ds = 1) (hw : ¬∃ d ∈ ds, d%2=0 ∧ 4 ≤ d) : requiredCost ds = 4 := by
  simp [requiredCost, optimumFormula, raw_multi h (by omega), gapFormula, ha, he, hw]
  ring

end Grid.Attainment
