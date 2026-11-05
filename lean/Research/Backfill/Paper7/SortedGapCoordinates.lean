import Research.Backfill.Paper7.SortedBoundedTuples

/-! Source-only candidate. The gap domain is defined by complete finite ranges,
not by a candidate table. No numerical cardinality of this domain is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SortedGaps
open Paper7Budget Paper7SortedRows
open scoped BigOperators Classical

def gapCost (g : Fin 4 → ℕ) : ℕ :=
  4 * g 0 + 3 * g 1 + 2 * g 2 + g 3
#print axioms Paper7SortedGaps.gapCost

/-- All nonnegative gap coordinates with weighted budget at most B. -/
def gapFinset (B : ℕ) : Finset (Fin 4 → ℕ) :=
  (Finset.range (B / 4 + 1)).biUnion fun a =>
    (Finset.range ((B - 4 * a) / 3 + 1)).biUnion fun b =>
      (Finset.range ((B - 4 * a - 3 * b) / 2 + 1)).biUnion fun c =>
        (Finset.range (B - 4 * a - 3 * b - 2 * c + 1)).image fun d =>
          ![a, b, c, d]
#print axioms Paper7SortedGaps.gapFinset

theorem mem_gapFinset_iff (B : ℕ) (g : Fin 4 → ℕ) :
    g ∈ gapFinset B ↔ gapCost g ≤ B := by
  simp only [gapFinset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    dsimp [gapCost]
    omega
  · intro hg
    have h := hg
    unfold gapCost at h
    refine ⟨g 0, ?_, g 1, ?_, g 2, ?_, g 3, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · funext i
      fin_cases i <;> rfl
#print axioms Paper7SortedGaps.mem_gapFinset_iff

abbrev GapTuple (B : ℕ) := ↥(gapFinset B)
#print axioms Paper7SortedGaps.GapTuple

def prefixRow (g : Fin 4 → ℕ) : Fin 4 → ℕ :=
  ![g 0, g 0 + g 1, g 0 + g 1 + g 2, g 0 + g 1 + g 2 + g 3]
#print axioms Paper7SortedGaps.prefixRow

theorem prefixRow_sum (g : Fin 4 → ℕ) :
    (∑ i, prefixRow g i) = gapCost g := by
  rw [Fin.sum_univ_four]
  dsimp [prefixRow, gapCost]
  omega
#print axioms Paper7SortedGaps.prefixRow_sum

theorem prefixRow_monotone (g : Fin 4 → ℕ) : Monotone (prefixRow g) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [prefixRow]
  all_goals omega
#print axioms Paper7SortedGaps.prefixRow_monotone

def rowGaps (x : Fin 4 → ℕ) : Fin 4 → ℕ :=
  ![x 0, x 1 - x 0, x 2 - x 1, x 3 - x 2]
#print axioms Paper7SortedGaps.rowGaps

theorem rowGaps_prefixRow (g : Fin 4 → ℕ) : rowGaps (prefixRow g) = g := by
  funext i
  fin_cases i <;> dsimp [rowGaps, prefixRow]
  all_goals omega
#print axioms Paper7SortedGaps.rowGaps_prefixRow

theorem prefixRow_rowGaps (x : Fin 4 → ℕ) (hx : Monotone x) :
    prefixRow (rowGaps x) = x := by
  have h01 : x 0 ≤ x 1 := hx (by decide)
  have h12 : x 1 ≤ x 2 := hx (by decide)
  have h23 : x 2 ≤ x 3 := hx (by decide)
  funext i
  fin_cases i <;> dsimp [rowGaps, prefixRow]
  all_goals omega
#print axioms Paper7SortedGaps.prefixRow_rowGaps

theorem rowGaps_cost (x : Fin 4 → ℕ) (hx : Monotone x) :
    gapCost (rowGaps x) = ∑ i, x i := by
  rw [← prefixRow_sum (rowGaps x), prefixRow_rowGaps x hx]
#print axioms Paper7SortedGaps.rowGaps_cost

def gapToSorted {B : ℕ} (g : GapTuple B) : SortedTuple 4 B :=
  ⟨⟨prefixRow g.val, by
      rw [prefixRow_sum]
      exact (mem_gapFinset_iff B g.val).mp g.property⟩,
    prefixRow_monotone g.val⟩
#print axioms Paper7SortedGaps.gapToSorted

def sortedToGap {B : ℕ} (x : SortedTuple 4 B) : GapTuple B :=
  ⟨rowGaps x.val.val, by
    apply (mem_gapFinset_iff B _).mpr
    rw [rowGaps_cost x.val.val x.property]
    exact x.val.property⟩
#print axioms Paper7SortedGaps.sortedToGap

/-- Genuine two-sided equivalence; includes zero and repeated coordinates. -/
def gapEquivSorted (B : ℕ) : GapTuple B ≃ SortedTuple 4 B where
  toFun := gapToSorted
  invFun := sortedToGap
  left_inv g := by
    apply Subtype.ext
    exact rowGaps_prefixRow g.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact prefixRow_rowGaps x.val.val x.property
#print axioms Paper7SortedGaps.gapEquivSorted

theorem sum_sorted_eq_gap (B : ℕ) (f : SortedTuple 4 B → ℕ) :
    (∑ x : SortedTuple 4 B, f x) = ∑ g : GapTuple B, f (gapToSorted g) := by
  exact ((gapEquivSorted B).bijective.sum_comp f).symm
#print axioms Paper7SortedGaps.sum_sorted_eq_gap

end Paper7SortedGaps
