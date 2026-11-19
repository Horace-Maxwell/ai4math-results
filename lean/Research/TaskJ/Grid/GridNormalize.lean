import Research.TaskJ.Grid.GridTransport
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Grid.Transport

open Challenge

def effective (ds : List ℕ) : List ℕ := ds.filter (fun d => !(d == 1))

theorem strip_maps (ds : List ℕ) :
    Nonempty (BoxMap ds (effective ds)) ∧ Nonempty (BoxMap (effective ds) ds) := by
  induction ds with
  | nil => exact ⟨⟨BoxMap.identity _⟩, ⟨BoxMap.identity _⟩⟩
  | cons d ds ih =>
    obtain ⟨⟨go⟩, ⟨back⟩⟩ := ih
    by_cases h : d = 1
    · subst d
      simpa [effective] using
        And.intro (Nonempty.intro ((BoxMap.eraseOne ds).trans go))
                  (Nonempty.intro (back.trans (BoxMap.addOne ds)))
    · simpa [effective, h] using
        And.intro (Nonempty.intro (go.cons d)) (Nonempty.intro (back.cons d))

theorem optimum_perm {a b : List ℕ} (h : a.Perm b) : optimumFormula a = optimumFormula b := by
  have ha : activeCount a = activeCount b := (h.filter _).length_eq
  have he : evenCount a = evenCount b := (h.filter _).length_eq
  have hw : (∃ x ∈ a, x % 2 = 0 ∧ 4 ≤ x) ↔ (∃ x ∈ b, x % 2 = 0 ∧ 4 ≤ x) := by
    simp only [h.mem_iff]
  have hu : rawUpper a = rawUpper b := by
    simp only [rawUpper, h.prod_eq]
    exact (h.map _).sum_eq
  simp only [optimumFormula, hu, gapFormula, ha, he, h.length_eq, hw]

private theorem active_zero {ds : List ℕ} (h : PositiveSides ds) :
    activeCount ds = 0 ↔ ds.prod = 1 := by
  induction ds with
  | nil => simp [activeCount]
  | cons d ds ih =>
    have hd : 0 < d := h d (by simp)
    have ht : PositiveSides ds := fun _ hx => h _ (List.mem_cons_of_mem _ hx)
    specialize ih ht
    by_cases hd1 : d = 1
    · subst d
      simpa [activeCount] using ih
    · have hgt : 1 < d := by omega
      have hn : d * ds.prod ≠ 1 := fun he => hd1 (Nat.eq_one_of_mul_eq_one_right he)
      simp [activeCount, hgt, hn]

theorem optimum_cons_one (ds : List ℕ) (h : PositiveSides ds) :
    optimumFormula (1 :: ds) = optimumFormula ds := by
  have hraw : rawUpper (1 :: ds) =
      (if ds.prod = 1 then (-1 : ℤ) else 0) + rawUpper ds := by
    by_cases hp : ds.prod = 1 <;> simp [rawUpper, rawTerm, hp]
  have hact : activeCount (1 :: ds) = activeCount ds := by simp [activeCount]
  have hev : evenCount (1 :: ds) = evenCount ds := by simp [evenCount]
  have hw : (∃ x ∈ 1 :: ds, x % 2 = 0 ∧ 4 ≤ x) ↔ ∃ x ∈ ds, x % 2 = 0 ∧ 4 ≤ x := by simp
  by_cases hz : activeCount ds = 0
  · have hp := (active_zero h).mp hz
    simp [optimumFormula, hraw, gapFormula, hact, hz, hp]
  · have hp : ds.prod ≠ 1 := fun hp => hz ((active_zero h).mpr hp)
    simp only [optimumFormula, hraw, hp, ↓reduceIte, zero_add, gapFormula, hact, hev, hw]
    rcases hk : activeCount ds with _ | _ | _ | k
    · exact (hz hk).elim
    all_goals rfl

theorem optimum_effective (ds : List ℕ) (h : PositiveSides ds) :
    optimumFormula (effective ds) = optimumFormula ds := by
  -- Move the axes of length one to the beginning and remove them there.
  let u := ds.filter (· == 1)
  have perm : (u ++ effective ds).Perm ds := by
    simpa [u, effective] using (List.filter_append_perm (· == 1) ds)
  have tailPos : PositiveSides (effective ds) := by
    intro x hx
    exact h x (List.mem_filter.mp hx).1
  have hu : ∀ x ∈ u, x = 1 := by
    intro x hx
    exact beq_iff_eq.mp (List.mem_filter.mp hx).2
  have remove : ∀ ones : List ℕ, (∀ x ∈ ones, x = 1) →
      optimumFormula (ones ++ effective ds) = optimumFormula (effective ds) := by
    intro ones
    induction ones with
    | nil => simp
    | cons x xs ih =>
      intro hall
      have hx := hall x (by simp)
      have ht : ∀ z ∈ xs, z = 1 := fun z hz => hall z (by simp [hz])
      have hpos : PositiveSides (xs ++ effective ds) := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rw [ht z hz]; decide
        · exact tailPos z hz
      subst x
      simpa only [List.cons_append, optimum_cons_one _ hpos] using ih ht
  exact (remove u hu).symm.trans (optimum_perm perm)

end Grid.Transport
