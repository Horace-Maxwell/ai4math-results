import Research.TaskV.Durer.Challenge
import Mathlib.Tactic.NormNum

namespace DurerDV

private noncomputable def twoPanelValue (h t : ℝ) : ℝ :=
  min h (h + (1 - t) / 10)

private theorem at_left (h t : ℝ) :
    twoPanelValue h t = h ↔ t ≤ 1 := by
  change min h (h + (1 - t) / 10) = h ↔ _
  rw [min_eq_left_iff]
  constructor <;> intro h' <;> linarith

private theorem at_right (h t : ℝ) :
    twoPanelValue h t = h + (1 - t) / 10 ↔ 1 ≤ t := by
  change min h (h + (1 - t) / 10) = _ ↔ _
  rw [min_eq_right_iff]
  constructor <;> intro h' <;> linarith

private noncomputable def twoPanel (h : ℝ) : Profile where
  count := 2
  length := 2
  knot i := i
  value := twoPanelValue h
  slope i := if i = 0 then 0 else -(1 / 10)
  count_pos := by decide
  length_pos := by norm_num
  first := by norm_num
  last := by norm_num
  increasing := by
    intro i j hij _
    exact_mod_cast hij
  covers := by
    intro t ht ht'
    by_cases hmid : t ≤ 1
    · exact ⟨0, by decide, by simpa using ht, by simpa using hmid⟩
    · exact ⟨1, by decide, by simpa using (le_of_not_ge hmid : (1:ℝ) ≤ t), by norm_num at *; assumption⟩
  support := by
    intro i hi t _ _
    have cases' : i = 0 ∨ i = 1 := by omega
    rcases cases' with rfl | rfl <;> norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_add, ite_true, ite_false]
    · change twoPanelValue h t ≤ twoPanelValue h 0 + 0 * (t - 0)
      rw [(at_left h 0).2 (by norm_num), zero_mul, add_zero]
      exact min_le_left _ _
    · change twoPanelValue h t ≤ twoPanelValue h 1 + -(1 / 10) * (t - 1)
      rw [(at_left h 1).2 le_rfl]
      have bound : twoPanelValue h t ≤ h + (1 - t) / 10 := min_le_right _ _
      linarith
  exposed := by
    intro i hi t ht ht'
    have cases' : i = 0 ∨ i = 1 := by omega
    rcases cases' with rfl | rfl <;> norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_add, ite_true, ite_false]
    · change twoPanelValue h t = twoPanelValue h 0 + 0 * (t - 0) ↔
          0 ≤ t ∧ t ≤ 1
      rw [(at_left h 0).2 (by norm_num), zero_mul, add_zero, at_left,
        and_iff_right ht]
    · change twoPanelValue h t = twoPanelValue h 1 + -(1 / 10) * (t - 1) ↔
          1 ≤ t ∧ t ≤ 2
      rw [(at_left h 1).2 le_rfl, and_iff_left ht']
      have eqn : h + -(1 / 10) * (t - 1) = h + (1 - t) / 10 := by ring
      rw [eqn, at_right]

theorem obliqueExample : ObliqueExample := by
  let model : Solid := {
    upper := twoPanel 3
    lower := twoPanel 0
    c := -(1 / 2)
    c_min := by norm_num
    c_max := by norm_num
    gap := by
      intro x y _ hx _ hy
      change x ≤ 2 at hx
      change y ≤ 2 at hy
      change -min 0 (0 + (1 - y) / 10) < min 3 (3 + (1 - x) / 10)
      rw [lt_min_iff]
      constructor <;> rw [neg_lt] <;> rw [lt_min_iff] <;> constructor <;> linarith
  }
  refine ⟨model, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro t _
    rfl
  · intro t _
    change -min 0 (0 + (1 - t) / 10) = max 0 ((t - 1) / 10)
    by_cases h : t ≤ 1
    · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      exact neg_zero
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      ring

#print axioms obliqueExample

end DurerDV
