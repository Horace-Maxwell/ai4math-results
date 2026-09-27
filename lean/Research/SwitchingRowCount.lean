import Mathlib

/-!
# The counting step of the Row Lemmas (switching conjecture, trees of diameter ≤ 4)

Session 3 of `work/round6/switching` (PROOF.md §9.15).  In the leaf-row family
`s_{ε,Λ}` the value of `G` at a secular eigenvalue is `θ + c + Λ • w` with `w = 1/(t - β) ≠ 0`,
and in the bare-row family it is `c + θ (1 - 2m/t)`.  In both cases a non-even pair
`(θ, -θ)` can make a member bad only if an injective affine function of the integer parameter
hits the two-element set `{θ, -θ}`.  This file proves that counting step:

* `SwitchingRow.card_bad_le_two`: for a field `K` of characteristic zero, `w ≠ 0`, the set of
  integers `Λ` with `u + Λ * w ∈ {θ, -θ}` has at most two elements;
* `SwitchingRow.card_bad_le_one_of_ne`: if moreover `2θ ∉ w ℤ` (i.e. no integer `j` with
  `j * w = 2 * θ`), it has at most one element.

The rest of the Row Lemmas (spectrum, reduced form, realizability) is not formalized here.
-/

set_option autoImplicit false

namespace SwitchingRow

variable {K : Type*} [Field K] [CharZero K]

lemma affine_injective (u w : K) (hw : w ≠ 0) :
    Function.Injective (fun Λ : ℤ => u + (Λ : K) * w) := by
  intro a b h
  have h' : ((a : K) - b) * w = 0 := by
    simp only at h; linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact_mod_cast sub_eq_zero.1 h1
  · exact absurd h1 hw

omit [CharZero K] in
lemma bad_set_eq (u w θ : K) :
    {Λ : ℤ | u + (Λ : K) * w = θ ∨ u + (Λ : K) * w = -θ}
      = (fun Λ : ℤ => u + (Λ : K) * w) ⁻¹' ({θ, -θ} : Set K) := by
  ext Λ; simp

/-- At most two integer parameters are bad for a given pair `(θ, -θ)`. -/
theorem card_bad_le_two (u w θ : K) (hw : w ≠ 0) :
    Set.ncard {Λ : ℤ | u + (Λ : K) * w = θ ∨ u + (Λ : K) * w = -θ} ≤ 2 := by
  have hinj := affine_injective u w hw
  rw [bad_set_eq]
  calc Set.ncard ((fun Λ : ℤ => u + (Λ : K) * w) ⁻¹' ({θ, -θ} : Set K))
      ≤ Set.ncard ({θ, -θ} : Set K) :=
        Set.ncard_le_ncard_of_injOn (fun Λ : ℤ => u + (Λ : K) * w) (fun a ha => ha)
          hinj.injOn
    _ ≤ Set.ncard ({-θ} : Set K) + 1 := Set.ncard_insert_le θ {-θ}
    _ = 2 := by rw [Set.ncard_singleton]

/-- If `2θ` is not an integer multiple of `w`, at most one integer parameter is bad. -/
theorem card_bad_le_one_of_ne (u w θ : K) (hw : w ≠ 0)
    (hθ : ∀ j : ℤ, (j : K) * w ≠ 2 * θ) :
    Set.ncard {Λ : ℤ | u + (Λ : K) * w = θ ∨ u + (Λ : K) * w = -θ} ≤ 1 := by
  have hinj := affine_injective u w hw
  have hfin : ((fun Λ : ℤ => u + (Λ : K) * w) ⁻¹' ({θ, -θ} : Set K)).Finite :=
    (Set.toFinite ({θ, -θ} : Set K)).preimage hinj.injOn
  rw [bad_set_eq, Set.ncard_le_one hfin]
  intro a ha b hb
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hinj (by simp only; rw [ha, hb])
  · exfalso; apply hθ (a - b); push_cast; linear_combination ha - hb
  · exfalso; apply hθ (b - a); push_cast; linear_combination hb - ha
  · exact hinj (by simp only; rw [ha, hb])

end SwitchingRow

#print axioms SwitchingRow.card_bad_le_two
#print axioms SwitchingRow.card_bad_le_one_of_ne
