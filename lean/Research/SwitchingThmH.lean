import Mathlib

/-!
# Theorem 9.22.2 (switching conjecture, trees of diameter ≤ 4): arithmetic core and refined count

Session 3 of `work/round6/switching` (PROOF.md §9.22).

* `SwitchingThmH.two_sqrt_add_seven_le`: for `b ≥ 13`, `2 * Nat.sqrt (b - 1) + 7 ≤ b`.
* `SwitchingThmH.row_budget`: if `b ≥ 13`, `sq ≤ Nat.sqrt (b - 1)`, `sq ≤ g`, `NI ≤ sq + 1` and
  `NI + 2 * NII + g ≤ b + 1`, then `2 * NI + NII + 1 ≤ b - 1`.  Here `b = b*` is the largest branch size,
  `g` the number of values in `{0, …, b*}` that are not branch sizes, `sq` the number of squares in
  `[1, b* - 1]` that are not branch sizes, `NI` / `NII` the numbers of integer / irrational non-even pairs.
  With `|L_{b*}| ≥ b* - 1` this is criterion (a') at `β = b*`.
* `SwitchingThmH.sol_subsingleton`: if `1, w` are linearly independent over `ℚ` in a field `K` of
  characteristic zero, then for every `u : K` at most one pair `(ε, Λ) : ℤ × ℤ` satisfies `ε + Λ * w = u`.
  (Refined count: an irrational non-even pair (θ, −θ) makes at most one member of a row bad for θ and at most one for −θ, so at most two in total.)
* `SwitchingThmH.indep_of_irrational`: `1, w` are linearly independent over `ℚ` whenever `w` is not rational.

Not formalized: the spectrum lemma, the reduced form, realizability and the finite search.
-/

set_option autoImplicit false

namespace SwitchingThmH

theorem two_sqrt_add_seven_le (b : ℕ) (hb : 13 ≤ b) : 2 * Nat.sqrt (b - 1) + 7 ≤ b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hc : c + 1 - 1 = c := by omega
  rw [hc]
  have h1 : Nat.sqrt c ^ 2 ≤ c := Nat.sqrt_le' c
  by_cases h : Nat.sqrt c ≤ 3
  · omega
  · push Not at h
    nlinarith [h1, h]

theorem row_budget (b sq g NI NII : ℕ) (hb : 13 ≤ b) (hsq : sq ≤ Nat.sqrt (b - 1)) (hsqg : sq ≤ g)
    (hNI : NI ≤ sq + 1) (hr : NI + 2 * NII + g ≤ b + 1) : 2 * NI + NII + 1 ≤ b - 1 := by
  have := two_sqrt_add_seven_le b hb
  omega

theorem sol_subsingleton {K : Type*} [Field K] [CharZero K] (w u : K)
    (hind : ∀ a c : ℚ, (a : K) + (c : K) * w = 0 → a = 0 ∧ c = 0) :
    Set.Subsingleton {p : ℤ × ℤ | (p.1 : K) + (p.2 : K) * w = u} := by
  intro p hp q hq
  change (p.1 : K) + (p.2 : K) * w = u at hp
  change (q.1 : K) + (q.2 : K) * w = u at hq
  obtain ⟨h1, h2⟩ := hind ((p.1 - q.1 : ℤ) : ℚ) ((p.2 - q.2 : ℤ) : ℚ)
    (by push_cast; linear_combination hp - hq)
  have e1 : p.1 - q.1 = 0 := by exact_mod_cast h1
  have e2 : p.2 - q.2 = 0 := by exact_mod_cast h2
  exact Prod.ext (by omega) (by omega)

theorem indep_of_irrational {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : ∀ q : ℚ, (q : K) ≠ w) :
    ∀ a c : ℚ, (a : K) + (c : K) * w = 0 → a = 0 ∧ c = 0 := by
  intro a c h
  by_cases hc : c = 0
  · subst hc
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hc' : (c : K) ≠ 0 := by exact_mod_cast hc
    apply hw (-a / c)
    push_cast
    field_simp
    linear_combination -h

end SwitchingThmH

#print axioms SwitchingThmH.two_sqrt_add_seven_le
#print axioms SwitchingThmH.row_budget
#print axioms SwitchingThmH.sol_subsingleton
#print axioms SwitchingThmH.indep_of_irrational
