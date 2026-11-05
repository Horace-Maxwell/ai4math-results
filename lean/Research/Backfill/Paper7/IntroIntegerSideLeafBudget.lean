import Mathlib

/-! A finite positive integer square budget gives a coordinate bound.
The predicate will be the side opposite the actual normalized anchor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroThreeLeafExternal

theorem integer_square_budget_twenty_bound
    {V : Type} [Fintype V] (p : V → Prop) (z : V → ℤ)
    (hz : ∀ v, 0 < z v)
    (hsum : (∑ v, if p v then z v ^ 2 else 0) = 20)
    (v : V) (hv : p v) : 1 ≤ z v ∧ z v ≤ 4 := by
  have hsingle : (if p v then z v ^ 2 else 0) ≤
      ∑ t, if p t then z t ^ 2 else 0 := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun t : V => if p t then z t ^ 2 else 0)
    · intro t _ht
      by_cases hp : p t
      · simpa only [hp, ↓reduceIte] using sq_nonneg (z t)
      · simp only [hp, ↓reduceIte, le_refl]
    · exact Finset.mem_univ v
  have hsquare : z v ^ 2 ≤ 20 := by
    simpa only [hv, ↓reduceIte, hsum] using hsingle
  constructor
  · have hp := hz v
    omega
  · by_contra hn
    have hfive : 5 ≤ z v := by omega
    have hprod : 0 ≤ (z v - 5) * (z v + 5) :=
      mul_nonneg (by omega) (by omega)
    nlinarith only [hsquare, hprod]
#print axioms Paper7IntroThreeLeafExternal.integer_square_budget_twenty_bound

end Paper7IntroThreeLeafExternal
