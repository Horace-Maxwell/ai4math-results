import Research.Backfill.Paper6.ChallengeV3

/-! Source-only bounded certificate primitives. No numerical result is imported
from an external enumeration. The interval clause is an upper inclusion only. -/

set_option autoImplicit false

namespace Paper6FiveExclusion

open BackfillPaper6.V3

def IntervalUpper (w : ℕ) : Prop :=
  w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)

def GoodWeight (w : ℕ) : Prop :=
  w ∉ U ∧ (w % 4 = 2 → 250 ≤ w → w ≤ 400 → IntervalUpper w)

instance goodWeightDecidable (w : ℕ) : Decidable (GoodWeight w) :=
  inferInstanceAs (Decidable
    (w ∉ U ∧ (w % 4 = 2 → 250 ≤ w → w ≤ 400 →
      w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398))))

def okayWeight (z : ℤ) : Bool := decide (GoodWeight z.toNat)

def allLe : ℕ → (ℕ → Bool) → Bool
  | 0, f => f 0
  | n + 1, f => f (n + 1) && allLe n f

theorem allLe_sound (n : ℕ) (f : ℕ → Bool) :
    allLe n f = true → ∀ i : ℕ, i ≤ n → f i = true := by
  induction n with
  | zero =>
      intro h i hi
      have hi0 : i = 0 := by omega
      subst i
      exact h
  | succ n ih =>
      intro h i hi
      have hh : f (n + 1) = true ∧ allLe n f = true := by
        simpa only [allLe, Bool.and_eq_true] using h
      by_cases heq : i = n + 1
      · simpa only [heq] using hh.1
      · exact ih hh.2 i (by omega)

theorem allLe_intro (n : ℕ) (f : ℕ → Bool) :
    (∀ i : ℕ, i ≤ n → f i = true) → allLe n f = true := by
  induction n with
  | zero =>
      intro h
      exact h 0 (by omega)
  | succ n ih =>
      intro h
      simp only [allLe, Bool.and_eq_true]
      exact ⟨h (n + 1) (by omega), ih (fun i hi => h i (by omega))⟩

theorem okayWeight_sound (w : ℕ) (h : okayWeight (w : ℤ) = true) : GoodWeight w := by
  have hh : GoodWeight (w : ℤ).toNat := of_decide_eq_true h
  simpa only [Int.toNat_natCast] using hh

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.IntervalUpper
#print axioms Paper6FiveExclusion.GoodWeight
#print axioms Paper6FiveExclusion.goodWeightDecidable
#print axioms Paper6FiveExclusion.okayWeight
#print axioms Paper6FiveExclusion.allLe
#print axioms Paper6FiveExclusion.allLe_sound
#print axioms Paper6FiveExclusion.allLe_intro
#print axioms Paper6FiveExclusion.okayWeight_sound
