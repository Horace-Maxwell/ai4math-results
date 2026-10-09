import Research.Backfill.Paper6.InclusionExclusionVenn

/-! Source candidate only. A bounded Boolean loop and its complete soundness
interface. The generated numerical files quantify all feasible Venn counts;
the actual-set bridge is in LiteralVenn. No weight classification is assumed. -/

set_option autoImplicit false

namespace Paper6LiteralLouWang

def smallWeights : Finset ℕ :=
  {0, 64, 96, 112, 120, 124, 126, 128, 136, 144, 148, 152, 154, 156, 158, 160}

def okayWeight (w : ℤ) : Bool := decide (161 < w ∨ w.toNat ∈ smallWeights)

def allLe : ℕ → (ℕ → Bool) → Bool
  | 0, f => f 0
  | n + 1, f => f (n + 1) && allLe n f

theorem allLe_sound (n : ℕ) (f : ℕ → Bool) :
    allLe n f = true → ∀ i : ℕ, i ≤ n → f i = true := by
  induction n with
  | zero =>
      intro h i hi
      have heq : i = 0 := by omega
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

theorem okayWeight_sound (w : ℕ) (h : okayWeight (w : ℤ) = true)
    (hle : w ≤ 161) : w ∈ smallWeights := by
  have hv : (161 : ℤ) < (w : ℤ) ∨ (w : ℤ).toNat ∈ smallWeights :=
    of_decide_eq_true h
  rcases hv with hbig | hmem
  · have : (w : ℤ) ≤ 161 := by exact_mod_cast hle
    omega
  · simpa only [Int.toNat_natCast] using hmem

theorem no_322_triple :
    ∀ a ∈ smallWeights, ∀ b ∈ smallWeights, ∀ c ∈ smallWeights,
      a + b + c ≠ 322 := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.smallWeights
#print axioms Paper6LiteralLouWang.okayWeight
#print axioms Paper6LiteralLouWang.allLe
#print axioms Paper6LiteralLouWang.allLe_sound
#print axioms Paper6LiteralLouWang.allLe_intro
#print axioms Paper6LiteralLouWang.okayWeight_sound
#print axioms Paper6LiteralLouWang.no_322_triple
