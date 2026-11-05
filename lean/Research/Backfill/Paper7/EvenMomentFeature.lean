import Research.Backfill.Paper7.LegacyCandidates

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
This module has not been compiled or accepted. It transports the literal even-b
MomentPass predicate to a finite positive-count witness, without counting witnesses.
-/
set_option autoImplicit false

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

/-- The exact positive feature condition for the even-b B1/D2 moment guard. -/
def evenFeatureCondition (b N W Q : ℕ) (T : ℤ) (a : Counts) : Prop :=
  (∃ ρ : Fin 8, 3 ≤ value ρ ∧ a ρ = 1 ∧
    ∀ i, value ρ < value i → a i = 0) ∧
  s2 b (a, 0) ≤ (N : ℤ) ∧
  m4 b (a, 0) = T + (if b = 4 then 4 else 0) ∧
  s2 b (a, 0) ≤ (b + W : ℤ) ∧
  (b + W : ℤ) - max (Q : ℤ) 2 ≤ s2 b (a, 0)

#print axioms Paper7MomentCounts.evenFeatureCondition

theorem momentPass_iff_evenFeature (b N : ℕ) (x : PQ b) (hb : Even b) :
    MomentPass false true false b N x ↔
      ∃ a : Counts, evenFeatureCondition b N (weight x) (qSum x) (theta x) a := by
  constructor
  · rintro ⟨⟨a, c⟩, hs, hm4, hs2, hload, _hcount⟩
    rcases hs.1 with ⟨⟨ρ, hρ, hone, habove, hnegative⟩, hN, _hodd⟩
    have hc : c = 0 := by
      simpa only [hb, ite_true] using hnegative
    subst c
    refine ⟨a, ⟨ρ, hρ, hone, habove⟩, ?_, ?_, ?_, ?_⟩
    · simpa only [hb, ite_true] using hN
    · simpa only [hb, ite_true] using hm4
    · simpa only [hb, ite_true] using hs2
    · simpa only [hb, ite_true, Nat.cast_max, Nat.cast_ofNat] using hload rfl
  · rintro ⟨a, ha⟩
    rcases ha with ⟨⟨ρ, hρ, hone, habove⟩, hN, hm4, hs2, hload⟩
    refine ⟨(a, 0), ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨⟨ρ, hρ, hone, habove, ?_⟩, ?_, ?_⟩
        · simp only [hb, ite_true]
        · simpa only [hb, ite_true] using hN
        · intro hodd
          exact (Nat.not_odd_iff_even.mpr hb hodd).elim
      · intro hfalse
        cases hfalse
    · simpa only [hb, ite_true] using hm4
    · simpa only [hb, ite_true] using hs2
    · intro _htrue
      simpa only [hb, ite_true, Nat.cast_max, Nat.cast_ofNat] using hload
    · intro hfalse
      cases hfalse

#print axioms Paper7MomentCounts.momentPass_iff_evenFeature

end Paper7MomentCounts
