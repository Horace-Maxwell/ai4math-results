import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! UNCOMPILED source-only draft by /root/moment_b6_continue_2150/type1122_manual_route.
The full q coefficient for ordered cycle lengths 1,1,2,2 is reduced to
at most ten products of interval lengths. No numerical sum is evaluated.
The two singleton labels and two double-cycle labels remain distinguished. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

abbrev B6TwoBoundedQ (a d s : ℕ) :=
  {q : Fin (a+1) × Fin (d+1) // q.1.val + q.2.val = s}
#print axioms Paper7MomentCounts.B6TwoBoundedQ

/-- Valid also for an empty fibre: the inclusive interval is then empty. -/
def b6TwoBoundedQIntervalEquiv (a d s : ℕ) :
    B6TwoBoundedQ a d s ≃ ↥(Finset.Icc (s-d) (min a s)) where
  toFun q := ⟨q.val.1.val, by
    have hq := q.property
    have hqa := q.val.1.isLt
    have hqd := q.val.2.isLt
    apply Finset.mem_Icc.mpr
    refine ⟨?_, le_min ?_ ?_⟩ <;> omega⟩
  invFun k := by
    have hk := Finset.mem_Icc.mp k.property
    have hka := (le_min_iff.mp hk.2).1
    have hks := (le_min_iff.mp hk.2).2
    exact ⟨(⟨k.val, by omega⟩, ⟨s-k.val, by omega⟩), by
      change k.val + (s-k.val) = s
      omega⟩
  left_inv q := by
    have hq := q.property
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · apply Fin.ext
      change s-q.val.1.val = q.val.2.val
      omega
  right_inv k := by
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.b6TwoBoundedQIntervalEquiv

def b6IntervalMultiplicity (a d s : ℕ) : ℕ := min a s + 1 - (s-d)
#print axioms Paper7MomentCounts.b6IntervalMultiplicity

theorem b6_two_bounded_q_card (a d s : ℕ) :
    Nat.card (B6TwoBoundedQ a d s) = b6IntervalMultiplicity a d s := by
  rw [Nat.card_congr (b6TwoBoundedQIntervalEquiv a d s),
    Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_Icc]
  rfl
#print axioms Paper7MomentCounts.b6_two_bounded_q_card

/-- The first pair occupies fixed positions 0 and 3; the second occupies
the ordered cycles (1,5) and (2,4). -/
abbrev B6Type1122QFibre (a b c d Q : ℕ) :=
  {q : (Fin (a+1) × Fin (d+1)) × (Fin (b+1) × Fin (c+1)) //
    q.1.1.val + q.1.2.val + 2*(q.2.1.val + q.2.2.val) = Q}
#print axioms Paper7MomentCounts.B6Type1122QFibre

def b6Type1122QJoin (a b c d Q : ℕ)
    (s : Σ t : Fin (Q/2+1),
      B6TwoBoundedQ a d (Q-2*t.val) × B6TwoBoundedQ b c t.val) :
    B6Type1122QFibre a b c d Q := by
  have ht := s.1.isLt
  have hs := s.2.1.property
  have hd := s.2.2.property
  exact ⟨(s.2.1.val,s.2.2.val), by
    change s.2.1.val.1.val + s.2.1.val.2.val +
      2*(s.2.2.val.1.val + s.2.2.val.2.val) = Q
    omega⟩
#print axioms Paper7MomentCounts.b6Type1122QJoin

theorem b6_type1122_q_join_bijective (a b c d Q : ℕ) :
    Function.Bijective (b6Type1122QJoin a b c d Q) := by
  constructor
  · rintro ⟨t,u,v⟩ ⟨t',u',v'⟩ h
    have hp : (u.val,v.val) = (u'.val,v'.val) :=
      congrArg Subtype.val h
    have hv := congrArg Prod.snd hp
    have ht : t = t' := by
      apply Fin.ext
      have hv' := congrArg (fun q : Fin (b+1) × Fin (c+1) =>
        q.1.val + q.2.val) hv
      exact v.property.symm.trans (hv'.trans v'.property)
    subst t'
    have huv : (u,v) = (u',v') :=
      Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext hv)
    exact congrArg (fun p : B6TwoBoundedQ a d (Q-2*t.val) ×
        B6TwoBoundedQ b c t.val =>
      (⟨t,p⟩ : Σ j : Fin (Q/2+1),
        B6TwoBoundedQ a d (Q-2*j.val) × B6TwoBoundedQ b c j.val)) huv
  · intro q
    have hq := q.property
    let t : Fin (Q/2+1) := ⟨q.val.2.1.val+q.val.2.2.val, by omega⟩
    let u : B6TwoBoundedQ a d (Q-2*t.val) := ⟨q.val.1, by
      change q.val.1.1.val+q.val.1.2.val =
        Q-2*(q.val.2.1.val+q.val.2.2.val)
      omega⟩
    let v : B6TwoBoundedQ b c t.val := ⟨q.val.2,rfl⟩
    exact ⟨⟨t,u,v⟩, Subtype.ext rfl⟩
#print axioms Paper7MomentCounts.b6_type1122_q_join_bijective

def b6Type1122QSplitEquiv (a b c d Q : ℕ) :
    B6Type1122QFibre a b c d Q ≃
      Σ t : Fin (Q/2+1),
        B6TwoBoundedQ a d (Q-2*t.val) × B6TwoBoundedQ b c t.val :=
  (Equiv.ofBijective _ (b6_type1122_q_join_bijective a b c d Q)).symm
#print axioms Paper7MomentCounts.b6Type1122QSplitEquiv

def b6Type1122Coefficient (a b c d Q : ℕ) : ℕ :=
  ∑ t : Fin (Q/2+1),
    b6IntervalMultiplicity a d (Q-2*t.val) * b6IntervalMultiplicity b c t.val
#print axioms Paper7MomentCounts.b6Type1122Coefficient

theorem b6_type1122_q_fibre_card (a b c d Q : ℕ) :
    Nat.card (B6Type1122QFibre a b c d Q) =
      b6Type1122Coefficient a b c d Q := by
  rw [Nat.card_congr (b6Type1122QSplitEquiv a b c d Q), Nat.card_sigma]
  unfold b6Type1122Coefficient
  apply Finset.sum_congr rfl
  intro t _
  rw [Nat.card_prod, b6_two_bounded_q_card, b6_two_bounded_q_card]
#print axioms Paper7MomentCounts.b6_type1122_q_fibre_card

theorem b6_type1122_coefficient_has_at_most_ten_terms (Q : ℕ) (hQ : Q ≤ 18) :
    Fintype.card (Fin (Q/2+1)) ≤ 10 := by
  rw [Fintype.card_fin]
  omega
#print axioms Paper7MomentCounts.b6_type1122_coefficient_has_at_most_ten_terms

end Paper7MomentCounts
