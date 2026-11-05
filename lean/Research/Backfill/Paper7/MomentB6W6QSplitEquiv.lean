import Research.Backfill.Paper7.MomentB6W6ActualCard

/-! NEW uncompiled candidate. Unit 2: the actual ordered bounded-q
concatenation/splitting equivalence, with its exact finite t interval.
All capacities and Q are arbitrary naturals, including zero. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def b6W6JoinedCapacity (u v : ℕ × ℕ × ℕ) : Fin 6 → ℕ :=
  ![u.1, u.2.1, u.2.2, v.1, v.2.1, v.2.2]
#print axioms Paper7MomentCounts.b6W6JoinedCapacity

def b6W6QSplitRange (u v : ℕ × ℕ × ℕ) (Q : ℕ) : Finset ℕ :=
  Finset.Icc (Q - (v.1 + v.2.1 + v.2.2)) (min Q (u.1 + u.2.1 + u.2.2))
#print axioms Paper7MomentCounts.b6W6QSplitRange

abbrev B6W6BoundedFibre (u v : ℕ × ℕ × ℕ) (Q : ℕ) :=
  {q : (i : Fin 6) → Fin (b6W6JoinedCapacity u v i + 1) // ∑ i, (q i).val = Q}
#print axioms Paper7MomentCounts.B6W6BoundedFibre

abbrev B6W6QSplitPair (u v : ℕ × ℕ × ℕ) (Q : ℕ) :=
  Σ t : ↥(b6W6QSplitRange u v Q),
    labelledTripleQFiber u t.val × labelledTripleQFiber v (Q - t.val)
#print axioms Paper7MomentCounts.B6W6QSplitPair

def b6W6QJoin (u v : ℕ × ℕ × ℕ) (Q : ℕ) :
    B6W6QSplitPair u v Q → B6W6BoundedFibre u v Q := fun y =>
  ⟨fun i =>
    ⟨![y.2.1.val.1.val, y.2.1.val.2.1.val, y.2.1.val.2.2.val,
       y.2.2.val.1.val, y.2.2.val.2.1.val, y.2.2.val.2.2.val] i, by
      fin_cases i
      · exact y.2.1.val.1.isLt
      · exact y.2.1.val.2.1.isLt
      · exact y.2.1.val.2.2.isLt
      · exact y.2.2.val.1.isLt
      · exact y.2.2.val.2.1.isLt
      · exact y.2.2.val.2.2.isLt⟩, by
    have ht : y.1.val ≤ Q :=
      (Finset.mem_Icc.mp y.1.property).2.trans (min_le_left _ _)
    have hl := y.2.1.property
    have hr := y.2.2.property
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change y.2.1.val.1.val + (y.2.1.val.2.1.val +
      (y.2.1.val.2.2.val + (y.2.2.val.1.val +
      (y.2.2.val.2.1.val + y.2.2.val.2.2.val)))) = Q
    omega⟩
#print axioms Paper7MomentCounts.b6W6QJoin

theorem b6W6QJoin_injective (u v : ℕ × ℕ × ℕ) (Q : ℕ) :
    Function.Injective (b6W6QJoin u v Q) := by
  rintro ⟨t, q, r⟩ ⟨s, q', r'⟩ h
  have h0 : q.val.1 = q'.val.1 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 0) h
  have h1 : q.val.2.1 = q'.val.2.1 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 1) h
  have h2 : q.val.2.2 = q'.val.2.2 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 2) h
  have h3 : r.val.1 = r'.val.1 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 3) h
  have h4 : r.val.2.1 = r'.val.2.1 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 4) h
  have h5 : r.val.2.2 = r'.val.2.2 :=
    congrArg (fun x : B6W6BoundedFibre u v Q => x.val 5) h
  have hq : q.val = q'.val := Prod.ext h0 (Prod.ext h1 h2)
  have hr : r.val = r'.val := Prod.ext h3 (Prod.ext h4 h5)
  have hts : t = s := by
    apply Subtype.ext
    calc
      t.val = q.val.1.val + q.val.2.1.val + q.val.2.2.val := q.property.symm
      _ = q'.val.1.val + q'.val.2.1.val + q'.val.2.2.val := by rw [hq]
      _ = s.val := q'.property
  cases hts
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact Prod.ext (Subtype.ext hq) (Subtype.ext hr)
#print axioms Paper7MomentCounts.b6W6QJoin_injective

theorem b6W6QJoin_surjective (u v : ℕ × ℕ × ℕ) (Q : ℕ) :
    Function.Surjective (b6W6QJoin u v Q) := by
  intro x
  let a : ℕ := (x.val 0).val + (x.val 1).val + (x.val 2).val
  let b : ℕ := (x.val 3).val + (x.val 4).val + (x.val 5).val
  have hab : a + b = Q := by
    have hs := x.property
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change (x.val 0).val + ((x.val 1).val + ((x.val 2).val +
      ((x.val 3).val + ((x.val 4).val + (x.val 5).val)))) = Q at hs
    dsimp only [a, b]
    omega
  have ha : a ≤ u.1 + u.2.1 + u.2.2 := by
    have h0 : (x.val 0).val ≤ u.1 := Nat.le_of_lt_succ (x.val 0).isLt
    have h1 : (x.val 1).val ≤ u.2.1 := Nat.le_of_lt_succ (x.val 1).isLt
    have h2 : (x.val 2).val ≤ u.2.2 := Nat.le_of_lt_succ (x.val 2).isLt
    dsimp only [a]
    omega
  have hb : b ≤ v.1 + v.2.1 + v.2.2 := by
    have h3 : (x.val 3).val ≤ v.1 := Nat.le_of_lt_succ (x.val 3).isLt
    have h4 : (x.val 4).val ≤ v.2.1 := Nat.le_of_lt_succ (x.val 4).isLt
    have h5 : (x.val 5).val ≤ v.2.2 := Nat.le_of_lt_succ (x.val 5).isLt
    dsimp only [b]
    omega
  let t : ↥(b6W6QSplitRange u v Q) := ⟨a, by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, le_min (by omega) ha⟩⟩
  let q : labelledTripleQFiber u t.val := ⟨(x.val 0, x.val 1, x.val 2), rfl⟩
  let r : labelledTripleQFiber v (Q - t.val) :=
    ⟨(x.val 3, x.val 4, x.val 5), by
      change b = Q - a
      omega⟩
  refine ⟨⟨t, q, r⟩, ?_⟩
  apply Subtype.ext
  funext i
  apply Fin.ext
  fin_cases i <;> rfl
#print axioms Paper7MomentCounts.b6W6QJoin_surjective

def b6W6QSplitEquiv (u v : ℕ × ℕ × ℕ) (Q : ℕ) :
    B6W6BoundedFibre u v Q ≃ B6W6QSplitPair u v Q :=
  (Equiv.ofBijective (b6W6QJoin u v Q)
    ⟨b6W6QJoin_injective u v Q, b6W6QJoin_surjective u v Q⟩).symm
#print axioms Paper7MomentCounts.b6W6QSplitEquiv

end Paper7MomentCounts
