import Research.Backfill.Paper7.MomentB6Type1122Coefficient

/-! UNCOMPILED source-only draft. Original ordered reflection row
[a,b,c,d,c,b], in both p and q, with a=position 0 and d=position 3.
No feature witness is counted; the original full guard is retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6Type1122Row (x : PQ 4) : PQ 6 :=
  (![x.1 0,x.1 1,x.1 2,x.1 3,x.1 2,x.1 1],
   ![x.2 0,x.2 1,x.2 2,x.2 3,x.2 2,x.2 1])
#print axioms Paper7MomentCounts.b6Type1122Row

def b6Type1122Total (v : Fin 4 → ℕ) : ℕ := v 0 + 2*v 1 + 2*v 2 + v 3
#print axioms Paper7MomentCounts.b6Type1122Total

def b6Type1122Squares (z : Fin 4 → ℕ) : ℤ :=
  (z 0 : ℤ)^2 + 2*(z 1 : ℤ)^2 + 2*(z 2 : ℤ)^2 + (z 3 : ℤ)^2
#print axioms Paper7MomentCounts.b6Type1122Squares

def b6Type1122Guard (z : Fin 4 → ℕ) (Q : ℕ) : Prop :=
  0 < b6Type1122Total z + Q ∧ b6Type1122Total z + Q ≤ 36 ∧
    b6FeatureGuard (b6Type1122Total z + Q) Q
      (12 + 3*(b6Type1122Total z : ℤ) + 2*(Q : ℤ) + b6Type1122Squares z)
#print axioms Paper7MomentCounts.b6Type1122Guard

theorem b6_type1122_row_injective : Function.Injective b6Type1122Row := by
  intro x y h
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrArg (fun v : PQ 6 => v.1 0) h
    · exact congrArg (fun v : PQ 6 => v.1 1) h
    · exact congrArg (fun v : PQ 6 => v.1 2) h
    · exact congrArg (fun v : PQ 6 => v.1 3) h
  · funext i
    fin_cases i
    · exact congrArg (fun v : PQ 6 => v.2 0) h
    · exact congrArg (fun v : PQ 6 => v.2 1) h
    · exact congrArg (fun v : PQ 6 => v.2 2) h
    · exact congrArg (fun v : PQ 6 => v.2 3) h
#print axioms Paper7MomentCounts.b6_type1122_row_injective

theorem b6_type1122_row_features (x : PQ 4) :
    weight (b6Type1122Row x) =
      b6Type1122Total (fun i => x.1 i+x.2 i) + b6Type1122Total x.2 ∧
    qSum (b6Type1122Row x) = b6Type1122Total x.2 ∧
    theta (b6Type1122Row x) =
      12 + 3*(b6Type1122Total (fun i => x.1 i+x.2 i) : ℤ) +
        2*(b6Type1122Total x.2 : ℤ) +
        b6Type1122Squares (fun i => x.1 i+x.2 i) := by
  constructor
  · simp [weight,pSum,qSum,b6Type1122Row,Fin.sum_univ_succ,b6Type1122Total]
    omega
  · constructor
    · simp [qSum,b6Type1122Row,Fin.sum_univ_succ,b6Type1122Total]
      omega
    · simp [theta,b6Type1122Row,Fin.sum_univ_succ,thetaV,
        b6Type1122Total,b6Type1122Squares]
      ring
#print axioms Paper7MomentCounts.b6_type1122_row_features

theorem b6_type1122_candB1_iff (x : PQ 4) :
    b6Type1122Row x ∈ CandB1 6 42 ↔
      b6Type1122Guard (fun i => x.1 i+x.2 i) (b6Type1122Total x.2) := by
  rw [b6_candB1_iff_guard]
  unfold b6CandidateGuard b6Type1122Guard
  rw [(b6_type1122_row_features x).1,(b6_type1122_row_features x).2.1,
    (b6_type1122_row_features x).2.2]
#print axioms Paper7MomentCounts.b6_type1122_candB1_iff

theorem b6_type1122_candD2_iff (x : PQ 4) :
    b6Type1122Row x ∈ CandD2 6 42 ↔
      b6Type1122Guard (fun i => x.1 i+x.2 i) (b6Type1122Total x.2) := by
  rw [candD2_eq_candB1_of_even 6 42 (by decide), b6_type1122_candB1_iff]
#print axioms Paper7MomentCounts.b6_type1122_candD2_iff

abbrev B6Type1122OriginalFibre (z : Fin 4 → ℕ) (Q : ℕ) :=
  {x : PQ 4 // (∀ i, x.1 i+x.2 i=z i) ∧ b6Type1122Total x.2=Q}
#print axioms Paper7MomentCounts.B6Type1122OriginalFibre

/-- Every original p coordinate is recovered as z-q. None of the four q
coordinates is discarded, sorted, or counted as a spectral witness. -/
def b6Type1122OriginalQEquiv (z : Fin 4 → ℕ) (Q : ℕ) :
    B6Type1122OriginalFibre z Q ≃
      B6Type1122QFibre (z 0) (z 1) (z 2) (z 3) Q where
  toFun x := by
    have h0 := x.property.1 0
    have h1 := x.property.1 1
    have h2 := x.property.1 2
    have h3 := x.property.1 3
    refine ⟨((⟨x.val.2 0, by omega⟩,⟨x.val.2 3, by omega⟩),
      (⟨x.val.2 1, by omega⟩,⟨x.val.2 2, by omega⟩)),?_⟩
    have hQ := x.property.2
    unfold b6Type1122Total at hQ
    change x.val.2 0 + x.val.2 3 + 2*(x.val.2 1 + x.val.2 2) = Q
    omega
  invFun q := by
    let v : Fin 4 → ℕ := ![q.val.1.1.val,q.val.2.1.val,q.val.2.2.val,q.val.1.2.val]
    have h0 := q.val.1.1.isLt
    have h1 := q.val.2.1.isLt
    have h2 := q.val.2.2.isLt
    have h3 := q.val.1.2.isLt
    refine ⟨(fun i => z i-v i,v),?_,?_⟩
    · intro i
      fin_cases i <;> dsimp [v] <;> omega
    · have hQ := q.property
      dsimp [b6Type1122Total,v]
      omega
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi : x.val.1 i + x.val.2 i = z i := x.property.1 i
      have hr : z i - x.val.2 i = x.val.1 i :=
        (congrArg (fun n : ℕ => n - x.val.2 i) hi).symm.trans
          (Nat.add_sub_cancel (x.val.1 i) (x.val.2 i))
      fin_cases i <;> dsimp at hr ⊢ <;> exact hr
    · funext i
      fin_cases i <;> rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> apply Fin.ext <;> rfl
#print axioms Paper7MomentCounts.b6Type1122OriginalQEquiv

theorem b6_type1122_original_fibre_card (z : Fin 4 → ℕ) (Q : ℕ) :
    Nat.card (B6Type1122OriginalFibre z Q) =
      b6Type1122Coefficient (z 0) (z 1) (z 2) (z 3) Q := by
  rw [Nat.card_congr (b6Type1122OriginalQEquiv z Q), b6_type1122_q_fibre_card]
#print axioms Paper7MomentCounts.b6_type1122_original_fibre_card

theorem b6_type1122_original_fibre_acceptance (z : Fin 4 → ℕ) (Q : ℕ)
    (x : B6Type1122OriginalFibre z Q) :
    b6Type1122Row x.val ∈ CandB1 6 42 ↔ b6Type1122Guard z Q := by
  rw [b6_type1122_candB1_iff, funext x.property.1, x.property.2]
#print axioms Paper7MomentCounts.b6_type1122_original_fibre_acceptance

theorem b6_type1122_original_fibre_Q_le (z : Fin 4 → ℕ) (Q : ℕ)
    (x : B6Type1122OriginalFibre z Q) : Q ≤ b6Type1122Total z := by
  have h0 := x.property.1 0
  have h1 := x.property.1 1
  have h2 := x.property.1 2
  have h3 := x.property.1 3
  have hQ := x.property.2
  unfold b6Type1122Total at hQ ⊢
  omega
#print axioms Paper7MomentCounts.b6_type1122_original_fibre_Q_le

theorem b6_type1122_guard_budget_bounds (z : Fin 4 → ℕ) (Q : ℕ)
    (h : b6Type1122Guard z Q) (hQ : Q ≤ b6Type1122Total z) :
    b6Type1122Total z ≤ 36 ∧ Q ≤ 18 ∧
      z 0 ≤ 36 ∧ z 3 ≤ 36 ∧ z 1 ≤ 18 ∧ z 2 ≤ 18 := by
  have hw := h.2.1
  unfold b6Type1122Total at hw hQ ⊢
  omega
#print axioms Paper7MomentCounts.b6_type1122_guard_budget_bounds

theorem b6_type1122_catalog_theta_upper (sm : ℤ × ℤ)
    (h : sm ∈ b6FeatureCatalog) : sm.2 ≤ 1272 := by
  simp only [b6FeatureCatalog,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
#print axioms Paper7MomentCounts.b6_type1122_catalog_theta_upper

/-- The stronger singleton cap 34 is forced by the original full catalog. -/
theorem b6_type1122_guard_singleton_bounds (z : Fin 4 → ℕ) (Q : ℕ)
    (h : b6Type1122Guard z Q) : z 0 ≤ 34 ∧ z 3 ≤ 34 := by
  obtain ⟨sm,hsm,ht,_,_⟩ := h.2.2
  have htop := b6_type1122_catalog_theta_upper sm hsm
  rw [ht] at htop
  unfold b6Type1122Total b6Type1122Squares at htop
  push_cast at htop
  have h0 := sq_nonneg (z 0 : ℤ)
  have h1 := sq_nonneg (z 1 : ℤ)
  have h2 := sq_nonneg (z 2 : ℤ)
  have h3 := sq_nonneg (z 3 : ℤ)
  constructor
  · by_contra hn
    have hz : (35 : ℤ) ≤ (z 0 : ℤ) := by omega
    nlinarith [sq_nonneg ((z 0 : ℤ)-35),Int.natCast_nonneg (z 1),Int.natCast_nonneg (z 2),
      Int.natCast_nonneg (z 3),Int.natCast_nonneg Q]
  · by_contra hn
    have hz : (35 : ℤ) ≤ (z 3 : ℤ) := by omega
    nlinarith [sq_nonneg ((z 3 : ℤ)-35),Int.natCast_nonneg (z 0),Int.natCast_nonneg (z 1),
      Int.natCast_nonneg (z 2),Int.natCast_nonneg Q]
#print axioms Paper7MomentCounts.b6_type1122_guard_singleton_bounds

/-- Q is uniquely determined by z and the selected original catalog moment. -/
theorem b6_type1122_Q_recovery (z : Fin 4 → ℕ) (Q : ℕ)
    (h : b6Type1122Guard z Q) :
    ∃ sm ∈ b6FeatureCatalog,
      2*(Q : ℤ) = sm.2-12-3*(b6Type1122Total z : ℤ)-b6Type1122Squares z ∧
      sm.1 ≤ (6+b6Type1122Total z+Q : ℤ) ∧
      (6+b6Type1122Total z+Q : ℤ)-max (Q : ℤ) 2 ≤ sm.1 := by
  obtain ⟨sm,hsm,ht,hs,hl⟩ := h.2.2
  refine ⟨sm,hsm,?_,?_,?_⟩
  · omega
  · simpa [Nat.cast_add,add_assoc] using hs
  · simpa [Nat.cast_add,add_assoc] using hl
#print axioms Paper7MomentCounts.b6_type1122_Q_recovery

end Paper7MomentCounts
