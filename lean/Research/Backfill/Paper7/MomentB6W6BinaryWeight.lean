import Research.Backfill.Paper7.MomentB6W6OriginalTransport

/-! NEW uncompiled full-domain rewrite after actual943 recursion-depth failure.
Executable weights use six fixed finite differences and proved zero branches.
The powerset definitions below are proof intermediates only. No value is given,
no old numerical expression is rerun, and no performance claim is made. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6W6BinaryBinomial (Q : ℕ) : ℤ := ((Q+5).choose 5 : ℕ)
#print axioms Paper7MomentCounts.b6W6BinaryBinomial

def b6W6BinaryDelta (d : ℕ) (F : ℕ → ℤ) (Q : ℕ) : ℤ :=
  bif decide (d ≤ Q) then F Q - F (Q-d) else F Q
#print axioms Paper7MomentCounts.b6W6BinaryDelta

def b6W6BinaryWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  b6W6BinaryDelta (z 0+1)
    (b6W6BinaryDelta (z 1+1)
      (b6W6BinaryDelta (z 2+1)
        (b6W6BinaryDelta (z 3+1)
          (b6W6BinaryDelta (z 4+1)
            (b6W6BinaryDelta (z 5+1) b6W6BinaryBinomial))))) Q
#print axioms Paper7MomentCounts.b6W6BinaryWeight

def b6W6CapacitySum (z : Fin 6 → ℕ) : ℕ :=
  z 0 + z 1 + z 2 + z 3 + z 4 + z 5
#print axioms Paper7MomentCounts.b6W6CapacitySum

def b6W6FastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q=0) then 1 else
    bif decide (b6W6CapacitySum z < Q) then 0 else b6W6BinaryWeight z Q
#print axioms Paper7MomentCounts.b6W6FastWeight

def b6W6SubsetTerm (z : Fin 6 → ℕ) (Q : ℕ) (I : Finset (Fin 6)) : ℤ :=
  (-1 : ℤ)^I.card *
    (if (∑ i ∈ I, (z i+1)) ≤ Q then
      b6W6BinaryBinomial (Q-(∑ i ∈ I, (z i+1))) else 0)
#print axioms Paper7MomentCounts.b6W6SubsetTerm

def b6W6SubsetWeight (z : Fin 6 → ℕ) (s : Finset (Fin 6)) (Q : ℕ) : ℤ :=
  ∑ I ∈ s.powerset, b6W6SubsetTerm z Q I
#print axioms Paper7MomentCounts.b6W6SubsetWeight

theorem b6W6SubsetTerm_insert (z : Fin 6 → ℕ) (Q : ℕ)
    (I : Finset (Fin 6)) (i : Fin 6) (hi : i ∉ I) :
    b6W6SubsetTerm z Q (insert i I) =
      if z i+1 ≤ Q then -b6W6SubsetTerm z (Q-(z i+1)) I else 0 := by
  unfold b6W6SubsetTerm
  rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi, pow_succ]
  let d : ℕ := ∑ j ∈ I, (z j+1)
  by_cases ha : z i+1 ≤ Q
  · rw [ite_eq_left ha]
    change ((-1 : ℤ)^I.card * (-1)) *
      (if z i+1+d ≤ Q then b6W6BinaryBinomial (Q-(z i+1+d)) else 0) =
        -((-1 : ℤ)^I.card *
          (if d ≤ Q-(z i+1) then b6W6BinaryBinomial (Q-(z i+1)-d) else 0))
    by_cases hb : d ≤ Q-(z i+1)
    · have hb' : z i+1+d ≤ Q := by omega
      have hs : Q-(z i+1+d) = Q-(z i+1)-d := by omega
      rw [ite_eq_left hb', ite_eq_left hb, hs]
      ring
    · have hb' : ¬ z i+1+d ≤ Q := by omega
      rw [ite_eq_right hb', ite_eq_right hb]
      simp only [mul_zero, neg_zero]
  · have hb : ¬ z i+1+(∑ j ∈ I, (z j+1)) ≤ Q := by omega
    rw [ite_eq_right ha, ite_eq_right hb, mul_zero]
#print axioms Paper7MomentCounts.b6W6SubsetTerm_insert

theorem b6W6SubsetWeight_empty (z : Fin 6 → ℕ) :
    b6W6SubsetWeight z ∅ = b6W6BinaryBinomial := by
  funext Q
  simp [b6W6SubsetWeight, b6W6SubsetTerm]
#print axioms Paper7MomentCounts.b6W6SubsetWeight_empty

theorem b6W6SubsetWeight_insert (z : Fin 6 → ℕ)
    (s : Finset (Fin 6)) (i : Fin 6) (hi : i ∉ s) :
    b6W6SubsetWeight z (insert i s) =
      b6W6BinaryDelta (z i+1) (b6W6SubsetWeight z s) := by
  classical
  funext Q
  unfold b6W6SubsetWeight
  rw [Finset.sum_powerset_insert hi]
  have hsum : (∑ I ∈ s.powerset, b6W6SubsetTerm z Q (insert i I)) =
      if z i+1 ≤ Q then -(∑ I ∈ s.powerset, b6W6SubsetTerm z (Q-(z i+1)) I) else 0 := by
    by_cases h : z i+1 ≤ Q
    · rw [ite_eq_left h, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro I hI
      have hn : i ∉ I := fun hmem => hi ((Finset.mem_powerset.mp hI) hmem)
      rw [b6W6SubsetTerm_insert z Q I i hn, ite_eq_left h]
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro I hI
      have hn : i ∉ I := fun hmem => hi ((Finset.mem_powerset.mp hI) hmem)
      rw [b6W6SubsetTerm_insert z Q I i hn, ite_eq_right h]
  rw [hsum]
  unfold b6W6BinaryDelta
  by_cases h : z i+1 ≤ Q
  · rw [Bool.cond_eq_ite, ite_eq_left (decide_eq_true h), ite_eq_left h]
    exact (sub_eq_add_neg _ _).symm
  · have hb : ¬ decide (z i+1 ≤ Q) = true := fun h' => h (of_decide_eq_true h')
    rw [Bool.cond_eq_ite, ite_eq_right hb, ite_eq_right h, add_zero]
#print axioms Paper7MomentCounts.b6W6SubsetWeight_insert

theorem b6W6SubsetWeight_univ_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6SubsetWeight z Finset.univ Q = b6W6EvalWeight z Q := by
  unfold b6W6SubsetWeight b6W6EvalWeight
  apply Finset.sum_congr rfl
  intro I _hI
  unfold b6W6SubsetTerm b6W6BinaryBinomial
  let d : ℕ := ∑ i ∈ I, (z i+1)
  change (-1 : ℤ)^I.card * (if d ≤ Q then (((Q-d+5).choose 5 : ℕ) : ℤ) else 0) =
    (-1 : ℤ)^I.card * (bif decide (d ≤ Q) then (((Q-d+5).choose 5 : ℕ) : ℤ) else 0)
  by_cases h : d ≤ Q
  · rw [Bool.cond_eq_ite, ite_eq_left (decide_eq_true h), ite_eq_left h]
  · have hb : ¬ decide (d ≤ Q) = true := fun h' => h (of_decide_eq_true h')
    rw [Bool.cond_eq_ite, ite_eq_right hb, ite_eq_right h]
#print axioms Paper7MomentCounts.b6W6SubsetWeight_univ_eq

theorem b6W6BinaryWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6BinaryWeight z Q = b6W6EvalWeight z Q := by
  classical
  have hu : (Finset.univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by
    ext i
    fin_cases i <;> simp
  have hlast : b6W6SubsetWeight z {5} =
      b6W6BinaryDelta (z 5+1) (b6W6SubsetWeight z ∅) := by
    simpa only [Finset.insert_empty] using
      (b6W6SubsetWeight_insert z ∅ 5 (by simp))
  calc
    b6W6BinaryWeight z Q = b6W6SubsetWeight z Finset.univ Q := by
      unfold b6W6BinaryWeight
      rw [hu,
        b6W6SubsetWeight_insert z {1,2,3,4,5} 0 (by decide),
        b6W6SubsetWeight_insert z {2,3,4,5} 1 (by decide),
        b6W6SubsetWeight_insert z {3,4,5} 2 (by decide),
        b6W6SubsetWeight_insert z {4,5} 3 (by decide),
        b6W6SubsetWeight_insert z {5} 4 (by decide),
        hlast, b6W6SubsetWeight_empty]
    _ = b6W6EvalWeight z Q := b6W6SubsetWeight_univ_eq z Q
#print axioms Paper7MomentCounts.b6W6BinaryWeight_eq

theorem b6W6CapacitySum_eq (z : Fin 6 → ℕ) :
    b6W6CapacitySum z = ∑ i, z i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change z 0 + z 1 + z 2 + z 3 + z 4 + z 5 =
    z 0 + (z 1 + (z 2 + (z 3 + (z 4 + z 5))))
  omega
#print axioms Paper7MomentCounts.b6W6CapacitySum_eq

theorem b6W6FastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6FastWeight z Q = b6W6EvalWeight z Q := by
  unfold b6W6FastWeight
  by_cases h0 : Q=0
  · rw [Bool.cond_eq_ite, ite_eq_left (decide_eq_true h0)]
    subst Q
    rw [b6W6EvalWeight_eq, labelledSixQWeight_eq_actual_card,
      bounded_q_actual_card_zero_Q, Nat.cast_one]
  · have hb0 : ¬ decide (Q=0) = true := fun h => h0 (of_decide_eq_true h)
    rw [Bool.cond_eq_ite, ite_eq_right hb0]
    by_cases hcap : b6W6CapacitySum z < Q
    · rw [Bool.cond_eq_ite, ite_eq_left (decide_eq_true hcap)]
      have hc : (∑ i, z i) < Q := by rwa [b6W6CapacitySum_eq] at hcap
      rw [b6W6EvalWeight_eq, labelledSixQWeight_eq_actual_card,
        bounded_q_actual_card_above_capacity 6 Q z hc, Nat.cast_zero]
    · have hb : ¬ decide (b6W6CapacitySum z < Q) = true :=
        fun h => hcap (of_decide_eq_true h)
      rw [Bool.cond_eq_ite, ite_eq_right hb]
      exact b6W6BinaryWeight_eq z Q
#print axioms Paper7MomentCounts.b6W6FastWeight_eq

end Paper7MomentCounts
