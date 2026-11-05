import Research.Backfill.Paper7.ChallengeV3
import Research.Backfill.Paper7.BudgetTupleCounts

/-! A complete finite encoding of the original labeled parameter functions. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Budget

open BackfillPaper7.Challenge

abbrev ParameterPair := (Fin 3 → ℕ) × (Fin 3 → ℕ)

#print axioms Paper7Budget.ParameterPair

def allBudget (N : ℕ) : Set ParameterPair := {d | nOf 3 d.1 d.2 ≤ N}

#print axioms Paper7Budget.allBudget

abbrev BudgetLayers (N : ℕ) :=
  Σ Q : Fin ((N - 3) / 2 + 1), ExactTuple 3 Q.val × BoundedTuple 3 (N - 3 - 2 * Q.val)

#print axioms Paper7Budget.BudgetLayers

/-- The layer index is exactly the total Q, not a pruning or an upper approximation. -/
def allBudgetEquivLayers (N : ℕ) (hN : 3 ≤ N) : allBudget N ≃ BudgetLayers N where
  toFun d := by
    let Q := ∑ i, d.val.2 i
    have hd : 3 + (∑ i, d.val.1 i) + 2 * (∑ i, d.val.2 i) ≤ N := d.property
    have hQ : Q < (N - 3) / 2 + 1 := by
      dsimp [Q]
      omega
    exact ⟨⟨Q, hQ⟩, ⟨d.val.2, rfl⟩, ⟨d.val.1, by
      dsimp [Q]
      omega⟩⟩
  invFun d := by
    refine ⟨(d.2.2.val, d.2.1.val), ?_⟩
    change 3 + (∑ i, d.2.2.val i) + 2 * (∑ i, d.2.1.val i) ≤ N
    have hQ := d.1.isLt
    have hp := d.2.2.property
    rw [d.2.1.property]
    omega
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    rcases d with ⟨⟨Q, hQ⟩, ⟨q, hq⟩, ⟨p, hp⟩⟩
    change (∑ i, q i) = Q at hq
    subst Q
    rfl

#print axioms Paper7Budget.allBudgetEquivLayers

theorem allBudget_finite (N : ℕ) (hN : 3 ≤ N) : (allBudget N).Finite := by
  let : Fintype (allBudget N) :=
    Fintype.ofEquiv (BudgetLayers N) (allBudgetEquivLayers N hN).symm
  exact Set.toFinite _

#print axioms Paper7Budget.allBudget_finite

theorem budgetPQ_finite (N : ℕ) (hN : 3 ≤ N) : (budgetPQ 3 N).Finite := by
  apply (allBudget_finite N hN).subset
  intro d hd
  exact hd.2

#print axioms Paper7Budget.budgetPQ_finite

theorem card_budgetLayers (N : ℕ) (hN : 3 ≤ N) :
    Fintype.card (BudgetLayers N) =
      ∑ Q ∈ Finset.range ((N - 3) / 2 + 1), (Q + 2).choose 2 * (N - 2 * Q).choose 3 := by
  calc
    Fintype.card (BudgetLayers N) =
        ∑ Q : Fin ((N - 3) / 2 + 1),
          (Q.val + 2).choose 2 * (N - 3 - 2 * Q.val + 3).choose 3 := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro Q _hQ
      rw [Fintype.card_prod, card_exactTuple 2 Q.val,
        card_boundedTuple 3 (N - 3 - 2 * Q.val)]
    _ = ∑ Q : Fin ((N - 3) / 2 + 1),
        (Q.val + 2).choose 2 * (N - 2 * Q.val).choose 3 := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      have hQ := Q.isLt
      have he : N - 3 - 2 * Q.val + 3 = N - 2 * Q.val := by omega
      rw [he]
    _ = ∑ Q ∈ Finset.range ((N - 3) / 2 + 1),
        (Q + 2).choose 2 * (N - 2 * Q).choose 3 :=
      (Finset.sum_range (n := (N - 3) / 2 + 1)
        (fun Q : ℕ => (Q + 2).choose 2 * (N - 2 * Q).choose 3)).symm

#print axioms Paper7Budget.card_budgetLayers

theorem allBudget_ncard (N : ℕ) (hN : 3 ≤ N) :
    (allBudget N).ncard =
      ∑ Q ∈ Finset.range ((N - 3) / 2 + 1), (Q + 2).choose 2 * (N - 2 * Q).choose 3 := by
  change Nat.card (allBudget N) = _
  calc
    Nat.card (allBudget N) = Nat.card (BudgetLayers N) :=
      Nat.card_congr (allBudgetEquivLayers N hN)
    _ = Fintype.card (BudgetLayers N) := Nat.card_eq_fintype_card
    _ = _ := card_budgetLayers N hN

#print axioms Paper7Budget.allBudget_ncard

theorem pair_eq_zero_iff (p q : Fin 3 → ℕ) :
    (p, q) = (0, 0) ↔ (∑ i, (p i + q i)) = 0 := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := Prod.mk.inj h
    subst p
    subst q
    simp
  · intro h
    have heach : ∀ i, p i = 0 ∧ q i = 0 := by
      intro i
      have hle : p i + q i ≤ ∑ j, (p j + q j) :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (p j + q j)) (Finset.mem_univ i)
      omega
    apply Prod.ext
    · funext i
      exact (heach i).1
    · funext i
      exact (heach i).2

#print axioms Paper7Budget.pair_eq_zero_iff

theorem budgetPQ_eq_sdiff_zero (N : ℕ) :
    budgetPQ 3 N = allBudget N \ {((0, 0) : ParameterPair)} := by
  ext d
  rcases d with ⟨p, q⟩
  change (0 < (∑ i, (p i + q i)) ∧ nOf 3 p q ≤ N) ↔
    (nOf 3 p q ≤ N ∧ (p, q) ≠ (0, 0))
  constructor
  · rintro ⟨hpos, hbudget⟩
    refine ⟨hbudget, ?_⟩
    intro hzero
    have hs := (pair_eq_zero_iff p q).mp hzero
    omega
  · rintro ⟨hbudget, hne⟩
    refine ⟨?_, hbudget⟩
    by_contra hpos
    have hs : (∑ i, (p i + q i)) = 0 := by omega
    exact hne ((pair_eq_zero_iff p q).mpr hs)

#print axioms Paper7Budget.budgetPQ_eq_sdiff_zero

theorem budgetPQ_ncard (N : ℕ) (hN : 3 ≤ N) :
    (budgetPQ 3 N).ncard =
      (∑ Q ∈ Finset.range ((N - 3) / 2 + 1),
        (Q + 2).choose 2 * (N - 2 * Q).choose 3) - 1 := by
  have hzero : ((0, 0) : ParameterPair) ∈ allBudget N := by
    simpa only [allBudget, Set.mem_ofPred_eq, nOf, Pi.zero_apply,
      Finset.sum_const_zero, mul_zero, add_zero] using hN
  rw [budgetPQ_eq_sdiff_zero, Set.ncard_sdiff_singleton_of_mem hzero, allBudget_ncard N hN]

#print axioms Paper7Budget.budgetPQ_ncard

end Paper7Budget
