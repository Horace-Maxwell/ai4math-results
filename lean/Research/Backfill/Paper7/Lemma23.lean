import Research.Backfill.Paper7.TraceFour
import Research.Backfill.Paper7.CycleFibres
import Research.Backfill.Paper7.OddGirthWalkBridge

/-! The entire frozen Lemma23, with its original edge-set cycle count and
all finite graph types, including the empty type. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

namespace Paper7Moments

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

def cycleSubtypeEquivBased (g : ℕ) :
    {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = g} ≃
      Paper7Cycles.BasedCycle H g where
  toFun p := ⟨p.val.1, ⟨⟨p.val.2, p.property.2⟩, p.property.1⟩⟩
  invFun p := ⟨⟨p.1, p.2.val.val⟩, p.2.property, p.2.val.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨u, ⟨⟨w, hw⟩, hc⟩⟩; rfl

theorem cycleSubtype_card (g : ℕ) :
    Nat.card {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = g} =
      2 * g * cycleCount H g := by
  rw [Nat.card_congr (cycleSubtypeEquivBased H g), Nat.card_eq_fintype_card]
  exact Paper7Cycles.basedCycle_card H g

theorem trace_four :
    ((H.adjMatrix ℤ) ^ 4).trace = 2 * (H.edgeFinset.card : ℤ) +
      2 * ∑ v, (H.degree v : ℤ) * ((H.degree v : ℤ) - 1) +
        8 * (cycleCount H 4 : ℤ) := by
  rw [Paper7FourWalks.trace_four_with_based_cycles, cycleSubtype_card]
  norm_num

theorem trace_odd_lt_oddGirth {g : ℕ} (hg : IsOddGirth H g)
    (L : ℕ) (hL : Odd L) (hlt : L < g) : ((H.adjMatrix ℤ) ^ L).trace = 0 := by
  rw [trace_eq_closed_walk_count]
  apply Finset.sum_eq_zero
  intro u _
  let : IsEmpty {w : H.Walk u u // w.length = L} :=
    ⟨fun w => Paper7OddWalk.no_odd_closedWalk_of_length_lt_oddGirth hg
      w.val w.property hL hlt⟩
  simp

def oddGirthClosedEquivBased {g : ℕ} (hg : IsOddGirth H g) :
    (Σ u : V, {w : H.Walk u u // w.length = g}) ≃ Paper7Cycles.BasedCycle H g where
  toFun w := ⟨w.1, ⟨w.2,
    Paper7OddWalk.isCycle_of_length_eq_oddGirth hg w.2.val w.2.property⟩⟩
  invFun w := ⟨w.1, w.2.val⟩
  left_inv w := rfl
  right_inv w := by rcases w with ⟨u, ⟨⟨p, hp⟩, hc⟩⟩; rfl

theorem trace_oddGirth {g : ℕ} (hg : IsOddGirth H g) :
    ((H.adjMatrix ℤ) ^ g).trace = 2 * (g : ℤ) * (cycleCount H g : ℤ) := by
  have hc := Fintype.card_congr (oddGirthClosedEquivBased H hg)
  rw [Fintype.card_sigma, Paper7Cycles.basedCycle_card] at hc
  rw [trace_eq_closed_walk_count]
  exact_mod_cast hc

theorem check_Lemma23 : BackfillPaper7.Challenge.Lemma23 := by
  intro V _ _ H _
  refine ⟨trace_square H, trace_four H, ?_⟩
  intro g hg
  exact ⟨trace_odd_lt_oddGirth H hg, trace_oddGirth H hg⟩

end Paper7Moments

#print axioms Paper7Moments.cycleSubtypeEquivBased
#print axioms Paper7Moments.cycleSubtype_card
#print axioms Paper7Moments.trace_four
#print axioms Paper7Moments.trace_odd_lt_oddGirth
#print axioms Paper7Moments.oddGirthClosedEquivBased
#print axioms Paper7Moments.trace_oddGirth
#print axioms Paper7Moments.check_Lemma23

#check (Paper7Moments.check_Lemma23 : BackfillPaper7.Challenge.Lemma23)
