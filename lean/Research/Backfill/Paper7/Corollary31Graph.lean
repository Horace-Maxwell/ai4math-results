import Research.Backfill.Paper7.KappaDivisibility
import Research.Backfill.Paper7.UnicyclicCardinality
import Research.Backfill.Paper7.Proposition3

/-! General finite graphs throughout; no SunV restriction or extra P3 premise. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7Corollary31
open BackfillPaper7.Challenge Paper7Unicyclic Paper7OddIntegral

theorem integral_unicyclic_kappa {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsIntegralGraph G) (hU : IsUnicyclicWithCycle G b) (ho : Odd b) :
    kappa b ∣ 2*b := by
  apply kappa_dvd_of_prime_divisors
  intro q hq hp
  have h := proposition3_prime_divisibility G b hG (unicyclic_isOddGirth hU ho) q hq hp
  simpa only [unicyclic_cycleCount hU b, ite_true, mul_one] using h
#print axioms Paper7Corollary31.integral_unicyclic_kappa

theorem integral_unicyclic_order_lower {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsIntegralGraph G) (hU : IsUnicyclicWithCycle G b) (ho : Odd b)
    (hb : 15 ≤ b) : 102 ≤ Fintype.card V := by
  have hbound := proposition3_square_bound G b hG (unicyclic_isOddGirth hU ho)
  rw [unicyclic_card_edges G hU] at hbound
  have hsmall : (∑ v ∈ Finset.Icc 2 8, v^2 : ℕ) = 203 := by decide
  have hsub : Finset.Icc 2 8 ⊆ Finset.Icc 2 ((b+1)/2) := by
    intro v hv
    have hv' := Finset.mem_Icc.mp hv
    exact Finset.mem_Icc.mpr ⟨hv'.1, by omega⟩
  have hsum : (203 : ℕ) ≤ ∑ v ∈ Finset.Icc 2 ((b+1)/2), v^2 := by
    rw [← hsmall]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  omega
#print axioms Paper7Corollary31.integral_unicyclic_order_lower

theorem corollary31_graph {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsIntegralGraph G) (hU : IsUnicyclicWithCycle G b) (ho : Odd b) :
    kappa b ∣ 2*b ∧ 3 ∣ b ∧ (b ≠ 3 → 15 ≤ b ∧ 102 ≤ Fintype.card V) := by
  have hb := unicyclic_three_le hU
  have hk := integral_unicyclic_kappa G b hG hU ho
  refine ⟨hk, three_dvd_of_kappa b hb ho hk, ?_⟩
  intro hne
  have h15 := fifteen_le_of_kappa b hb ho hk hne
  exact ⟨h15, integral_unicyclic_order_lower G b hG hU ho h15⟩
#print axioms Paper7Corollary31.corollary31_graph

end Paper7Corollary31
