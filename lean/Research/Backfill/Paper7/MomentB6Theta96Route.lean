import Research.Backfill.Paper7.MomentB6TenComplete

/-! Source-only original theta=96 route. No validation has been run by the
source author. The finite histogram data below are consequences of the
original predicate and actual coordinate capacity, not new assumptions on PQ.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6FeatureCatalog_theta96 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (ht : sm.2 = 96) : sm = (17,96) := by
  have hc := b6FeatureCatalog_m4_le_138 sm hsm (by omega)
  rcases hc with rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_theta96

def B6Theta96Data (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  7 ≤ ∑ i, z i ∧ (∑ i, z i) ≤ 13 ∧ Q ≤ ∑ i, z i ∧
    11 ≤ (∑ i, z i) + Q ∧
    (2 ≤ Q → (∑ i, z i) ≤ 11) ∧
    (Q ≤ 1 → (∑ i, z i) + Q ≤ 13) ∧
    (∑ i, z i^2) + 3*(∑ i, z i) + 2*Q = 84
#print axioms Paper7MomentCounts.B6Theta96Data

theorem b6_theta96_data_of_accept (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ ∑ i, z i) (hg : b6ZQAccept z Q)
    (ht : 12 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) +
      ∑ i, (z i : ℤ)^2 = 96) : B6Theta96Data z Q := by
  obtain ⟨sm,hsm,hM,hS,hl⟩ := hg.2.2
  have he := b6FeatureCatalog_theta96 sm hsm (hM.trans ht)
  rw [he] at hS hl
  norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat] at hS hl
  have hlo : 11 ≤ (∑ i, z i) + Q := by exact_mod_cast (show
      (11 : ℤ) ≤ ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ) by omega)
  have hlarge : 2 ≤ Q → (∑ i, z i) ≤ 11 := by
    intro htwo
    have htwoI : (2 : ℤ) ≤ Q := by exact_mod_cast htwo
    have hl' := hl
    rw [max_eq_left htwoI] at hl'
    exact_mod_cast (show ((∑ i, z i : ℕ) : ℤ) ≤ 11 by omega)
  have hsmall : Q ≤ 1 → (∑ i, z i) + Q ≤ 13 := by
    intro hone
    have honeI : (Q : ℤ) ≤ 2 := by exact_mod_cast (show Q ≤ 2 by omega)
    have hl' := hl
    rw [max_eq_right honeI] at hl'
    exact_mod_cast (show ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ) ≤ 13 by omega)
  have hZ13 : (∑ i, z i) ≤ 13 := by
    by_cases htwo : 2 ≤ Q
    · have h := hlarge htwo; omega
    · have h := hsmall (by omega); omega
  have hZ7 : 7 ≤ ∑ i, z i := by
    by_contra hn
    have hZ6 : (∑ i, z i) ≤ 6 := by omega
    have hu := b6_zq_theta_upper z Q hQ
    have hz0 : (0 : ℤ) ≤ ((∑ i, z i : ℕ) : ℤ) := Int.natCast_nonneg _
    have hz6 : ((∑ i, z i : ℕ) : ℤ) ≤ 6 := by exact_mod_cast hZ6
    have hp := mul_nonneg (sub_nonneg.mpr hz6)
      (add_nonneg (show (0 : ℤ) ≤ 6 by norm_num) hz0)
    nlinarith only [hu,ht,hz6,hp]
  have hm : (∑ i, z i^2) + 3*(∑ i, z i) + 2*Q = 84 := by
    have hmI : (∑ i, (z i : ℤ)^2) + 3*((∑ i, z i : ℕ) : ℤ) +
        2*(Q : ℤ) = 84 := by omega
    exact_mod_cast hmI
  exact ⟨hZ7,hZ13,hQ,hlo,hlarge,hsmall,hm⟩
#print axioms Paper7MomentCounts.b6_theta96_data_of_accept

theorem b6_theta96_accept_of_data (z : Fin 6 → ℕ) (Q : ℕ)
    (h : B6Theta96Data z Q) : b6ZQAccept z Q ∧
      12 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) +
        ∑ i, (z i : ℤ)^2 = 96 := by
  rcases h with ⟨hlo,hhi,hQ,hload,hlarge,hsmall,hm⟩
  have hmI : (∑ i, (z i : ℤ)^2) + 3*((∑ i, z i : ℕ) : ℤ) +
      2*(Q : ℤ) = 84 := by exact_mod_cast hm
  have ht : 12 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) +
      ∑ i, (z i : ℤ)^2 = 96 := by omega
  refine ⟨⟨by omega,by omega,(17,96),by norm_num [b6FeatureCatalog],
    ht.symm,?_,?_⟩,ht⟩
  · norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (show 17 ≤ 6 + ((∑ i, z i) + Q) by omega)
  · norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
    by_cases htwo : 2 ≤ Q
    · have hz := hlarge htwo
      have hzI : ((∑ i, z i : ℕ) : ℤ) ≤ 11 := by exact_mod_cast hz
      have htwoI : (2 : ℤ) ≤ Q := by exact_mod_cast htwo
      rw [max_eq_left htwoI]
      omega
    · have hz := hsmall (by omega)
      have hzI : ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ) ≤ 13 := by exact_mod_cast hz
      have htwoI : (Q : ℤ) ≤ 2 := by exact_mod_cast (show Q ≤ 2 by omega)
      rw [max_eq_right htwoI]
      omega
#print axioms Paper7MomentCounts.b6_theta96_accept_of_data

theorem b6_theta96_coordinate_le_seven (z : Fin 6 → ℕ) (Q : ℕ)
    (h : B6Theta96Data z Q) (i : Fin 6) : z i ≤ 7 := by
  have hm := h.2.2.2.2.2.2
  have hz := Finset.single_le_sum (fun k _ => Nat.zero_le (z k)) (Finset.mem_univ i)
  have hs := Finset.single_le_sum (fun k _ => Nat.zero_le (z k^2)) (Finset.mem_univ i)
  nlinarith
#print axioms Paper7MomentCounts.b6_theta96_coordinate_le_seven

end Paper7MomentCounts
