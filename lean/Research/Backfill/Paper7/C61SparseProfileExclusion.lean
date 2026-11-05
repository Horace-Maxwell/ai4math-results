import Research.Backfill.Paper7.C61FourSquareObstruction
import Research.Backfill.Paper7.C61ThreeSquareObstruction
import Research.Backfill.Paper7.C61SparseSupportRepresentation
import Research.Backfill.Paper7.C61HigherRemainderData

/-! Source-only recovery of the full {2,2,3,5} profile exclusion.
All parameters remain arbitrary. No finite parameter table is assumed.
This file has not been compiled or independently accepted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Sparse
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61ThreeSquareObstruction
open scoped BigOperators Classical

theorem support_four_sum36_square576_impossible (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4) (hP : totalP 6 p = 36)
    (hS : squares 6 p = 576) : False := by
  obtain ⟨a,b,c,d,hs,hq⟩ := support_four_moments p hK
  rw [hP] at hs
  rw [hS] at hq
  exact four_no_sum36_square576 a b c d hs hq
#print axioms Paper7C61Sparse.support_four_sum36_square576_impossible

theorem support_three_sum34_square576_impossible (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 3) (hP : totalP 6 p = 34)
    (hS : squares 6 p = 576) : False := by
  obtain ⟨a,b,c,hs,hq⟩ := support_three_moments p hK
  rw [hP] at hs
  rw [hS] at hq
  exact not_sum34_squares576 a b c hs hq
#print axioms Paper7C61Sparse.support_three_sum34_square576_impossible

theorem support_three_sum35_square577_impossible (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 3) (hP : totalP 6 p = 35)
    (hS : squares 6 p = 577) : False := by
  obtain ⟨a,b,c,hs,hq⟩ := support_three_moments p hK
  rw [hP] at hs
  rw [hS] at hq
  exact not_sum35_squares577 a b c hs hq
#print axioms Paper7C61Sparse.support_three_sum35_square577_impossible

/-- A q coordinate attached inside p support adds no load-support position. -/
theorem singleton_q_load_support_subset (p q : Fin 6 → ℕ) (t : Fin 6)
    (hp : 0 < p t) (hq : ∀ k, k ≠ t → q k = 0) :
    Kp 6 (fun k => p k + q k) ⊆ Kp 6 p := by
  intro k hk
  have hkpos := (Finset.mem_filter.mp hk).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ k, ?_⟩
  by_cases hkt : k = t
  · subst k
    exact hp
  · simpa only [hq k hkt, add_zero] using hkpos
#print axioms Paper7C61Sparse.singleton_q_load_support_subset

/-- A unit q coordinate outside p support adds exactly one to the square sum. -/
theorem singleton_q_outside_square (p q : Fin 6 → ℕ) (t : Fin 6)
    (hp : p t = 0) (ht : q t = 1) (hq : ∀ k, k ≠ t → q k = 0) :
    squares 6 (fun k => p k + q k) = squares 6 p + totalQ 6 q := by
  have hk (k : Fin 6) : (p k + q k)^2 = p k^2 + q k := by
    by_cases hkt : k = t
    · subst k
      simp only [hp, ht]
      norm_num
    · simp only [hq k hkt, add_zero]
  change (∑ k, (p k + q k)^2) = (∑ k, p k^2) + ∑ k, q k
  calc
    _ = ∑ k, (p k^2 + q k) := Finset.sum_congr rfl (fun k _ => hk k)
    _ = _ := Finset.sum_add_distrib
#print axioms Paper7C61Sparse.singleton_q_outside_square

/-- The Q=1 moment branch is impossible in both possible support positions. -/
theorem qone_sparse_moments_impossible (p q : Fin 6 → ℕ)
    (hQ : totalQ 6 q = 1) (hP : totalP 6 p = 34)
    (hS : squares 6 (fun k => p k + q k) = 577)
    (hK : (Kp 6 p).card ≤ 3) : False := by
  obtain ⟨t,ht,hq⟩ := totalQ_one_coordinate q hQ
  by_cases hp : 0 < p t
  · have hsub := singleton_q_load_support_subset p q t hp hq
    have hloadK : (Kp 6 (fun k => p k + q k)).card ≤ 3 :=
      (Finset.card_le_card hsub).trans hK
    have hloadP : totalP 6 (fun k => p k + q k) = 35 := by
      have hsum : totalP 6 (fun k => p k + q k) = totalP 6 p + totalQ 6 q := by
        simp only [totalP, totalQ, Finset.sum_add_distrib]
      omega
    exact support_three_sum35_square577_impossible
      (fun k => p k + q k) hloadK hloadP hS
  · have hp0 : p t = 0 := by omega
    have hs := singleton_q_outside_square p q t hp0 ht hq
    have hSp : squares 6 p = 576 := by omega
    exact support_three_sum34_square576_impossible p hK hP hSp
#print axioms Paper7C61Sparse.qone_sparse_moments_impossible

/-- Full exclusion of the actual {2,2,3,5} profile from original parameters. -/
theorem root_five_three_two_twos_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 2)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0) : False := by
  rcases root_five_three_two_twos_data p q hn hG h5 h0 h1 h2 with
    ⟨_hq,_hb,_ha,hP,hS,hK⟩ | ⟨hQ,_hb,_ha,hP,hS,hK⟩
  · exact support_four_sum36_square576_impossible p hK hP hS
  · exact qone_sparse_moments_impossible p q hQ hP hS hK
#print axioms Paper7C61Sparse.root_five_three_two_twos_impossible

/-- The only remaining Perron-five profile is {2,3,5}. This is a necessary
condition; existence or impossibility of that profile is not asserted. -/
theorem root_five_remaining_shape (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (h5 : RootFive (actual p q)) :
    (actual p q 0).val = 1 ∧ (actual p q 1).val = 1 ∧
      (actual p q 2).val = 0 := by
  obtain ⟨h2,h1,h0⟩ := root_five_contains_three p q hp hn hG h5
  rcases h0 with h0 | h0
  · exact ⟨h0,h1,h2⟩
  · exact (root_five_three_two_twos_impossible p q hn hG h5 h0 h1 h2).elim
#print axioms Paper7C61Sparse.root_five_remaining_shape

end Paper7C61Sparse
