import Research.Backfill.Paper7.C61MultiQPositions
import Research.Backfill.Paper7.C61FourWithoutThreeQpositive
import Research.Backfill.Paper7.C61HigherRemainderData

/-! NEW SOURCE ONLY. Cyclic transport covers every support with at least
two positive q coordinates. The final theorem returns to the original
Perron-four, cardinality-four, beta-six profile. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Higher Paper7C61Three
open scoped BigOperators Classical

theorem multiq_p_support_shift (p : Fin 6 → ℕ) :
    (Kp 6 (shiftSix p)).card=(Kp 6 p).card := by
  have hcard (f : Fin 6 → ℕ) :
      (Kp 6 f).card = ∑ k : Fin 6, if 0<f k then (1 : ℕ) else 0 := by
    simp only [Kp,Finset.card_eq_sum_ones,Finset.sum_filter]
  have sumShift (f : Fin 6 → ℕ) : (∑ k, shiftSix f k) = ∑ k, f k := by
    simp only [Fin.sum_univ_six,shiftSix]
    change f 1+f 2+f 3+f 4+f 5+f 0 = f 0+f 1+f 2+f 3+f 4+f 5
    omega
  rw [hcard,hcard]
  exact sumShift (fun k => if 0<p k then (1 : ℕ) else 0)
#print axioms Paper7C61Four.multiq_p_support_shift

theorem multiq_q_support_shift (q : Fin 6 → ℕ) :
    (Kq 6 (shiftSix q)).card=(Kq 6 q).card := by
  change (Kp 6 (shiftSix q)).card=(Kp 6 q).card
  exact multiq_p_support_shift q
#print axioms Paper7C61Four.multiq_q_support_shift

theorem multiq_q_total_shift (q : Fin 6 → ℕ) :
    totalQ 6 (shiftSix q)=totalQ 6 q := by
  norm_num [totalQ,shiftSix,Fin.sum_univ_six]
  omega
#print axioms Paper7C61Four.multiq_q_total_shift

theorem multiq_ordinary_data_shift (p q : Fin 6 → ℕ)
    (h : MultiQOrdinaryData p q) : MultiQOrdinaryData (shiftSix p) (shiftSix q) := by
  rcases h with ⟨hm,hL,hQ⟩ | ⟨hm,hL,hQ⟩
  · exact Or.inl ⟨pair_two_shift p q hm,by rwa [total_shift],by rwa [multiq_q_total_shift]⟩
  · exact Or.inr ⟨pair_three_shift p q hm,by rwa [total_shift],by rwa [multiq_q_total_shift]⟩
#print axioms Paper7C61Four.multiq_ordinary_data_shift

def MultiQContext (p q : Fin 6 → ℕ) : Prop :=
  FullUnitWitness p q ∧ (Kp 6 p).card≤4 ∧
    MultiQOrdinaryData p q ∧ 2≤(Kq 6 q).card
#print axioms Paper7C61Four.MultiQContext

theorem multiq_context_shift (p q : Fin 6 → ℕ)
    (h : MultiQContext p q) : MultiQContext (shiftSix p) (shiftSix q) := by
  exact ⟨full_unit_witness_shift p q h.1,
    by rw [multiq_p_support_shift]; exact h.2.1,
    multiq_ordinary_data_shift p q h.2.2.1,
    by rw [multiq_q_support_shift]; exact h.2.2.2⟩
#print axioms Paper7C61Four.multiq_context_shift

theorem multiq_zero_positive_impossible (p q : Fin 6 → ℕ)
    (h : MultiQContext p q) (hq0 : 0<q 0) : False := by
  obtain ⟨hw,hK,hd,hqK⟩ := h
  have hq1 : q 1=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 0 hq0
  have hq5 : q 5=0 := by simpa using unit_positive_previous_zero p q hw 0 hq0
  by_cases hq2 : 0<q 2
  · by_cases hq4 : 0<q 4
    · exact multiq_alternating_support_impossible p q hw hd hq0 hq2 hq4
    · exact multiq_distance_two_support_impossible p q hw hK hd hq0 hq2 (by omega)
  have hq2z : q 2=0 := by omega
  by_cases hq3 : 0<q 3
  · exact multiq_opposite_support_impossible p q hw hd hq0 hq3
  have hq3z : q 3=0 := by omega
  have hq4 : 0<q 4 := by
    by_contra hn
    have hq4z : q 4=0 := by omega
    have hs : 2≤∑ k : Fin 6, if 0<q k then (1 : ℕ) else 0 := by
      have hcard : (Kq 6 q).card = ∑ k : Fin 6, if 0<q k then (1 : ℕ) else 0 := by
        simp only [Kq,Finset.card_eq_sum_ones,Finset.sum_filter]
      rw [← hcard]
      exact hqK
    norm_num only [Fin.sum_univ_six,hq0,hq1,hq2z,hq3z,hq4z,hq5,Nat.lt_irrefl,ite_true,ite_false] at hs
  have h2 := multiq_context_shift _ _ (multiq_context_shift _ _ ⟨hw,hK,hd,hqK⟩)
  have h4 := multiq_context_shift _ _ (multiq_context_shift _ _ h2)
  apply multiq_distance_two_support_impossible
    (shiftSix (shiftSix (shiftSix (shiftSix p))))
    (shiftSix (shiftSix (shiftSix (shiftSix q)))) h4.1 h4.2.1 h4.2.2.1
  · simpa [shiftSix] using hq4
  · simpa [shiftSix] using hq0
  · simpa [shiftSix] using hq2z
#print axioms Paper7C61Four.multiq_zero_positive_impossible

theorem full_unit_multiq_ordinary_impossible (p q : Fin 6 → ℕ)
    (hw : FullUnitWitness p q) (hK : (Kp 6 p).card≤4)
    (hd : MultiQOrdinaryData p q) (hqK : 2≤(Kq 6 q).card) : False := by
  have h : MultiQContext p q := ⟨hw,hK,hd,hqK⟩
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(Kq 6 q).card by omega)
  have hjp : 0<q j := (Finset.mem_filter.mp hj).2
  have h1 := multiq_context_shift _ _ h
  have h2 := multiq_context_shift _ _ h1
  have h3 := multiq_context_shift _ _ h2
  have h4 := multiq_context_shift _ _ h3
  have h5 := multiq_context_shift _ _ h4
  fin_cases j
  · exact multiq_zero_positive_impossible _ _ h hjp
  · apply multiq_zero_positive_impossible _ _ h1
    simpa [shiftSix] using hjp
  · apply multiq_zero_positive_impossible _ _ h2
    simpa [shiftSix] using hjp
  · apply multiq_zero_positive_impossible _ _ h3
    simpa [shiftSix] using hjp
  · apply multiq_zero_positive_impossible _ _ h4
    simpa [shiftSix] using hjp
  · apply multiq_zero_positive_impossible _ _ h5
    simpa [shiftSix] using hjp
#print axioms Paper7C61Four.full_unit_multiq_ordinary_impossible

theorem root_four_card_four_multiq_beta_six_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q≤42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hc : card (actual p q)=4)
    (hb : unitExponent p q=6) (hqK : 2≤(Kq 6 q).card) : False := by
  have hprofile := (root_four_profile (actual p q) h4).1
  have haLt := (actual p q 0).isLt
  have hbLt := (actual p q 1).isLt
  have hcases : ((actual p q 0).val=2 ∧ (actual p q 1).val=1) ∨
      ((actual p q 0).val=1 ∧ (actual p q 1).val=2) := by omega
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p=4 := by omega
  have hsupp := support_add_delta0_le_six p
  have hK : (Kp 6 p).card≤4 := by unfold zeroExponent at ha; omega
  have hw := beta_six_full_unit_witness p q hb
  have hL := (root_four_parameter_relations p q hn hG h4).1
  have hn' : 6+totalP 6 p+2*totalQ 6 q≤42 := hn
  apply full_unit_multiq_ordinary_impossible p q hw hK ?_ hqK
  rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl ⟨actual_two_twice_pair_two p q h0,by omega,by omega⟩
  · exact Or.inr ⟨actual_three_twice_pair_three p q h1,by omega,by omega⟩
#print axioms Paper7C61Four.root_four_card_four_multiq_beta_six_impossible

end Paper7C61Four
