import Research.Backfill.Paper7.C61SingletonEffectiveMonodromy
import Research.Backfill.Paper7.C61FourThreeTwiceSingleton
import Research.Backfill.Paper7.C61FourQzeroClassification

/-! NEW SOURCE ONLY. The effective integral parameters are derived from the
original singleton q; their moments, cap, zero, and monodromy are all proved. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Three
open scoped BigOperators Classical

theorem p_support_four_zero_away (p : Fin 6 → ℕ) (j : Fin 6)
    (hK : (Kp 6 p).card≤4) : ∃ i : Fin 6, i≠j ∧ p i=0 := by
  by_contra! hn
  have hsub : (Finset.univ.erase j : Finset (Fin 6)) ⊆ Kp 6 p := by
    intro i hi
    have hij : i≠j := (Finset.mem_erase.mp hi).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,Nat.pos_of_ne_zero (hn i hij)⟩
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,
    Fintype.card_fin] at hc
  omega
#print axioms Paper7C61Four.p_support_four_zero_away

theorem singleton_effective_parameters_impossible (p q : Fin 6 → ℕ) (j k : ℕ)
    (head : Fin 6) (hq : ∀ i : Fin 6, i≠head → q i=0)
    (hqhead : q head=3*k) (hk : k=1 ∨ k=2 ∨ k=3)
    (hj : j=p head) (hK : (Kp 6 p).card≤4)
    (hL : totalP 6 p+totalQ 6 q=27)
    (hS : squares 6 (fun i => p i+q i)+2*totalQ 6 q=243)
    (hcap : ∀ i, p i+q i≤13) (hm : Mono 6 p q 2=1) : False := by
  let r : Fin 6 → ℕ := fun i => p i+if i=head then 4*k else 0
  have hQ : totalQ 6 q=3*k := by
    have he : totalQ 6 q=q head := by
      apply Finset.sum_eq_single head
      · intro i _ hi
        exact hq i hi
      · intro hn
        exact (hn (Finset.mem_univ head)).elim
    exact he.trans hqhead
  have hP : totalP 6 r=totalP 6 p+4*k := by
    simp [r,totalP,Finset.sum_add_distrib]
  have hSq : squares 6 r=squares 6 (fun i => p i+q i)+2*k*j+7*k^2 := by
    have he (i : Fin 6) : r i^2=(p i+q i)^2+
        if i=head then 2*k*j+7*k^2 else 0 := by
      by_cases hi : i=head
      · subst i
        simp only [r,ite_true,hqhead,hj]
        ring
      · simp only [r,ite_eq_right hi,hq i hi,add_zero]
    simp only [squares,he,Finset.sum_add_distrib]
    simp [Nat.add_assoc]
  have hrcap (i : Fin 6) : r i≤13+k := by
    have hc := hcap i
    by_cases hi : i=head
    · subst i
      simp only [r,ite_true]
      rw [hqhead] at hc
      omega
    · simp only [r,ite_eq_right hi,add_zero]
      omega
  have hrm : Mono 6 r (fun _ => 0) 2=1 := by
    have he (i : Fin 6) : coefficientTwo r (fun _ => 0) i=coefficientTwo p q i := by
      by_cases hi : i=head
      · subst i
        norm_num [r,coefficientTwo,hqhead,Nat.cast_add,Nat.cast_mul]
        ring
      · simp [r,coefficientTwo,hi,hq i hi]
    rw [mono_two_six_product] at hm ⊢
    simpa only [he] using hm
  have hrzero : ∃ i : Fin 6, r i=0 := by
    obtain ⟨i,hi,hpi⟩ := p_support_four_zero_away p head hK
    exact ⟨i,by simp [r,hi,hpi]⟩
  apply effective_singleton_zero_impossible r k j hk hrzero
  refine ⟨by omega,by omega,?_,hrcap,⟨head,?_⟩,hrm⟩
  · have hc := hcap head
    omega
  · simp [r,hj]
#print axioms Paper7C61Four.singleton_effective_parameters_impossible

theorem root_four_two_twos_one_three_qpositive_beta_six_singleton_impossible
    (p q : Fin 6 → ℕ) (hn : nOf 6 p q≤42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val=2)
    (h1 : (actual p q 1).val=1) (hb : unitExponent p q=6)
    (hK : (Kq 6 q).card=1) : False := by
  have hc := (root_four_profile (actual p q) h4).1
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p=4 := by omega
  obtain ⟨hL,hS⟩ := Paper7C61Higher.root_four_parameter_relations p q hn hG h4
  rw [h0,h1,hb] at hL
  rw [h1,hb] at hS
  have hL27 : totalP 6 p+totalQ 6 q=27 := by omega
  have hS243 : squares 6 (fun i => p i+q i)+2*totalQ 6 q=243 := by omega
  have hn' : 6+totalP 6 p+2*totalQ 6 q≤42 := hn
  have hQ9 : totalQ 6 q≤9 := by omega
  have hQpos : 0<totalQ 6 q := by
    have hs := Paper7Rank.support_card_le_sum 6 q
    change (Kq 6 q).card≤totalQ 6 q at hs
    omega
  have hm := actual_two_monodromy p q h0
  obtain ⟨head,hq⟩ := q_support_card_one_unique q hK
  have hQhead : totalQ 6 q=q head := by
    apply Finset.sum_eq_single head
    · intro i _ hi
      exact hq i hi
    · intro hh
      exact (hh (Finset.mem_univ head)).elim
  obtain ⟨k,hk⟩ := mono_two_singleton_total_divisible_three p q hm ⟨head,hq⟩
  have hkc : k=1 ∨ k=2 ∨ k=3 := by omega
  exact singleton_effective_parameters_impossible p q (p head) k head hq
    (by omega) hkc rfl (alpha_at_least_four_support p (by omega)) hL27 hS243
    (Paper7C61Higher.root_four_load_le_thirteen p q hn hG h4) hm
#print axioms Paper7C61Four.root_four_two_twos_one_three_qpositive_beta_six_singleton_impossible

end Paper7C61Four
