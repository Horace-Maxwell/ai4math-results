import Research.Backfill.Paper7.C61UnitGapArithmetic
import Research.Backfill.Paper7.C61FourTraceConstraints

/-! NEW SOURCE ONLY. Actual unit witnesses and ordinary pair identities
exclude the normalized two- and three-site q-support configurations. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge Paper7C61Three
open BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

def MultiQOrdinaryData (p q : Fin 6 → ℕ) : Prop :=
  (PairTwo p q ∧ totalP 6 p+totalQ 6 q=27 ∧ totalQ 6 q≤9) ∨
  (PairThree p q ∧ totalP 6 p+totalQ 6 q=32 ∧ totalQ 6 q≤4)
#print axioms Paper7C61Four.MultiQOrdinaryData

theorem unit_positive_previous_zero (p q : Fin 6 → ℕ)
    (hw : FullUnitWitness p q) (k : Fin 6) (hk : 0<q k) : q (k+5)=0 := by
  by_contra hn
  have hh := full_unit_witness_adjacent p q hw (k+5) (Nat.pos_of_ne_zero hn)
  have hz : q k=0 := by
    simpa only [nxt_six,add_assoc,show (5 : Fin 6)+1=0 from rfl,add_zero] using hh
  omega
#print axioms Paper7C61Four.unit_positive_previous_zero

theorem unit_short_gap_one (p q : Fin 6 → ℕ) (hw : FullUnitWitness p q)
    (hq0 : 0<q 0) (hq2 : 0<q 2) : p 1=1 := by
  have hq1 : q 1=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 0 hq0
  obtain ⟨y,hy0,hy1,hy⟩ := hw 0 hq0
  norm_num [nxt_six] at hy1
  have hy2 := (hy 2).1 hq2
  have hr := (hy 1).2 hq1
  norm_num [nxt_six,prv_six] at hr
  rw [hy0,hy1,hy2] at hr
  have hpR : (p 1 : ℝ)=1 := by nlinarith only [hr]
  exact_mod_cast hpR
#print axioms Paper7C61Four.unit_short_gap_one

theorem unit_opposite_gap_cases (p q : Fin 6 → ℕ) (hw : FullUnitWitness p q)
    (hq0 : 0<q 0) (hq3 : 0<q 3) (hq1 : q 1=0) (hq2 : q 2=0) :
    (p 1=0 ∧ p 2=0) ∨ (p 1=2 ∧ p 2=2) := by
  obtain ⟨y,hy0,hy1,hy⟩ := hw 0 hq0
  norm_num [nxt_six] at hy1
  have hy3 := (hy 3).1 hq3
  have hr1 := (hy 1).2 hq1
  have hr2 := (hy 2).2 hq2
  norm_num [nxt_six,prv_six] at hr1 hr2
  rw [hy0,hy1] at hr1
  have hy2 : y 2=1-(p 1 : ℝ) := by nlinarith only [hr1]
  rw [hy1,hy2,hy3] at hr2
  exact unit_gap_two_cases (p 1) (p 2) (by nlinarith only [hr2])
#print axioms Paper7C61Four.unit_opposite_gap_cases

theorem unit_long_gap_equation (p q : Fin 6 → ℕ) (hw : FullUnitWitness p q)
    (hq0 : 0<q 0) (hq2 : 0<q 2)
    (hq3 : q 3=0) (hq4 : q 4=0) (hq5 : q 5=0) :
    ((p 3 : ℝ)-1)*((p 4 : ℝ)-1)*((p 5 : ℝ)-1)=
      ((p 3 : ℝ)-1)+((p 5 : ℝ)-1) := by
  obtain ⟨y,hy2,hy3,hy⟩ := hw 2 hq2
  norm_num [nxt_six] at hy3
  have hy0 := (hy 0).1 hq0
  have hr3 := (hy 3).2 hq3
  have hr4 := (hy 4).2 hq4
  have hr5 := (hy 5).2 hq5
  norm_num [nxt_six,prv_six] at hr3 hr4 hr5
  rw [hy2,hy3] at hr3
  have hy4 : y 4=1-(p 3 : ℝ) := by nlinarith only [hr3]
  rw [hy3,hy4] at hr4
  have hy5 : y 5=(1-(p 4 : ℝ))*(1-(p 3 : ℝ))-1 := by nlinarith only [hr4]
  rw [hy4,hy5,hy0] at hr5
  nlinarith only [hr5]
#print axioms Paper7C61Four.unit_long_gap_equation

theorem multiq_three_ones_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1=1) (hp3 : p 3=1) (hp5 : p 5=1)
    (hq1 : q 1=0) (hq3 : q 3=0) (hq5 : q 5=0)
    (hd : MultiQOrdinaryData p q) : False := by
  rcases hd with ⟨hm,hL,_hQ⟩ | ⟨hm,hL,_hQ⟩
  · obtain ⟨h0,h1,h2⟩ := hm
    norm_num [coefficientTwo,hp1,hp3,hp5,hq1,hq3,hq5] at h0 h1 h2
    have hLR : (totalP 6 p : ℝ)+(totalQ 6 q : ℝ)=27 := by exact_mod_cast hL
    norm_num [totalP,totalQ,Fin.sum_univ_six,hp1,hp3,hp5,hq1,hq3,hq5] at hLR
    have hn0 : (0 : ℝ)≤q 0 := Nat.cast_nonneg (q 0)
    have hn2 : (0 : ℝ)≤q 2 := Nat.cast_nonneg (q 2)
    have hn4 : (0 : ℝ)≤q 4 := Nat.cast_nonneg (q 4)
    nlinarith only [h0,h1,h2,hLR,hn0,hn2,hn4]
  · obtain ⟨h0,h1,h2⟩ := hm
    norm_num [coefficientThree,hp1,hp3,hp5,hq1,hq3,hq5] at h0 h1 h2
    have hLR : (totalP 6 p : ℝ)+(totalQ 6 q : ℝ)=32 := by exact_mod_cast hL
    norm_num [totalP,totalQ,Fin.sum_univ_six,hp1,hp3,hp5,hq1,hq3,hq5] at hLR
    have hn0 : (0 : ℝ)≤q 0 := Nat.cast_nonneg (q 0)
    have hn2 : (0 : ℝ)≤q 2 := Nat.cast_nonneg (q 2)
    have hn4 : (0 : ℝ)≤q 4 := Nat.cast_nonneg (q 4)
    nlinarith only [h0,h1,h2,hLR,hn0,hn2,hn4]
#print axioms Paper7C61Four.multiq_three_ones_impossible

theorem multiq_alternating_support_impossible (p q : Fin 6 → ℕ)
    (hw : FullUnitWitness p q) (hd : MultiQOrdinaryData p q)
    (hq0 : 0<q 0) (hq2 : 0<q 2) (hq4 : 0<q 4) : False := by
  have hq1 : q 1=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 0 hq0
  have hq3 : q 3=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 2 hq2
  have hq5 : q 5=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 4 hq4
  have hp1 := unit_short_gap_one p q hw hq0 hq2
  have hw2 := full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw)
  have hp3 : p 3=1 := by
    have hh := unit_short_gap_one (shiftSix (shiftSix p)) (shiftSix (shiftSix q)) hw2
      (by simpa [shiftSix] using hq2) (by simpa [shiftSix] using hq4)
    simpa [shiftSix] using hh
  have hw4 := full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw2)
  have hp5 : p 5=1 := by
    have hh := unit_short_gap_one (shiftSix (shiftSix (shiftSix (shiftSix p))))
      (shiftSix (shiftSix (shiftSix (shiftSix q)))) hw4
      (by simpa [shiftSix] using hq4) (by simpa [shiftSix] using hq0)
    simpa [shiftSix] using hh
  exact multiq_three_ones_impossible p q hp1 hp3 hp5 hq1 hq3 hq5 hd
#print axioms Paper7C61Four.multiq_alternating_support_impossible

theorem multiq_opposite_support_impossible (p q : Fin 6 → ℕ)
    (hw : FullUnitWitness p q) (hd : MultiQOrdinaryData p q)
    (hq0 : 0<q 0) (hq3 : 0<q 3) : False := by
  have hq1 : q 1=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 0 hq0
  have hq5 : q 5=0 := by simpa using unit_positive_previous_zero p q hw 0 hq0
  have hq4 : q 4=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 3 hq3
  have hq2 : q 2=0 := by simpa using unit_positive_previous_zero p q hw 3 hq3
  have hA := unit_opposite_gap_cases p q hw hq0 hq3 hq1 hq2
  have hw3 := full_unit_witness_shift _ _ (full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw))
  have hB : (p 4=0 ∧ p 5=0) ∨ (p 4=2 ∧ p 5=2) := by
    have hh := unit_opposite_gap_cases (shiftSix (shiftSix (shiftSix p)))
      (shiftSix (shiftSix (shiftSix q))) hw3
      (by simpa [shiftSix] using hq3) (by simpa [shiftSix] using hq0)
      (by simpa [shiftSix] using hq4) (by simpa [shiftSix] using hq5)
    simpa [shiftSix] using hh
  rcases hd with ⟨hm,hL,_hQ⟩ | ⟨hm,_hL,_hQ⟩
  · have hp : p 1=2 ∧ p 2=2 ∧ p 4=2 ∧ p 5=2 := by
      have hh := hm.2.1
      rcases hA with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
        rcases hB with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;>
        norm_num [coefficientTwo,ha,hb,hc,hd,hq1,hq2,hq4,hq5] at hh
      exact ⟨ha,hb,hc,hd⟩
    have hh := hm.1
    norm_num [coefficientTwo,hp.1,hp.2.2.1,hq1,hq4] at hh
    have hLR : (totalP 6 p : ℝ)+(totalQ 6 q : ℝ)=27 := by exact_mod_cast hL
    norm_num [totalP,totalQ,Fin.sum_univ_six,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
      hq1,hq2,hq4,hq5] at hLR
    have hn0 : (0 : ℝ)≤q 0 := Nat.cast_nonneg (q 0)
    have hn3 : (0 : ℝ)≤q 3 := Nat.cast_nonneg (q 3)
    nlinarith only [hh,hLR,hn0,hn3]
  · have hh := hm.2.1
    rcases hA with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
      rcases hB with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;>
      norm_num [coefficientThree,ha,hb,hc,hd,hq1,hq2,hq4,hq5] at hh
#print axioms Paper7C61Four.multiq_opposite_support_impossible

theorem support_four_four_positive_other_zero (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card≤4) (h1 : 0<p 1) (h3 : 0<p 3)
    (h4 : 0<p 4) (h5 : 0<p 5) : p 0=0 ∧ p 2=0 := by
  have hs : (∑ k : Fin 6, if 0<p k then (1 : ℕ) else 0)≤4 := by
    have hcard : (Kp 6 p).card = ∑ k : Fin 6, if 0<p k then (1 : ℕ) else 0 := by
      simp only [Kp,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [← hcard]
    exact hK
  simp only [Fin.sum_univ_six,ite_eq_left h1,ite_eq_left h3,ite_eq_left h4,ite_eq_left h5] at hs
  constructor
  · by_contra hn
    simp only [ite_eq_left (Nat.pos_of_ne_zero hn)] at hs
    omega
  · by_contra hn
    simp only [ite_eq_left (Nat.pos_of_ne_zero hn)] at hs
    omega
#print axioms Paper7C61Four.support_four_four_positive_other_zero

theorem multiq_distance_two_support_impossible (p q : Fin 6 → ℕ)
    (hw : FullUnitWitness p q) (hK : (Kp 6 p).card≤4)
    (hd : MultiQOrdinaryData p q) (hq0 : 0<q 0) (hq2 : 0<q 2)
    (hq4 : q 4=0) : False := by
  have hq1 : q 1=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 0 hq0
  have hq3 : q 3=0 := by simpa [nxt_six] using full_unit_witness_adjacent p q hw 2 hq2
  have hq5 : q 5=0 := by simpa using unit_positive_previous_zero p q hw 0 hq0
  have hp1 := unit_short_gap_one p q hw hq0 hq2
  have hh := unit_long_gap_equation p q hw hq0 hq2 hq3 hq4 hq5
  rcases unit_gap_three_cases (p 3) (p 4) (p 5) hh with
    ⟨hc,he⟩ | ⟨hc,hd4,he⟩ | ⟨hc,hd4,he⟩ | ⟨hc,hd4,he⟩ | ⟨hc,hd4,he⟩
  · exact multiq_three_ones_impossible p q hp1 hc he hq1 hq3 hq5 hd
  · obtain ⟨hp0,hp2⟩ := support_four_four_positive_other_zero p hK
      (by omega) (by omega) (by omega) (by omega)
    have hP : totalP 6 p=9 := by norm_num [totalP,Fin.sum_univ_six,hp0,hp1,hp2,hc,hd4,he]
    rcases hd with ⟨_,hL,hQ⟩ | ⟨_,hL,hQ⟩ <;> omega
  · obtain ⟨hp0,hp2⟩ := support_four_four_positive_other_zero p hK
      (by omega) (by omega) (by omega) (by omega)
    have hP : totalP 6 p=8 := by norm_num [totalP,Fin.sum_univ_six,hp0,hp1,hp2,hc,hd4,he]
    rcases hd with ⟨_,hL,hQ⟩ | ⟨_,hL,hQ⟩ <;> omega
  · rcases hd with ⟨hm,_,_⟩ | ⟨hm,_,_⟩
    · obtain ⟨h0,h1,h2⟩ := hm
      norm_num [coefficientTwo,hp1,hc,hd4,he,hq1,hq3,hq4,hq5] at h0 h1 h2
      linarith only [h0,h1,h2]
    · obtain ⟨h0,h1,h2⟩ := hm
      norm_num [coefficientThree,hp1,hc,hd4,he,hq1,hq3,hq4,hq5] at h0 h1 h2
      linarith only [h0,h1,h2]
  · rcases hd with ⟨hm,_,_⟩ | ⟨hm,_,_⟩
    · obtain ⟨h0,h1,h2⟩ := hm
      norm_num [coefficientTwo,hp1,hc,hd4,he,hq1,hq3,hq4,hq5] at h0 h1 h2
      linarith only [h0,h1,h2]
    · obtain ⟨h0,h1,h2⟩ := hm
      norm_num [coefficientThree,hp1,hc,hd4,he,hq1,hq3,hq4,hq5] at h0 h1 h2
      linarith only [h0,h1,h2]
#print axioms Paper7C61Four.multiq_distance_two_support_impossible

end Paper7C61Four
