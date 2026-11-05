import Research.Backfill.Paper7.DReachRecurrence
import Mathlib

/-!
Source-only technical repair by /root/paper6_tree_actual_final_review,
from the candidate authored by subagent p6_binding_spotcheck.
The two D cells below use the literal unfiltered (`false`) feature family and
the frozen D2 recurrence. The recurrence is converted to an actual PQ vector
using the DReachRecurrence source actually compiled successfully in dev198. Integer load and square-sum bounds
then exclude all possibilities. No cycle-filter inequality is introduced.
This source has not been compiled or accepted by either kernel.
-/

set_option autoImplicit false
open scoped Classical BigOperators
noncomputable section

namespace Paper7FeatureEmpty
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def emptyLoad {b : ℕ} (x : PQ b) : ℕ := ∑ i, (x.1 i + x.2 i)
#print axioms Paper7FeatureEmpty.emptyLoad

def emptySquareLoad {b : ℕ} (x : PQ b) : ℕ := ∑ i, (x.1 i + x.2 i) ^ 2
#print axioms Paper7FeatureEmpty.emptySquareLoad

theorem empty_weight_eq {b : ℕ} (x : PQ b) :
    weight x = emptyLoad x + qSum x := by
  simp only [weight, emptyLoad, pSum, qSum, Finset.sum_add_distrib]
  ring
#print axioms Paper7FeatureEmpty.empty_weight_eq

theorem empty_theta_eq {b : ℕ} (x : PQ b) :
    theta x = ((2 * b + 3 * emptyLoad x + emptySquareLoad x +
      2 * qSum x : ℕ) : ℤ) := by
  have hterm (i : Fin b) : thetaV (x.1 i) (x.2 i) =
      ((2 + 3 * (x.1 i + x.2 i) + (x.1 i + x.2 i) ^ 2 +
        2 * x.2 i : ℕ) : ℤ) := by
    unfold thetaV
    push_cast
    ring
  unfold theta
  simp_rw [hterm]
  rw [← Nat.cast_sum]
  congr 1
  simp only [emptyLoad, emptySquareLoad, qSum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]
  ring
#print axioms Paper7FeatureEmpty.empty_theta_eq

theorem empty_square_le {b : ℕ} (x : PQ b) :
    emptySquareLoad x ≤ emptyLoad x ^ 2 := by
  exact Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin b => x.1 i + x.2 i)
    (fun _ _ => Nat.zero_le _)
#print axioms Paper7FeatureEmpty.empty_square_le

theorem empty_sum_sq_le_mul {α : Type*} [Fintype α] (f : α → ℕ)
    (c : ℕ) (hf : ∀ i, f i ≤ c) :
    (∑ i, f i ^ 2) ≤ c * ∑ i, f i := by
  calc
    (∑ i, f i ^ 2) ≤ ∑ i, c * f i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left (f i) (hf i)
    _ = _ := (Finset.mul_sum _ _ _).symm
#print axioms Paper7FeatureEmpty.empty_sum_sq_le_mul

theorem empty_square_remainder {α : Type*} [Fintype α] (f : α → ℕ) (i : α) :
    (∑ j, f j ^ 2) ≤ f i ^ 2 + ((∑ j, f j) - f i) ^ 2 := by
  classical
  have hs := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have hsq := Finset.add_sum_erase Finset.univ (fun j => f j ^ 2)
    (Finset.mem_univ i)
  have hrem := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ.erase i) (f := f) (fun _ _ => Nat.zero_le _)
  have heq : (∑ j ∈ Finset.univ.erase i, f j) = (∑ j, f j) - f i := by omega
  rw [heq] at hrem
  omega
#print axioms Paper7FeatureEmpty.empty_square_remainder

theorem empty_square_gap_eighteen {α : Type*} [Fintype α] (f : α → ℕ)
    (hL : (∑ i, f i) = 18) (hS : (∑ i, f i ^ 2) = 298) : False := by
  classical
  have hex : ∃ i, 17 ≤ f i := by
    by_contra h
    push Not at h
    have hu := empty_sum_sq_le_mul f 16 (fun i => by have := h i; omega)
    omega
  obtain ⟨i, hi⟩ := hex
  have hsingle : f i ^ 2 ≤ 298 := by
    rw [← hS]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j => f j ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have himax : f i ≤ 17 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show 18 ≤ f i by omega) 2
    norm_num at hp
    omega
  have hieq : f i = 17 := by omega
  have hr := empty_square_remainder f i
  rw [hL, hS, hieq] at hr
  norm_num at hr
#print axioms Paper7FeatureEmpty.empty_square_gap_eighteen

/-- This interval deliberately includes more residual cases than are needed. -/
theorem empty_square_gap_twenty {α : Type*} [Fintype α] (f : α → ℕ)
    (hL : (∑ i, f i) ≤ 20) (hlo : 304 ≤ ∑ i, f i ^ 2)
    (hhi : (∑ i, f i ^ 2) < 324) : False := by
  classical
  have hex : ∃ i, 15 ≤ f i := by
    by_contra h
    push Not at h
    have hu := empty_sum_sq_le_mul f 14 (fun i => by have := h i; omega)
    omega
  obtain ⟨i, hi⟩ := hex
  have hsingle : f i ^ 2 ≤ ∑ j, f j ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j => f j ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have himax : f i ≤ 17 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show 18 ≤ f i by omega) 2
    norm_num at hp
    omega
  have hr := empty_square_remainder f i
  have hrem : (∑ j, f j) - f i ≤ 20 - f i := Nat.sub_le_sub_right hL _
  have hp := Nat.pow_le_pow_left hrem 2
  have hb : (∑ j, f j ^ 2) ≤ f i ^ 2 + (20 - f i) ^ 2 := by omega
  have hicases : f i = 15 ∨ f i = 16 ∨ f i = 17 := by omega
  rcases hicases with hi15 | hi16 | hi17
  · rw [hi15] at hb
    norm_num at hb
    omega
  · rw [hi16] at hb
    norm_num at hb
    omega
  · rw [hi17] at hb
    norm_num at hb
    omega
#print axioms Paper7FeatureEmpty.empty_square_gap_twenty

/-- Below the fourth-moment contribution of a single value 5, the frozen
Perron entry is 3 or 4. Its larger entries are zero by AdmissibleBase itself. -/
theorem empty_even_feature_shape (b : ℕ) (s : SpectralCounts)
    (he : Even b) (hs : AdmissibleBase b 42 s) (hm : m4 b s < 600) :
    (∃ u : ℕ, u ≤ 2 ∧ s2 b s = ((9 + 4 * u : ℕ) : ℤ) ∧
      m4 b s = ((72 + 12 * u : ℕ) : ℤ)) ∨
    (∃ u v : ℕ, u ≤ 2 ∧ v ≤ 2 ∧
      s2 b s = ((16 + 4 * u + 9 * v : ℕ) : ℤ) ∧
      m4 b s = ((240 + 12 * u + 72 * v : ℕ) : ℤ)) := by
  classical
  obtain ⟨ρ, hρ, hpeak, habove, _⟩ := hs.1
  have hnonneg (i : Fin 8) : 0 ≤ ((s.1 i).val : ℤ) * (value i : ℤ) ^ 2 *
      ((value i : ℤ) ^ 2 - 1) := by
    have hv : (2 : ℤ) ≤ value i := by
      exact_mod_cast (show 2 ≤ value i by unfold value; omega)
    have hv2 : (1 : ℤ) ≤ (value i : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((value i : ℤ) - 2)]
    exact mul_nonneg (by positivity) (by omega)
  have hterm : (value ρ : ℤ) ^ 2 * ((value ρ : ℤ) ^ 2 - 1) ≤ m4 b s := by
    have ht := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 8)))
      (f := fun i => ((s.1 i).val : ℤ) * (value i : ℤ) ^ 2 *
        ((value i : ℤ) ^ 2 - 1)) (fun i _ => hnonneg i) (Finset.mem_univ ρ)
    simpa [m4, he, hpeak] using ht
  have hρupper : value ρ ≤ 4 := by
    fin_cases ρ <;> norm_num [value] at hterm ⊢ <;> omega
  have hρcases : ρ = (1 : Fin 8) ∨ ρ = (2 : Fin 8) := by
    have hv : ρ.val = 1 ∨ ρ.val = 2 := by unfold value at hρ hρupper; omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hρcases with rfl | rfl
  · have hz (i : Fin 8) (hi : 2 ≤ i.val) : s.1 i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inl ⟨(s.1 0).val, by omega, ?_, ?_⟩
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
  · have hz (i : Fin 8) (hi : 3 ≤ i.val) : s.1 i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inr ⟨(s.1 0).val, (s.1 1).val, by omega, by omega, ?_, ?_⟩
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
#print axioms Paper7FeatureEmpty.empty_even_feature_shape

theorem empty_load_arithmetic_26 (L Q S u v : ℕ)
    (hu : u ≤ 2) (hv : v ≤ 2) (hbudget : L + Q ≤ 16)
    (hsq : S ≤ L ^ 2)
    (hload : 26 + L + Q ≤ 16 + 4 * u + 9 * v + max Q 2)
    (htheta : 52 + 3 * L + S + 2 * Q = 240 + 12 * u + 72 * v) : False := by
  have hL : L ≤ 16 := by omega
  have hLsq := Nat.pow_le_pow_left hL 2
  norm_num at hLsq
  have htop : 240 + 12 * u + 72 * v ≤ 356 := by omega
  have hv1 : v ≤ 1 := by omega
  have hmax : max Q 2 ≤ Q + 2 := max_le (by omega) (by omega)
  have hL9 : L ≤ 9 := by omega
  have hL9sq := Nat.pow_le_pow_left hL9 2
  norm_num at hL9sq
  omega
#print axioms Paper7FeatureEmpty.empty_load_arithmetic_26

theorem empty_load_arithmetic_22 {α : Type*} [Fintype α] (f : α → ℕ)
    (Q u v : ℕ) (hu : u ≤ 2) (hv : v ≤ 2)
    (hbudget : (∑ i, f i) + Q ≤ 20)
    (hload : 22 + (∑ i, f i) + Q ≤ 16 + 4 * u + 9 * v + max Q 2)
    (htheta : 44 + 3 * (∑ i, f i) + (∑ i, f i ^ 2) + 2 * Q =
      240 + 12 * u + 72 * v) : False := by
  classical
  let L := ∑ i, f i
  let S := ∑ i, f i ^ 2
  change L + Q ≤ 20 at hbudget
  change 22 + L + Q ≤ 16 + 4 * u + 9 * v + max Q 2 at hload
  change 44 + 3 * L + S + 2 * Q = 240 + 12 * u + 72 * v at htheta
  have hsq : S ≤ L ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)
  have hmax : max Q 2 ≤ Q + 2 := max_le (by omega) (by omega)
  interval_cases v
  · have hL : L ≤ 4 := by omega
    have hp := Nat.pow_le_pow_left hL 2
    norm_num at hp
    omega
  · have hL : L ≤ 13 := by omega
    have hp := Nat.pow_le_pow_left hL 2
    norm_num at hp
    omega
  · interval_cases u
    · have hL : L ≤ 14 := by omega
      have hp := Nat.pow_le_pow_left hL 2
      norm_num at hp
      omega
    · have hL18 : 18 ≤ L := by
        by_contra h
        have hp := Nat.pow_le_pow_left (show L ≤ 17 by omega) 2
        norm_num at hp
        omega
      have hLeq : L = 18 := by omega
      have hQeq : Q = 0 := by
        by_cases hQ : Q ≤ 2
        · rw [max_eq_right hQ] at hload
          omega
        · rw [max_eq_left (show 2 ≤ Q by omega)] at hload
          omega
      have hSeq : S = 298 := by omega
      exact empty_square_gap_eighteen f hLeq hSeq
    · have hL18 : 18 ≤ L := by
        by_contra h
        have hp := Nat.pow_le_pow_left (show L ≤ 17 by omega) 2
        norm_num at hp
        omega
      have hL20 : L ≤ 20 := by omega
      have hlo : 304 ≤ S := by omega
      have hhi : S < 324 := by omega
      exact empty_square_gap_twenty f hL20 hlo hhi
#print axioms Paper7FeatureEmpty.empty_load_arithmetic_22

/-- The cycle-filter parameter stays false throughout this proof. -/
theorem unfiltered_dreach_empty_cases (b : ℕ) (hb : b = 22 ∨ b = 26) :
    ¬ DReachable true false b 42 b 0 0 0 := by
  classical
  intro h
  rcases h with ⟨_, s, hs, he, wr, Qr, tr, hw, _, hr, ht, _, hload⟩
  change reachD2 b wr Qr tr at hr
  obtain ⟨x, hxw, hxQ, hxt⟩ :=
    (Paper7Pruning.reachD2_iff b wr Qr tr (Paper7Pruning.reachD2_storage hr)).mp hr
  have hb4 : b ≠ 4 := by omega
  have hwx : weight x ≤ 42 - b := by simpa only [zero_add, hxw] using hw
  have htheta : theta x = m4 b s := by
    simpa only [Nat.cast_zero, zero_add, targetTheta, he, ite_true, hb4, ite_false, sub_zero, hxt]
      using ht
  have hloadx : ((b + weight x : ℕ) : ℤ) ≤ s2 b s + max (qSum x : ℤ) 2 := by
    simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_max, Nat.cast_ofNat,
      zero_add, add_zero, hxw, hxQ] using hload rfl
  have hwload : emptyLoad x + qSum x ≤ 42 - b := by
    simpa only [empty_weight_eq] using hwx
  have hL20 : emptyLoad x ≤ 20 := by omega
  have hsq := empty_square_le x
  have hLsq := Nat.pow_le_pow_left hL20 2
  norm_num at hLsq
  have hnatbound : 2 * b + 3 * emptyLoad x + emptySquareLoad x + 2 * qSum x < 600 := by
    omega
  have hm : m4 b s < 600 := by
    rw [← htheta, empty_theta_eq]
    exact_mod_cast hnatbound
  rcases empty_even_feature_shape b s he hs.1 hm with
    ⟨u, hu, hs2, _⟩ | ⟨u, v, hu, hv, hs2, hm4⟩
  · have hloadNat : b + emptyLoad x + qSum x ≤ 9 + 4 * u + max (qSum x) 2 := by
      rw [empty_weight_eq, hs2] at hloadx
      simp only [← Nat.add_assoc] at hloadx
      exact_mod_cast hloadx
    have hmax : max (qSum x) 2 ≤ qSum x + 2 := max_le (by omega) (by omega)
    omega
  · have hloadNat : b + emptyLoad x + qSum x ≤
        16 + 4 * u + 9 * v + max (qSum x) 2 := by
      rw [empty_weight_eq, hs2] at hloadx
      simp only [← Nat.add_assoc] at hloadx
      exact_mod_cast hloadx
    have hthetaNat : 2 * b + 3 * emptyLoad x + emptySquareLoad x + 2 * qSum x =
        240 + 12 * u + 72 * v := by
      exact_mod_cast (empty_theta_eq x).symm.trans (htheta.trans hm4)
    rcases hb with hb22 | hb26
    · have hw22 : emptyLoad x + qSum x ≤ 20 := by omega
      have hl22 : 22 + emptyLoad x + qSum x ≤
          16 + 4 * u + 9 * v + max (qSum x) 2 := by omega
      have ht22 : 44 + 3 * emptyLoad x + emptySquareLoad x + 2 * qSum x =
          240 + 12 * u + 72 * v := by omega
      exact empty_load_arithmetic_22 (α := Fin b)
        (fun i : Fin b => x.1 i + x.2 i) (qSum x) u v hu hv hw22 hl22 ht22
    · have hw26 : emptyLoad x + qSum x ≤ 16 := by omega
      have hl26 : 26 + emptyLoad x + qSum x ≤
          16 + 4 * u + 9 * v + max (qSum x) 2 := by omega
      have ht26 : 52 + 3 * emptyLoad x + emptySquareLoad x + 2 * qSum x =
          240 + 12 * u + 72 * v := by omega
      exact empty_load_arithmetic_26 (emptyLoad x) (qSum x) (emptySquareLoad x)
        u v hu hv hw26 hsq hl26 ht26
#print axioms Paper7FeatureEmpty.unfiltered_dreach_empty_cases

theorem unfiltered_dreach_empty_22 : ¬ DReachable true false 22 42 22 0 0 0 :=
  unfiltered_dreach_empty_cases 22 (Or.inl rfl)
#print axioms Paper7FeatureEmpty.unfiltered_dreach_empty_22

theorem unfiltered_dreach_empty_26 : ¬ DReachable true false 26 42 26 0 0 0 :=
  unfiltered_dreach_empty_cases 26 (Or.inr rfl)
#print axioms Paper7FeatureEmpty.unfiltered_dreach_empty_26

theorem unfiltered_dreach_empty (b : ℕ) (hb : b ∈ ({22, 26} : Finset ℕ)) :
    ¬ DReachable true false b 42 b 0 0 0 := by
  apply unfiltered_dreach_empty_cases b
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
#print axioms Paper7FeatureEmpty.unfiltered_dreach_empty

end Paper7FeatureEmpty
