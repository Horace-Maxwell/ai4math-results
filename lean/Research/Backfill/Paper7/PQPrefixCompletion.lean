import Research.Backfill.Paper7.DReachRecurrence
import Research.Backfill.Paper7.Lemma53

/-! Source-only coordinate splitting. No DP correctness or positive pendant
assumption is used. The suffix may be empty and the assigned prefix may be empty. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def suffixPQ {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) : PQ (b-d) :=
  (fun i => x.1 ⟨d+i.val, by omega⟩, fun i => x.2 ⟨d+i.val, by omega⟩)
#print axioms Paper7Pruning.suffixPQ

def completePQ {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) (z : PQ (b-d)) : PQ b :=
  (fun i => if h : i.val < d then x.1 i else z.1 ⟨i.val-d, by omega⟩,
   fun i => if h : i.val < d then x.2 i else z.2 ⟨i.val-d, by omega⟩)
#print axioms Paper7Pruning.completePQ

theorem sum_suffix {A : Type*} [AddCommMonoid A] (b d : ℕ) (hd : d ≤ b)
    (f : Fin b → A) :
    (∑ i ∈ univ.filter (fun i : Fin b => ¬ i.val < d), f i) =
      ∑ j : Fin (b-d), f ⟨d+j.val, by omega⟩ := by
  classical
  refine Finset.sum_bij
    (fun i hi => (⟨i.val-d, by have := (mem_filter.mp hi).2; omega⟩ : Fin (b-d)))
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have hv := congrArg Fin.val hij
    change i.val - d = j.val - d at hv
    apply Fin.ext
    omega
  · intro j _
    refine ⟨⟨d+j.val, by omega⟩, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_univ _, by simp⟩
    · apply Fin.ext
      simp
  · intro i hi
    apply congrArg f
    apply Fin.ext
    have := (mem_filter.mp hi).2
    dsimp
    omega
#print axioms Paper7Pruning.sum_suffix

theorem sum_prefix_suffix {A : Type*} [AddCommMonoid A] (b d : ℕ) (hd : d ≤ b)
    (f : Fin b → A) :
    (∑ i, f i) = (∑ i ∈ univ.filter (fun i : Fin b => i.val < d), f i) +
      ∑ j : Fin (b-d), f ⟨d+j.val, by omega⟩ := by
  rw [← sum_filter_add_sum_filter_not univ (fun i : Fin b => i.val < d) f,
    sum_suffix b d hd f]
#print axioms Paper7Pruning.sum_prefix_suffix

theorem pSum_prefix_suffix {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) :
    pSum x = pSum («prefix» d x) + pSum (suffixPQ d hd x) := by
  simpa only [pSum, «prefix», suffixPQ, Finset.sum_filter] using
    sum_prefix_suffix b d hd x.1
#print axioms Paper7Pruning.pSum_prefix_suffix

theorem qSum_prefix_suffix {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) :
    qSum x = qSum («prefix» d x) + qSum (suffixPQ d hd x) := by
  simpa only [qSum, «prefix», suffixPQ, Finset.sum_filter] using
    sum_prefix_suffix b d hd x.2
#print axioms Paper7Pruning.qSum_prefix_suffix

theorem weight_prefix_suffix {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) :
    weight x = weight («prefix» d x) + weight (suffixPQ d hd x) := by
  unfold weight
  rw [pSum_prefix_suffix d hd x, qSum_prefix_suffix d hd x]
  omega
#print axioms Paper7Pruning.weight_prefix_suffix

theorem theta_prefix_suffix {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) :
    theta x = prefixTheta d x + theta (suffixPQ d hd x) := by
  exact sum_prefix_suffix b d hd (fun i => thetaV (x.1 i) (x.2 i))
#print axioms Paper7Pruning.theta_prefix_suffix

theorem prefixTheta_nonneg {b : ℕ} (d : ℕ) (x : PQ b) : 0 ≤ prefixTheta d x := by
  exact sum_nonneg (fun i _ => thetaV_nonneg (x.1 i) (x.2 i))
#print axioms Paper7Pruning.prefixTheta_nonneg

theorem prefixTheta_prefix {b : ℕ} (d : ℕ) (x : PQ b) :
    prefixTheta d («prefix» d x) = prefixTheta d x := by
  apply Finset.sum_congr rfl
  intro i hi
  have hit := (mem_filter.mp hi).2
  simp only [«prefix», ite_eq_left hit]
#print axioms Paper7Pruning.prefixTheta_prefix

theorem prefixTheta_congr {b : ℕ} (d : ℕ) (x y : PQ b)
    (h : «prefix» d x = «prefix» d y) : prefixTheta d x = prefixTheta d y := by
  rw [← prefixTheta_prefix d x, h, prefixTheta_prefix]
#print axioms Paper7Pruning.prefixTheta_congr

theorem prefix_completePQ {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) (z : PQ (b-d)) :
    «prefix» d (completePQ d hd x z) = «prefix» d x := by
  apply Prod.ext <;> funext i <;>
    by_cases hi : i.val < d <;> simp [«prefix», completePQ, hi]
#print axioms Paper7Pruning.prefix_completePQ

theorem suffix_completePQ {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) (z : PQ (b-d)) :
    suffixPQ d hd (completePQ d hd x z) = z := by
  apply Prod.ext <;> funext i <;> simp [suffixPQ, completePQ]
#print axioms Paper7Pruning.suffix_completePQ

theorem completePQ_suffix {b : ℕ} (d : ℕ) (hd : d ≤ b) (x : PQ b) :
    completePQ d hd x (suffixPQ d hd x) = x := by
  apply Prod.ext <;> funext i
  · by_cases hi : i.val < d
    · simp [completePQ, hi]
    · simp only [completePQ, hi, suffixPQ]
      apply congrArg x.1
      apply Fin.ext
      dsimp
      omega
  · by_cases hi : i.val < d
    · simp [completePQ, hi]
    · simp only [completePQ, hi, suffixPQ]
      apply congrArg x.2
      apply Fin.ext
      dsimp
      omega
#print axioms Paper7Pruning.completePQ_suffix

theorem theta_lt_storage_bound (b N : ℕ) (x : PQ b)
    (hbudget : b + weight x ≤ N) (hN : N ≤ 49) : theta x < 3072 := by
  have hb : b ≤ 49 := by omega
  have hw : weight x ≤ 49 := by omega
  have hbound := (BackfillPaper7.WindowProof.sum_thetaV_bounds univ x.1 x.2).2
  have hsum : (∑ k : Fin b, ((x.1 k : ℤ) + 2 * x.2 k)) = (weight x : ℤ) := by
    simp only [weight, pSum, qSum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sum, sum_add_distrib, mul_sum]
  simp only [Finset.card_univ, Fintype.card_fin] at hbound
  rw [hsum] at hbound
  change theta x ≤ gW (weight x) + 2 * ((b : ℤ)-1) at hbound
  have hg := BackfillPaper7.WindowProof.gW_mono
    (Int.natCast_nonneg (weight x)) (show (weight x : ℤ) ≤ 49 by exact_mod_cast hw)
  have hbZ : (b : ℤ) ≤ 49 := by exact_mod_cast hb
  have hg49 : gW (49 : ℤ) = 2550 := by norm_num [gW]
  rw [hg49] at hg
  linarith
#print axioms Paper7Pruning.theta_lt_storage_bound

theorem prefixTheta_lt_storage_bound (b N d : ℕ) (hd : d ≤ b) (x : PQ b)
    (hbN : b ≤ N) (hweight : weight («prefix» d x) ≤ N-b) (hN : N ≤ 49) :
    prefixTheta d x < 3072 := by
  have h := theta_lt_storage_bound b N («prefix» d x) (by omega) hN
  have hs := theta_prefix_suffix d hd («prefix» d x)
  rw [prefixTheta_prefix] at hs
  have hz := theta_nonneg (suffixPQ d hd («prefix» d x))
  linarith
#print axioms Paper7Pruning.prefixTheta_lt_storage_bound

end Paper7Pruning
