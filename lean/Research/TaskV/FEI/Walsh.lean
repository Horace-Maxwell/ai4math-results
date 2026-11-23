import Research.TaskV.FEI.Challenge

namespace Fei
open Finset

private theorem character_comm {n : ℕ} (s x : Cube n) : character s x = character x s := by
  unfold character
  simp only [Finset.prod_ite_mem, Finset.prod_const]
  rw [Finset.inter_comm]

private theorem orthogonal {n : ℕ} (a b : Cube n) :
    (∑ x : Cube n, character a x * character b x) = if a = b then (2 : ℝ)^n else 0 := by
  classical
  let sign (s : Cube n) (i : Fin n) : ℝ := if i ∈ s then -1 else 1
  have h := Finset.prod_one_add (f := fun i => sign a i * sign b i) (univ : Finset (Fin n))
  simp only [powerset_univ] at h
  change (∑ x : Cube n, (∏ i ∈ x, sign a i) * ∏ i ∈ x, sign b i) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← h]
  split_ifs with hab
  · subst b
    have e (i : Fin n) : 1 + sign a i * sign a i = 2 := by
      by_cases hi : i ∈ a <;> norm_num [sign, hi]
    simp [e]
  · have neq : ¬ (∀ i, i ∈ a ↔ i ∈ b) := fun he => hab (Finset.ext he)
    push Not at neq
    obtain ⟨i, hi⟩ := neq
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all [sign]

private theorem inversion {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    (∑ s : Cube n, coeff f s * character s x) = value f x := by
  classical
  let N := (2 : ℝ)^n
  have hN : N ≠ 0 := pow_ne_zero _ (by norm_num)
  have h (s : Cube n) :
      coeff f s * character s x =
        (∑ y : Cube n, value f y * (character y s * character x s)) / N := by
    simp only [coeff, N, div_mul_eq_mul_div, Finset.sum_mul]
    apply congrArg (· / (2:ℝ)^n)
    apply Finset.sum_congr rfl
    intro y _
    rw [character_comm s y, character_comm s x]
    ring
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orthogonal]
  simp [N, mul_ite, hN]

theorem parseval {n : ℕ} (f : Cube n → Bool) :
    ∑ s ∈ support f, mass f s = 1 := by
  classical
  have h (s : Cube n) : mass f s =
      (∑ x : Cube n, value f x * (coeff f s * character s x)) / (2:ℝ)^n := by
    change coeff f s ^ 2 = _
    calc
      _ = ((∑ x : Cube n, value f x * character s x) / (2:ℝ)^n) * coeff f s := by rw [sq]; rfl
      _ = _ := by
        rw [div_mul_eq_mul_div, Finset.sum_mul]
        apply congrArg (· / (2:ℝ)^n)
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hs : (∑ s ∈ support f, mass f s) = ∑ s : Cube n, mass f s := by
    unfold support
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hc : coeff f s = 0 <;> simp [hc, mass]
  rw [hs]
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inversion]
  have sqv (x : Cube n) : value f x * value f x = 1 := by
    cases hx : f x <;> norm_num [value, hx]
  simp [sqv, Cube]

private theorem signed_face {n : ℕ} (R w : Cube n) :
    (∑ T ∈ R.powerset, (-1:ℝ)^T.card * character w T) =
      if R ⊆ w then (2:ℝ)^R.card else 0 := by
  classical
  let sign (i : Fin n) : ℝ := if i ∈ w then -1 else 1
  have h := Finset.prod_one_add (f := fun i => (-1 : ℝ) * sign i) R
  have eq (T : Cube n) : (-1 : ℝ)^T.card * character w T = ∏ i ∈ T, (-1 : ℝ) * sign i := by
    rw [Finset.prod_mul_distrib]
    simp [character, sign]
  simp_rw [eq]
  rw [← h]
  split_ifs with hsub
  · calc
      _ = ∏ _i ∈ R, (2:ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        norm_num [sign, hsub hi]
      _ = _ := by simp
  · obtain ⟨i, hR, hw⟩ := Finset.not_subset.mp hsub
    apply Finset.prod_eq_zero hR
    norm_num [sign, hw]

private theorem face_sum {n : ℕ} (f : Cube n → Bool) (R : Cube n) :
    (∑ T ∈ R.powerset, (-1:ℝ)^T.card * value f T) =
      (2:ℝ)^R.card * (∑ w ∈ support f, if R ⊆ w then coeff f w else 0) := by
  classical
  have h (T : Cube n) :
      (-1:ℝ)^T.card * value f T =
        ∑ w : Cube n, coeff f w * ((-1:ℝ)^T.card * character w T) := by
    rw [← inversion f T, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, signed_face]
  unfold support
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : R ⊆ w <;> by_cases hc : coeff f w = 0 <;> simp [hr,hc,mul_comm]

theorem tail_integral {n : ℕ} (f : Cube n → Bool) (R : Cube n) :
    ∃ z : ℤ, (2:ℝ)^R.card * (∑ w ∈ support f, if R ⊆ w then coeff f w else 0) =
      (if R = ∅ then (1:ℝ) else 2) * (z : ℝ) := by
  classical
  rw [← face_sum]
  by_cases hr : R = ∅
  · subst R
    refine ⟨if f ∅ then -1 else 1, ?_⟩
    cases h : f ∅ <;> simp [value,h]
  · let b (T : Cube n) : ℤ := if f T then 1 else 0
    refine ⟨-∑ T ∈ R.powerset, (-1:ℤ)^T.card * b T, ?_⟩
    have hv (T : Cube n) : value f T = 1 - 2*(b T : ℝ) := by
      cases hx : f T <;> norm_num [value,b,hx]
    have hz : (∑ T ∈ R.powerset, (-1:ℝ)^T.card) = 0 := by
      exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hr)
    have hh (T : Cube n) : (-1:ℝ)^T.card * value f T =
        (-1:ℝ)^T.card - 2*((-1:ℝ)^T.card * (b T : ℝ)) := by rw [hv]; ring
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, hz, ← Finset.mul_sum]
    simp [hr]

end Fei
