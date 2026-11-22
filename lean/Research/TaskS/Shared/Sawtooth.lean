import Mathlib

noncomputable section
open scoped BigOperators
open Finset

namespace TaskS.Shared

theorem grid_sum (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (∑ k : Fin n, Int.fract (a + (k : ℝ) / n)) =
      Int.fract (n * a) + ((n : ℝ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => Int.fract (a + (k : ℝ) / n))]
  have hf : (∑ k ∈ range n, (⌊a + (k : ℝ)/n⌋ : ℝ)) = ⌊n*a⌋ := by
    exact_mod_cast Int.sum_floor_add_div a n
  have hs : (∑ k ∈ range n, (k : ℝ)) * 2 = (n : ℝ) * ((n : ℝ)-1) := by
    have h := sum_range_id_mul_two n
    have h' : (∑ k ∈ range n, (k : ℝ)) * 2 = (n : ℝ) * ((n-1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using congrArg (fun k : ℕ => (k : ℝ)) h
    rwa [Nat.cast_sub hn, Nat.cast_one] at h'
  simp only [Int.fract, sum_sub_distrib, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul, ← sum_div, hf]
  field_simp
  nlinarith

private def event (q : ℕ) (x : ℝ) (k : Fin q) : ℝ := -(x + (k : ℝ)) / q

private theorem grid_deviation (q : ℕ) (hq : 0 < q) (x t : ℝ) :
    (∑ k : Fin q, (Int.fract (t - event q x k) - 1/2)) =
      Int.fract (x + (q : ℝ)*t) - 1/2 := by
  have he (k : Fin q) : t - event q x k = (t+x/q) + (k : ℝ)/q := by
    unfold event
    ring
  simp only [he, sum_sub_distrib, grid_sum q hq, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  rw [show (q : ℝ)*(t+x/q) = x+q*t by field_simp; ring]
  ring

private def dev (p q : ℕ) (x y : ℝ) : ℝ :=
  ∑ k : Fin p, (Int.fract (y + (q : ℝ) * event p x k) - 1/2)

private theorem dev_diag (q : ℕ) (hq : 0 < q) (x : ℝ) :
    dev q q x x = -(q : ℝ)/2 := by
  have hz (k : Fin q) : x + (q : ℝ) * event q x k = -(k : ℝ) := by
    unfold event
    have hn : (q : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hz' (k : Fin q) : Int.fract (-(k : ℝ)) = 0 := Int.fract_neg_eq_zero.mpr (Int.fract_natCast _)
  simp [dev, hz, hz']
  ring

private theorem dev_pair (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (x y : ℝ) :
    dev p q x y + dev q p y x ≤ 0 := by
  unfold dev
  simp_rw [← grid_deviation q hq y, ← grid_deviation p hp x]
  rw [sum_comm (f := fun (l : Fin q) (k : Fin p) =>
    Int.fract (event q y l - event p x k) - 1/2)]
  rw [← sum_add_distrib]
  apply sum_nonpos
  intro k _
  rw [← sum_add_distrib]
  apply sum_nonpos
  intro l _
  let z := event p x k - event q y l
  have h : event q y l - event p x k = -z := by dsimp [z]; ring
  change Int.fract z - 1 / 2 + (Int.fract (event q y l - event p x k) - 1 / 2) ≤ 0
  rw [h]
  by_cases hz : Int.fract z = 0
  · rw [hz, Int.fract_neg_eq_zero.mpr hz]
    norm_num
  · rw [Int.fract_neg hz]
    ring_nf
    exact le_rfl


theorem sawtooth_weighted {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x : ι → ℝ) :
    ∃ t : ℝ, (∑ i, c i * Int.fract (x i + (q i : ℝ)*t)) ≤
      ((∑ i, c i) - (∑ i, (q i : ℝ)*(c i)^2) / (∑ i, (q i : ℝ)*c i))/2 := by
  classical
  let W := ∑ i, (q i : ℝ)*c i
  let V := ∑ i, (q i : ℝ)*(c i)^2
  let D := fun i j => c i * c j * dev (q i) (q j) (x i) (x j)
  have hw : 0 < W := sum_pos (fun i _ => mul_pos (by exact_mod_cast hq i) (hc i)) univ_nonempty
  have hpair (i j : ι) :
      D i j + D j i ≤ if i = j then -((q i : ℝ)*(c i)^2) else 0 := by
    dsimp only [D]
    split_ifs with h
    · subst j
      rw [dev_diag _ (hq i)]
      exact le_of_eq (by ring)
    · have h' := mul_nonpos_of_nonneg_of_nonpos (mul_pos (hc i) (hc j)).le
          (dev_pair _ _ (hq i) (hq j) (x i) (x j))
      linarith only [h']
  have hsum : 2 * (∑ i, ∑ j, D i j) ≤ -V := calc
    _ = (∑ i, ∑ j, D i j) + ∑ j, ∑ i, D i j := by rw [sum_comm (f := fun j i => D i j)]; ring
    _ = ∑ i, ∑ j, (D i j + D j i) := by simp only [sum_add_distrib]
    _ ≤ ∑ i, ∑ j, if i = j then -((q i : ℝ)*(c i)^2) else 0 :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hpair i j
    _ = -V := by simp [V]
  by_contra! ha
  have hbad (t : ℝ) : -(V / W)/2 < ∑ j, c j * (Int.fract (x j + (q j : ℝ)*t) - 1/2) := by
    specialize ha t
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul]
    dsimp only [V, W]
    linarith
  have he (i : ι) : (q i : ℝ) * c i * (-(V/W)/2) < ∑ j, D i j := by
    have : Nonempty (Fin (q i)) := Fin.pos_iff_nonempty.mp (hq i)
    calc
      _ = ∑ _k : Fin (q i), c i * (-(V/W)/2) := by simp; ring
      _ < ∑ k : Fin (q i), c i * ∑ j, c j *
          (Int.fract (x j + (q j : ℝ) * event (q i) (x i) k) - 1/2) :=
        sum_lt_sum_of_nonempty univ_nonempty fun k _ => mul_lt_mul_of_pos_left (hbad _) (hc i)
      _ = ∑ j, D i j := by
        simp only [D, dev, mul_sum, ← mul_assoc]
        rw [sum_comm]
  have hbadSum := sum_lt_sum_of_nonempty univ_nonempty (fun i _ => he i)
  rw [← sum_mul] at hbadSum
  change W * (-(V / W)/2) < _ at hbadSum
  rw [show W * (-(V/W)/2) = -V/2 by field_simp] at hbadSum
  linarith

theorem sawtooth_unweighted {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (x : ι → ℝ) :
    ∃ t : ℝ, (∑ i, Int.fract (x i + (q i : ℝ)*t)) ≤ ((Fintype.card ι : ℝ)-1)/2 := by
  have h : 0 < ∑ i, (q i : ℝ) := sum_pos (fun i _ => by exact_mod_cast hq i) univ_nonempty
  simpa [h.ne'] using sawtooth_weighted q hq (fun _ => 1) (fun _ => zero_lt_one) x

end TaskS.Shared
