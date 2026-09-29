import Research.Backfill.Paper3.Proof.L67.W

/-!
# Lemma 7: the sign of `D(q)`

With `μ(i, j) = C(d-1,i) C(d-1,j) q^{ij}`, `4 D(q) = Δ`, the sum over `i, i', j, j' < d` of
`[μ(i,j) μ(i',j') - μ(i,j') μ(i',j)] (q^i - q^{i'}) (q^j - q^{j'})` (expand; the second half is
minus the first after exchanging `j`, `j'`). Each term is a nonnegative weight times
`(q^{ij+i'j'} - q^{ij'+i'j}) (q^i - q^{i'}) (q^j - q^{j'})`, which has the sign of `log q` or
vanishes; the term `i = j = 0`, `i' = j' = 1` does not vanish.
-/

set_option autoImplicit false

namespace P3L67

open Finset Polynomial BackfillPaper3.Challenge

/-- A fourfold sum of products factors. -/
theorem sum4_mul (s : Finset ℕ) (f g : ℕ → ℕ → ℝ) :
    ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s, f i j * g i' j' =
      (∑ i ∈ s, ∑ j ∈ s, f i j) * (∑ i' ∈ s, ∑ j' ∈ s, g i' j') := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_mul_sum]

/-- The identity `Δ = 4 (W₀₀ W₁₁ - W₁₀ W₀₁)` for arbitrary weights `μ` and values `p`. -/
theorem four_D_eq (s : Finset ℕ) (μ : ℕ → ℕ → ℝ) (p : ℕ → ℝ) :
    ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s,
        (μ i j * μ i' j' - μ i j' * μ i' j) * ((p i - p i') * (p j - p j')) =
      4 * ((∑ i ∈ s, ∑ j ∈ s, μ i j) * (∑ i ∈ s, ∑ j ∈ s, μ i j * p i * p j) -
        (∑ i ∈ s, ∑ j ∈ s, μ i j * p j) * (∑ i ∈ s, ∑ j ∈ s, μ i j * p i)) := by
  -- the first half
  have hS : ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s, μ i j * μ i' j' * ((p i - p i') * (p j - p j')) =
      2 * ((∑ i ∈ s, ∑ j ∈ s, μ i j) * (∑ i ∈ s, ∑ j ∈ s, μ i j * p i * p j) -
        (∑ i ∈ s, ∑ j ∈ s, μ i j * p j) * (∑ i ∈ s, ∑ j ∈ s, μ i j * p i)) := by
    have e : ∀ i i' j j', μ i j * μ i' j' * ((p i - p i') * (p j - p j')) =
        (μ i j * p i * p j) * μ i' j' - (μ i j * p i) * (μ i' j' * p j') -
          (μ i j * p j) * (μ i' j' * p i') + μ i j * (μ i' j' * p i' * p j') := by
      intro i i' j j'
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum4_mul, sum4_mul, sum4_mul, sum4_mul]
    ring
  -- the second half is minus the first
  have hT : ∀ i i', ∑ j ∈ s, ∑ j' ∈ s, μ i j' * μ i' j * ((p i - p i') * (p j - p j')) =
      -∑ j ∈ s, ∑ j' ∈ s, μ i j * μ i' j' * ((p i - p i') * (p j - p j')) := by
    intro i i'
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsplit : ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s,
        (μ i j * μ i' j' - μ i j' * μ i' j) * ((p i - p i') * (p j - p j')) =
      ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s, μ i j * μ i' j' * ((p i - p i') * (p j - p j')) -
        ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s, μ i j' * μ i' j * ((p i - p i') * (p j - p j')) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  rw [hsplit, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => hT i i']
  simp only [Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [hS]
  ring

theorem nat_cross (a a' b b' : ℕ) (ha : a ≤ a') (hb : b ≤ b') :
    a * b' + a' * b ≤ a * b + a' * b' := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith [Nat.zero_le (x * y)]

/-- For `q ≥ 1` every term of `Δ` (without its binomial weight) is nonnegative. -/
theorem term_nonneg {q : ℝ} (hq : 1 ≤ q) (i i' j j' : ℕ) :
    0 ≤ (q ^ (i * j + i' * j') - q ^ (i * j' + i' * j)) *
      ((q ^ i - q ^ i') * (q ^ j - q ^ j')) := by
  rcases le_total i i' with hi | hi <;> rcases le_total j j' with hj | hj
  · have e := nat_cross i i' j j' hi hj
    exact mul_nonneg (sub_nonneg.2 (pow_le_pow_right₀ hq e))
      (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_right₀ hq hi))
        (sub_nonpos.2 (pow_le_pow_right₀ hq hj)))
  · have e := nat_cross i i' j' j hi hj
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_right₀ hq e))
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (pow_le_pow_right₀ hq hi))
        (sub_nonneg.2 (pow_le_pow_right₀ hq hj)))
  · have e : i * j + i' * j' ≤ i * j' + i' * j := by
      have := nat_cross i' i j j' hi hj
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_right₀ hq e))
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (pow_le_pow_right₀ hq hi))
        (sub_nonpos.2 (pow_le_pow_right₀ hq hj)))
  · have e : i * j' + i' * j ≤ i * j + i' * j' := by
      have := nat_cross i' i j' j hi hj
      linarith
    exact mul_nonneg (sub_nonneg.2 (pow_le_pow_right₀ hq e))
      (mul_nonneg (sub_nonneg.2 (pow_le_pow_right₀ hq hi))
        (sub_nonneg.2 (pow_le_pow_right₀ hq hj)))

/-- For `0 ≤ q ≤ 1` every term of `Δ` (without its binomial weight) is nonpositive. -/
theorem term_nonpos {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1) (i i' j j' : ℕ) :
    (q ^ (i * j + i' * j') - q ^ (i * j' + i' * j)) *
      ((q ^ i - q ^ i') * (q ^ j - q ^ j')) ≤ 0 := by
  rcases le_total i i' with hi | hi <;> rcases le_total j j' with hj | hj
  · have e := nat_cross i i' j j' hi hj
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq e))
      (mul_nonneg (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq hi))
        (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq hj)))
  · have e := nat_cross i i' j' j hi hj
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq e))
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq hi))
        (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq hj)))
  · have e : i * j + i' * j' ≤ i * j' + i' * j := by
      have := nat_cross i' i j j' hi hj
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq e))
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq hi))
        (sub_nonneg.2 (pow_le_pow_of_le_one hq0 hq hj)))
  · have e : i * j' + i' * j ≤ i * j + i' * j' := by
      have := nat_cross i' i j' j hi hj
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq e))
      (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq hi))
        (sub_nonpos.2 (pow_le_pow_of_le_one hq0 hq hj)))

/-- A fourfold sum of nonnegative terms with one positive term is positive. -/
theorem sum4_pos (s : Finset ℕ) (T : ℕ → ℕ → ℕ → ℕ → ℝ) (h : ∀ i i' j j', 0 ≤ T i i' j j')
    (a b c e : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (he : e ∈ s) (hpos : 0 < T a b c e) :
    0 < ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ s, ∑ j' ∈ s, T i i' j j' := by
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun j' _ => h i i' j j') ⟨a, ha, ?_⟩
  refine Finset.sum_pos' (fun i' _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun j' _ => h a i' j j') ⟨b, hb, ?_⟩
  refine Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun j' _ => h a b j j') ⟨c, hc, ?_⟩
  exact Finset.sum_pos' (fun j' _ => h a b c j') ⟨e, he, hpos⟩

/-- `4 D(q) = Δ(q)`. -/
theorem four_evalR_D (d : ℕ) (q : ℝ) :
    4 * evalR (Dpoly d) q =
      ∑ i ∈ range d, ∑ i' ∈ range d, ∑ j ∈ range d, ∑ j' ∈ range d,
        (((d - 1).choose i : ℝ) * ((d - 1).choose i' : ℝ) * ((d - 1).choose j : ℝ) *
          ((d - 1).choose j' : ℝ)) *
        ((q ^ (i * j + i' * j') - q ^ (i * j' + i' * j)) *
          ((q ^ i - q ^ i') * (q ^ j - q ^ j'))) := by
  set μ : ℕ → ℕ → ℝ := fun i j => ((d - 1).choose i : ℝ) * ((d - 1).choose j : ℝ) * q ^ (i * j)
    with hμ
  have h00 : evalR (Wpoly d 0 0) q = ∑ i ∈ range d, ∑ j ∈ range d, μ i j := by
    rw [evalR_Wpoly]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [hμ]
  have h11 : evalR (Wpoly d 1 1) q = ∑ i ∈ range d, ∑ j ∈ range d, μ i j * q ^ i * q ^ j := by
    rw [evalR_Wpoly]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hμ]
    ring
  have h10 : evalR (Wpoly d 1 0) q = ∑ i ∈ range d, ∑ j ∈ range d, μ i j * q ^ j := by
    rw [evalR_Wpoly]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hμ]
    ring
  have h01 : evalR (Wpoly d 0 1) q = ∑ i ∈ range d, ∑ j ∈ range d, μ i j * q ^ i := by
    rw [evalR_Wpoly]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hμ]
    ring
  have hD : evalR (Dpoly d) q =
      evalR (Wpoly d 0 0) q * evalR (Wpoly d 1 1) q -
        evalR (Wpoly d 1 0) q * evalR (Wpoly d 0 1) q := by
    rw [← wSymm d]
    simp only [evalR, Dpoly, map_sub, map_mul, map_pow]
    ring
  have key := four_D_eq (range d) μ (fun i => q ^ i)
  rw [hD, h00, h11, h10, h01, ← key]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [hμ]
  ring

/-- **Lemma 7.** -/
theorem lemma7 (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) :
    (1 < q → 0 < evalR (Dpoly d) q) ∧ (q < 1 → evalR (Dpoly d) q < 0) := by
  have h0 : 0 ∈ range d := Finset.mem_range.2 (by omega)
  have h1 : 1 ∈ range d := Finset.mem_range.2 (by omega)
  have hc1 : (0 : ℝ) < ((d - 1).choose 1 : ℝ) := by
    rw [Nat.choose_one_right]
    exact_mod_cast (show 0 < d - 1 by omega)
  have hw : ∀ i i' j j' : ℕ, (0 : ℝ) ≤ ((d - 1).choose i : ℝ) * ((d - 1).choose i' : ℝ) *
      ((d - 1).choose j : ℝ) * ((d - 1).choose j' : ℝ) := fun _ _ _ _ => by positivity
  have hstrict : ∀ x : ℝ, ((d - 1).choose 0 : ℝ) * ((d - 1).choose 1 : ℝ) *
      ((d - 1).choose 0 : ℝ) * ((d - 1).choose 1 : ℝ) *
        ((q ^ (0 * 0 + 1 * 1) - q ^ (0 * 1 + 1 * 0)) * ((q ^ 0 - q ^ 1) * (q ^ 0 - q ^ 1))) =
      ((d - 1).choose 1 : ℝ) ^ 2 * ((q - 1) * (q - 1) ^ 2) + 0 * x := by
    intro x
    simp only [Nat.choose_zero_right, Nat.cast_one]
    ring
  constructor
  · intro hq1
    have hpos := sum4_pos (range d) (fun i i' j j' =>
      (((d - 1).choose i : ℝ) * ((d - 1).choose i' : ℝ) * ((d - 1).choose j : ℝ) *
          ((d - 1).choose j' : ℝ)) *
        ((q ^ (i * j + i' * j') - q ^ (i * j' + i' * j)) * ((q ^ i - q ^ i') * (q ^ j - q ^ j'))))
      (fun i i' j j' => mul_nonneg (hw i i' j j') (term_nonneg hq1.le i i' j j'))
      0 1 0 1 h0 h1 h0 h1 (by
        rw [hstrict 0]
        have : 0 < q - 1 := by linarith
        positivity)
    rw [← four_evalR_D] at hpos
    linarith
  · intro hq1
    have hpos := sum4_pos (range d) (fun i i' j j' =>
      -((((d - 1).choose i : ℝ) * ((d - 1).choose i' : ℝ) * ((d - 1).choose j : ℝ) *
          ((d - 1).choose j' : ℝ)) *
        ((q ^ (i * j + i' * j') - q ^ (i * j' + i' * j)) * ((q ^ i - q ^ i') * (q ^ j - q ^ j')))))
      (fun i i' j j' => neg_nonneg.2
        (mul_nonpos_of_nonneg_of_nonpos (hw i i' j j') (term_nonpos hq.le hq1.le i i' j j')))
      0 1 0 1 h0 h1 h0 h1 (by
        rw [neg_pos, hstrict 0]
        have h1q : 0 < 1 - q := by linarith
        have : (q - 1) * (q - 1) ^ 2 = -((1 - q) * (1 - q) ^ 2) := by ring
        rw [this]
        have : 0 < ((d - 1).choose 1 : ℝ) ^ 2 * ((1 - q) * (1 - q) ^ 2) := by positivity
        linarith)
    simp only [Finset.sum_neg_distrib] at hpos
    rw [← four_evalR_D] at hpos
    linarith

end P3L67
