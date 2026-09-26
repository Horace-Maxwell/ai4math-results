import Mathlib
import Research.ICGGeneralPath

/-!
# Theorem 5: the sign-matrix inequality `‖T_a(p) Y T_b(q)ᵀ‖₁ ≤ d_a(p) d_b(q)`

Formalisation of §3–§5 of `work/round3/icg-q3/q3-proof.md`:

* `hcell_le` (Lemma 3): the cell function `h(A,B) = P|A-B| + μ|B+PA| - (P-μ)|B| - P(1+μ)|A|`
  satisfies `h ≤ 2μ max(0, |B| - P|A|)` for `0 ≤ μ ≤ 1`, `μ ≤ P`.
* `local_ineq`, `local_ineq_strict` (Lemma 4): for `q ≥ 3`, `P ≥ 4`, `3/5 ≤ μ ≤ 1`,
  `y ∈ {±1}^{b+1}`, `ζ ∈ [-1,1]^{b+1}`, with `F = ‖T_b(q) ·‖₁`:
  `P F(y-ζ) + μ F(ζ+Py) - (P-μ) F(ζ) ≤ P(1+μ) d_b(q)`, strictly unless `y` alternates.
* `thm5_le`, `thm5_eq`, `L1mat_sgnv` (Theorem 5): for real `p ≥ 5`, `q ≥ 3` and every sign
  matrix `Y`, `‖T_a(p) Y T_b(q)ᵀ‖₁ ≤ d_a(p) d_b(q)`, with equality only for `Y = ±s sᵀ`
  (and equality there), where `d_m(x) = ‖T_m(x) s‖₁`.
-/

noncomputable section

namespace ICGGeneral

open Finset

/-! ### Lemma 3: the cell function -/

/-- The cell function `h(A,B)`. -/
def hcell (P μ A B : ℝ) : ℝ := P * |A - B| + μ * |B + P * A| - (P - μ) * |B| - P * (1 + μ) * |A|

lemma hcell_neg (P μ A B : ℝ) : hcell P μ (-A) (-B) = hcell P μ A B := by
  unfold hcell
  rw [show -A - -B = -(A - B) by ring, show -B + P * -A = -(B + P * A) by ring,
    abs_neg, abs_neg, abs_neg, abs_neg]

lemma hcell_le_of_nonneg {P μ A B : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hPμ : μ ≤ P) (hA : 0 ≤ A) :
    hcell P μ A B ≤ 2 * μ * max 0 (|B| - P * |A|) := by
  have hP : 0 ≤ P := le_trans hμ0 hPμ
  have hPA : 0 ≤ P * A := mul_nonneg hP hA
  unfold hcell
  rw [abs_of_nonneg hA]
  rcases le_or_gt 0 B with hB | hB
  · rw [abs_of_nonneg hB, abs_of_nonneg (by linarith : 0 ≤ B + P * A)]
    have hm1 : μ * (B - P * A) ≤ μ * max 0 (B - P * A) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hμ0
    have hm0 : 0 ≤ μ * max 0 (B - P * A) := mul_nonneg hμ0 (le_max_left _ _)
    rcases le_or_gt B A with hBA | hBA
    · rw [abs_of_nonneg (by linarith : 0 ≤ A - B)]
      nlinarith [mul_nonneg (sub_nonneg.2 hPμ) hB]
    · rw [abs_of_neg (by linarith : A - B < 0)]
      nlinarith [mul_nonneg hPA (sub_nonneg.2 hμ1)]
  · rw [abs_of_neg hB, abs_of_nonneg (by linarith : 0 ≤ A - B)]
    have hm1 : μ * (-B - P * A) ≤ μ * max 0 (-B - P * A) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hμ0
    have hm0 : 0 ≤ μ * max 0 (-B - P * A) := mul_nonneg hμ0 (le_max_left _ _)
    rcases le_or_gt 0 (B + P * A) with hBPA | hBPA
    · rw [abs_of_nonneg hBPA]
      nlinarith
    · rw [abs_of_neg hBPA]
      nlinarith

/-- **Lemma 3.** -/
theorem hcell_le {P μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hPμ : μ ≤ P) (A B : ℝ) :
    hcell P μ A B ≤ 2 * μ * max 0 (|B| - P * |A|) := by
  rcases le_or_gt 0 A with hA | hA
  · exact hcell_le_of_nonneg hμ0 hμ1 hPμ hA
  · rw [← hcell_neg]
    have := hcell_le_of_nonneg (B := -B) hμ0 hμ1 hPμ (by linarith : 0 ≤ -A)
    rwa [abs_neg, abs_neg] at this

lemma hcell_nonpos {P μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hPμ : μ ≤ P) {A B : ℝ}
    (h : |B| ≤ P * |A|) : hcell P μ A B ≤ 0 := by
  have := hcell_le hμ0 hμ1 hPμ A B
  rw [max_eq_left (by linarith)] at this
  linarith

lemma sum_hcell (P μ : ℝ) (s : Finset ℕ) (A B : ℕ → ℝ) :
    ∑ j ∈ s, hcell P μ (A j) (B j) = P * ∑ j ∈ s, |A j - B j| + μ * ∑ j ∈ s, |B j + P * A j|
      - (P - μ) * ∑ j ∈ s, |B j| - P * (1 + μ) * ∑ j ∈ s, |A j| := by
  rw [eq_comm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold hcell
  ring

/-! ### Path increments and linearity -/

/-- Path increment `τ_j(w) = Z_j(w) - Z_{j+1}(w)`. -/
def tau (x : ℝ) (m : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ := Zp x m w j - Zp x m w (j + 1)

lemma L1_tau {x : ℝ} (hx : 0 < x) (m : ℕ) (w : ℕ → ℝ) :
    L1 x m w = x ^ m * (|Zp x m w 0| + ∑ j ∈ range m, |tau x m w j|) :=
  L1_path hx m w

lemma tau_eq {x : ℝ} (hx : x ≠ 0) {m : ℕ} (w : ℕ → ℝ) {j : ℕ} (hj : j < m) :
    tau x m w j = (x - 1) / x * (w j - Zp x m w (j + 1)) := by
  unfold tau
  rw [Zp_rec hx m w hj]
  field_simp
  ring

lemma Zp_add_mul (x : ℝ) (m : ℕ) (β : ℝ) (w w' : ℕ → ℝ) (k : ℕ) :
    Zp x m (fun i => w i + β * w' i) k = Zp x m w k + β * Zp x m w' k := by
  unfold Zp Wp
  rw [mul_div_assoc', ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Zp_sub (x : ℝ) (m : ℕ) (w w' : ℕ → ℝ) (k : ℕ) :
    Zp x m (fun i => w i - w' i) k = Zp x m w k - Zp x m w' k := by
  unfold Zp Wp
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tau_add_mul (x : ℝ) (m : ℕ) (β : ℝ) (w w' : ℕ → ℝ) (j : ℕ) :
    tau x m (fun i => w i + β * w' i) j = tau x m w j + β * tau x m w' j := by
  unfold tau
  rw [Zp_add_mul, Zp_add_mul]
  ring

lemma tau_sub (x : ℝ) (m : ℕ) (w w' : ℕ → ℝ) (j : ℕ) :
    tau x m (fun i => w i - w' i) j = tau x m w j - tau x m w' j := by
  unfold tau
  rw [Zp_sub, Zp_sub]
  ring

lemma Zp_sum (x : ℝ) (m : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (k : ℕ) :
    Zp x m (fun i => ∑ l ∈ s, c l * f l i) k = ∑ l ∈ s, c l * Zp x m (f l) k := by
  unfold Zp Wp
  have h : ∑ j ∈ Ico k (m + 1), phiX x (m - j) * ∑ l ∈ s, c l * f l j =
      ∑ l ∈ s, c l * ∑ j ∈ Ico k (m + 1), phiX x (m - j) * f l j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-! ### Lemma 4: the local q-side inequality -/

/-- The combination `P F(y-ζ) + μ F(ζ+Py) - (P-μ) F(ζ)` in terms of cell functions. -/
lemma L1_combo {q : ℝ} (hq : 0 < q) (b : ℕ) (P μ : ℝ) (y ζ : ℕ → ℝ) :
    P * L1 q b (fun i => y i - ζ i) + μ * L1 q b (fun i => ζ i + P * y i) - (P - μ) * L1 q b ζ =
      q ^ b * (hcell P μ (Zp q b y 0) (Zp q b ζ 0) +
        ∑ j ∈ range b, hcell P μ (tau q b y j) (tau q b ζ j)) + P * (1 + μ) * L1 q b y := by
  rw [L1_tau hq b (fun i => y i - ζ i), L1_tau hq b (fun i => ζ i + P * y i), L1_tau hq b ζ,
    L1_tau hq b y, Zp_sub, Zp_add_mul, sum_hcell]
  simp only [tau_sub, tau_add_mul]
  unfold hcell
  ring

lemma numeric_core {r P μ ν t : ℝ} (hr : 2 / 3 ≤ r) (hP : 4 ≤ P) (hμ0 : 3 / 5 ≤ μ) (hμ1 : μ ≤ 1)
    (hν : 2 * r - 1 ≤ ν) (ht0 : 2 * r - 1 ≤ t) (ht1 : t ≤ 1) :
    2 * μ * r < P * (μ * (r * (1 - t)) + (1 + μ) * ν * t) := by
  have ht : 0 ≤ t := by linarith
  have h1t : 0 ≤ 1 - t := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hν0 : 0 ≤ ν := by linarith
  have h1 : 3 / 5 * (r * (1 - t)) ≤ μ * (r * (1 - t)) :=
    mul_le_mul_of_nonneg_right hμ0 (mul_nonneg hr0 h1t)
  have h2a : (2 * r - 1) * t ≤ ν * t := mul_le_mul_of_nonneg_right hν ht
  have h2b : 8 / 5 * (ν * t) ≤ (1 + μ) * (ν * t) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hν0 ht)
  have h3a : 0 ≤ t * (13 * r - 8) := mul_nonneg ht (by linarith)
  have h3 : 3 / 5 * r ≤ μ * (r * (1 - t)) + (1 + μ) * ν * t := by nlinarith
  have h4 : 4 * (μ * (r * (1 - t)) + (1 + μ) * ν * t) ≤
      P * (μ * (r * (1 - t)) + (1 + μ) * ν * t) :=
    mul_le_mul_of_nonneg_right hP (by linarith)
  have h5 : μ * r ≤ r := by nlinarith
  nlinarith

/-- The index-`0` cell is non-positive. -/
lemma local_term0 {q P μ : ℝ} (hq : 3 ≤ q) (hP : 4 ≤ P) (hμ0 : 3 / 5 ≤ μ) (hμ1 : μ ≤ 1)
    {b : ℕ} {y ζ : ℕ → ℝ} (hy : IsSign b y) (hζ : ∀ i ≤ b, |ζ i| ≤ 1) :
    hcell P μ (Zp q b y 0) (Zp q b ζ 0) ≤ 0 := by
  have hq0 : 0 < q := by linarith
  apply hcell_nonpos (by linarith) hμ1 (by linarith)
  have hB := Zp_abs_le (x := q) (by linarith) hζ 0 (Nat.zero_le _)
  have hA : (q - 2) / q ≤ |Zp q b y 0| := by
    rw [Zp_abs_eq (by linarith) hy (Nat.zero_le _)]
    exact Zp_sign (by linarith) hy 0 (Nat.zero_le _)
  have h13 : 1 / 3 ≤ (q - 2) / q := by rw [le_div_iff₀ hq0]; linarith
  nlinarith

/-- The index-`j` cells (`j < b`). -/
lemma local_term {q P μ : ℝ} (hq : 3 ≤ q) (hP : 4 ≤ P) (hμ0 : 3 / 5 ≤ μ) (hμ1 : μ ≤ 1)
    {b : ℕ} {y ζ : ℕ → ℝ} (hy : IsSign b y) (hζ : ∀ i ≤ b, |ζ i| ≤ 1) {j : ℕ} (hj : j < b) :
    (y j ≠ y (j + 1) → hcell P μ (tau q b y j) (tau q b ζ j) ≤ 0) ∧
    (y j = y (j + 1) → hcell P μ (tau q b y j) (tau q b ζ j) <
        P * (1 + μ) * (2 * nu q (j + 1) * |Zp q b y (j + 1)|)) := by
  have hq0 : 0 < q := by linarith
  have hj1 : j + 1 ≤ b := hj
  set r := (q - 1) / q with hr
  have hr0 : 0 < r := div_pos (by linarith) hq0
  have hr23 : 2 / 3 ≤ r := by rw [hr, le_div_iff₀ hq0]; linarith
  have hlow : (q - 2) / q = 2 * r - 1 := by rw [hr]; field_simp; ring
  have hPμ : μ ≤ P := by linarith
  have hμ0' : 0 ≤ μ := by linarith
  have hB : |tau q b ζ j| ≤ 2 * r := by
    rw [tau_eq hq0.ne' ζ hj, ← hr, abs_mul, abs_of_pos hr0]
    have h1 := hζ j hj.le
    have h2 := Zp_abs_le (x := q) (by linarith) hζ (j + 1) hj1
    have h3 : |ζ j - Zp q b ζ (j + 1)| ≤ 2 := by
      calc |ζ j - Zp q b ζ (j + 1)| ≤ |ζ j| + |Zp q b ζ (j + 1)| := abs_sub _ _
        _ ≤ 2 := by linarith
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, |Zp q b y (j + 1)| = t := ⟨_, rfl⟩
  have ht1 : t ≤ 1 := by
    rw [← ht]
    exact Zp_abs_le (x := q) (by linarith) (isSign_abs_le hy) (j + 1) hj1
  have htlow : 2 * r - 1 ≤ t := by
    rw [← ht, Zp_abs_eq (x := q) (by linarith) hy hj1, ← hlow]
    exact Zp_sign (x := q) (by linarith) hy (j + 1) hj1
  have hZt : Zp q b y (j + 1) = y (j + 1) * t := by
    rw [← ht, Zp_abs_eq (x := q) (by linarith) hy hj1, ← mul_assoc, isSign_sq hy hj1, one_mul]
  have hA : tau q b y j = r * (y j - y (j + 1) * t) := by
    rw [tau_eq hq0.ne' y hj, ← hr, hZt]
  rw [ht]
  constructor
  · intro hne
    have hyj1 : y (j + 1) = -y j := by
      rcases hy j hj.le with a | a <;> rcases hy (j + 1) hj1 with c | c
      · exact absurd (a.trans c.symm) hne
      · rw [a, c]
      · rw [a, c]; norm_num
      · exact absurd (a.trans c.symm) hne
    have hAabs : |tau q b y j| = r * (1 + t) := by
      rw [hA, hyj1, show r * (y j - -y j * t) = r * (1 + t) * y j by ring, abs_mul,
        isSign_abs hy hj.le, mul_one, abs_of_nonneg (mul_nonneg hr0.le (by linarith))]
    apply hcell_nonpos hμ0' hμ1 hPμ
    rw [hAabs]
    nlinarith [mul_nonneg (sub_nonneg.2 hP) hr0.le,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P) hr0.le) (by linarith : (0 : ℝ) ≤ t)]
  · intro heq
    have hAabs : |tau q b y j| = r * (1 - t) := by
      rw [hA, ← heq, show r * (y j - y j * t) = r * (1 - t) * y j by ring, abs_mul,
        isSign_abs hy hj.le, mul_one, abs_of_nonneg (mul_nonneg hr0.le (by linarith))]
    have hν := (nu_bounds (show (2 : ℝ) ≤ q by linarith) (j + 1)).1
    rw [hlow] at hν
    have hcore := numeric_core hr23 hP hμ0 hμ1 hν htlow ht1
    have hcl := hcell_le hμ0' hμ1 hPμ (tau q b y j) (tau q b ζ j)
    rw [hAabs] at hcl
    have hRpos : 0 < P * (1 + μ) * (2 * nu q (j + 1) * t) := by
      have h1 : 0 < nu q (j + 1) := nu_pos (by linarith) _
      have h2 : 0 < t := by linarith
      have h3 : 0 < P := by linarith
      have h4 : 0 < 1 + μ := by linarith
      positivity
    rcases le_or_gt (|tau q b ζ j| - P * (r * (1 - t))) 0 with hm | hm
    · rw [max_eq_left hm] at hcl
      linarith
    · rw [max_eq_right hm.le] at hcl
      nlinarith [mul_le_mul_of_nonneg_left hB hμ0']

/-- The gap in Lemma 4, written as a sum of non-negative cell contributions. -/
lemma local_gap {q P μ : ℝ} (hq : 3 ≤ q) {b : ℕ} {y ζ : ℕ → ℝ} (hy : IsSign b y) :
    P * (1 + μ) * L1 q b sgnv -
      (P * L1 q b (fun i => y i - ζ i) + μ * L1 q b (fun i => ζ i + P * y i) -
        (P - μ) * L1 q b ζ) =
      q ^ b * (∑ j ∈ range b, (P * (1 + μ) *
          (if y j = y (j + 1) then 2 * nu q (j + 1) * |Zp q b y (j + 1)| else 0) -
            hcell P μ (tau q b y j) (tau q b ζ j)) - hcell P μ (Zp q b y 0) (Zp q b ζ 0)) := by
  have hq0 : 0 < q := by linarith
  have hq2 : 2 < q := by linarith
  rw [L1_combo hq0, L1_sign hq2 hy, L1_sgnv hq2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold slack
  ring

/-- **Lemma 4.** -/
theorem local_ineq {q P μ : ℝ} (hq : 3 ≤ q) (hP : 4 ≤ P) (hμ0 : 3 / 5 ≤ μ) (hμ1 : μ ≤ 1)
    {b : ℕ} {y ζ : ℕ → ℝ} (hy : IsSign b y) (hζ : ∀ i ≤ b, |ζ i| ≤ 1) :
    P * L1 q b (fun i => y i - ζ i) + μ * L1 q b (fun i => ζ i + P * y i) - (P - μ) * L1 q b ζ
      ≤ P * (1 + μ) * L1 q b sgnv := by
  have hq0 : 0 < q := by linarith
  have hg := local_gap (P := P) (μ := μ) (ζ := ζ) hq hy
  have h0 := local_term0 hq hP hμ0 hμ1 hy hζ
  have hs : 0 ≤ ∑ j ∈ range b, (P * (1 + μ) *
      (if y j = y (j + 1) then 2 * nu q (j + 1) * |Zp q b y (j + 1)| else 0) -
        hcell P μ (tau q b y j) (tau q b ζ j)) := by
    apply Finset.sum_nonneg
    intro j hj
    rw [Finset.mem_range] at hj
    have ht := local_term hq hP hμ0 hμ1 hy hζ hj
    by_cases hyj : y j = y (j + 1)
    · rw [if_pos hyj]
      linarith [ht.2 hyj]
    · rw [if_neg hyj, mul_zero]
      linarith [ht.1 hyj]
  linarith [mul_nonneg (pow_pos hq0 b).le hs, mul_nonneg (pow_pos hq0 b).le (neg_nonneg.mpr h0)]

/-- **Lemma 4, strict form.** -/
theorem local_ineq_strict {q P μ : ℝ} (hq : 3 ≤ q) (hP : 4 ≤ P) (hμ0 : 3 / 5 ≤ μ) (hμ1 : μ ≤ 1)
    {b : ℕ} {y ζ : ℕ → ℝ} (hy : IsSign b y) (hζ : ∀ i ≤ b, |ζ i| ≤ 1)
    (hna : ∃ j < b, y j = y (j + 1)) :
    P * L1 q b (fun i => y i - ζ i) + μ * L1 q b (fun i => ζ i + P * y i) - (P - μ) * L1 q b ζ
      < P * (1 + μ) * L1 q b sgnv := by
  have hq0 : 0 < q := by linarith
  have hg := local_gap (P := P) (μ := μ) (ζ := ζ) hq hy
  have h0 := local_term0 hq hP hμ0 hμ1 hy hζ
  obtain ⟨j0, hj0, hyj0⟩ := hna
  have hs : 0 < ∑ j ∈ range b, (P * (1 + μ) *
      (if y j = y (j + 1) then 2 * nu q (j + 1) * |Zp q b y (j + 1)| else 0) -
        hcell P μ (tau q b y j) (tau q b ζ j)) := by
    apply Finset.sum_pos'
    · intro j hj
      rw [Finset.mem_range] at hj
      have ht := local_term hq hP hμ0 hμ1 hy hζ hj
      by_cases hyj : y j = y (j + 1)
      · rw [if_pos hyj]
        linarith [ht.2 hyj]
      · rw [if_neg hyj, mul_zero]
        linarith [ht.1 hyj]
    · refine ⟨j0, Finset.mem_range.mpr hj0, ?_⟩
      have ht := local_term hq hP hμ0 hμ1 hy hζ hj0
      rw [if_pos hyj0]
      linarith [ht.2 hyj0]
  linarith [mul_pos (pow_pos hq0 b) hs, mul_nonneg (pow_pos hq0 b).le (neg_nonneg.mpr h0)]

/-! ### Theorem 5 -/

/-- Entry `(u, v)` of `T_a(p) Y T_b(q)ᵀ`. -/
def Mentry (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ i ∈ range (a + 1), ∑ l ∈ range (b + 1), Tent p a u i * Y i l * Tent q b v l

/-- `‖T_a(p) Y T_b(q)ᵀ‖₁` (entrywise). -/
def L1mat (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) : ℝ :=
  ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1), |Mentry p q a b Y u v|

/-- Rows of `Y` pushed along the `p`-path: `ζ_k = Z_k` applied column-wise. -/
def zeta (p : ℝ) (a : ℕ) (Y : ℕ → ℕ → ℝ) (k l : ℕ) : ℝ := Zp p a (fun i => Y i l) k

/-- The per-step quantity `g_k` of the potential argument. -/
def gk (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  L1 q b (fun l => zeta p a Y k l - zeta p a Y (k + 1) l) + nu p k * L1 q b (zeta p a Y k) -
    nu p (k + 1) * L1 q b (zeta p a Y (k + 1))

lemma Mentry_eq (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) :
    Mentry p q a b Y u v = Tv p a (fun i => Tv q b (Y i) v) u := by
  unfold Mentry Tv
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma Zp_col (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (v k : ℕ) :
    Zp p a (fun i => Tv q b (Y i) v) k = Tv q b (zeta p a Y k) v := by
  unfold Tv zeta
  exact Zp_sum p a (range (b + 1)) (fun l => Tent q b v l) (fun l i => Y i l) k

lemma Tv_sub (x : ℝ) (m : ℕ) (w w' : ℕ → ℝ) (u : ℕ) :
    Tv x m (fun i => w i - w' i) u = Tv x m w u - Tv x m w' u := by
  unfold Tv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The `p`-path decomposition of `‖T_a(p) Y T_b(q)ᵀ‖₁`. -/
lemma L1mat_path {p : ℝ} (hp : 0 < p) (q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    L1mat p q a b Y = p ^ a * (L1 q b (zeta p a Y 0) +
      ∑ k ∈ range a, L1 q b (fun l => zeta p a Y k l - zeta p a Y (k + 1) l)) := by
  unfold L1mat
  simp_rw [Mentry_eq]
  rw [Finset.sum_comm]
  have hv : ∀ v, ∑ u ∈ range (a + 1), |Tv p a (fun i => Tv q b (Y i) v) u| =
      p ^ a * (|Tv q b (zeta p a Y 0) v| +
        ∑ k ∈ range a, |Tv q b (fun l => zeta p a Y k l - zeta p a Y (k + 1) l) v|) := by
    intro v
    have h := L1_path hp a (fun i => Tv q b (Y i) v)
    unfold L1 at h
    rw [h, Zp_col]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [Zp_col, Zp_col, Tv_sub]
  simp_rw [hv]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
  unfold L1
  rfl

lemma zeta_rec {p : ℝ} (hp : p ≠ 0) {a : ℕ} (Y : ℕ → ℕ → ℝ) {k : ℕ} (hk : k < a) (l : ℕ) :
    zeta p a Y k l = (zeta p a Y (k + 1) l + (p - 1) * Y k l) / p :=
  Zp_rec hp a _ hk

lemma zeta_last (p : ℝ) (a : ℕ) (Y : ℕ → ℕ → ℝ) (l : ℕ) : zeta p a Y a l = Y a l :=
  Zp_self p a _

lemma zeta_abs_le {p : ℝ} (hp : 1 ≤ p) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) {k : ℕ} (hk : k ≤ a) {l : ℕ} (hl : l ≤ b) :
    |zeta p a Y k l| ≤ 1 :=
  Zp_abs_le hp (fun i hi => by rcases hY i hi l hl with h | h <;> simp [h]) k hk

/-- `p · g_k` is the Lemma-4 combination with `P = p - 1`, `μ = ν_k`. -/
lemma gk_identity {p : ℝ} (hp : 1 ≤ p) (q : ℝ) {a b : ℕ} (Y : ℕ → ℕ → ℝ) {k : ℕ} (hk : k < a) :
    p * gk p q a b Y k =
      (p - 1) * L1 q b (fun l => Y k l - zeta p a Y (k + 1) l) +
        nu p k * L1 q b (fun l => zeta p a Y (k + 1) l + (p - 1) * Y k l) -
        (p - 1 - nu p k) * L1 q b (zeta p a Y (k + 1)) := by
  have hp0 : 0 < p := by linarith
  have h1 : L1 q b (fun l => zeta p a Y k l - zeta p a Y (k + 1) l) =
      (p - 1) / p * L1 q b (fun l => Y k l - zeta p a Y (k + 1) l) := by
    rw [← abs_of_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ p - 1) hp0.le), ← L1_smul]
    congr 1
    funext l
    rw [zeta_rec hp0.ne' Y hk l]
    field_simp
    ring
  have h2 : L1 q b (zeta p a Y k) =
      1 / p * L1 q b (fun l => zeta p a Y (k + 1) l + (p - 1) * Y k l) := by
    rw [← abs_of_nonneg (div_nonneg zero_le_one hp0.le), ← L1_smul]
    congr 1
    funext l
    rw [zeta_rec hp0.ne' Y hk l]
    field_simp
  unfold gk
  rw [h1, h2, nu_succ]
  field_simp

lemma L1mat_eq_gk {p : ℝ} (hp : 0 < p) (q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    L1mat p q a b Y = p ^ a * (∑ k ∈ range a, gk p q a b Y k + nu p a * L1 q b (Y a)) := by
  rw [L1mat_path hp]
  congr 1
  have hlast : L1 q b (zeta p a Y a) = L1 q b (Y a) := by
    congr 1
    funext l
    exact zeta_last p a Y l
  have htel := Finset.sum_range_sub' (fun k => nu p k * L1 q b (zeta p a Y k)) a
  have hg : ∀ k ∈ range a, gk p q a b Y k =
      L1 q b (fun l => zeta p a Y k l - zeta p a Y (k + 1) l) +
        (nu p k * L1 q b (zeta p a Y k) - nu p (k + 1) * L1 q b (zeta p a Y (k + 1))) := by
    intro k _
    unfold gk
    ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib, htel, nu_zero, hlast]
  ring

lemma nu_range {p : ℝ} (hp : 5 ≤ p) (k : ℕ) : 3 / 5 ≤ nu p k ∧ nu p k ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hν := nu_bounds (show (2 : ℝ) ≤ p by linarith) k
  exact ⟨le_trans (by rw [le_div_iff₀ hp0]; linarith) hν.1, hν.2⟩

lemma cc_mul_eq {p : ℝ} (hp : 0 < p) (k : ℕ) (D : ℝ) :
    p * (cc p k * D) = (p - 1) * (1 + nu p k) * D := by
  unfold cc
  field_simp

lemma gk_le {p q : ℝ} (hp : 5 ≤ p) (hq : 3 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) {k : ℕ} (hk : k < a) :
    gk p q a b Y k ≤ cc p k * L1 q b sgnv := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hμ0, hμ1⟩ := nu_range hp k
  have hloc := local_ineq (P := p - 1) (μ := nu p k) (ζ := zeta p a Y (k + 1)) hq (by linarith)
    hμ0 hμ1 (hY k hk.le) (fun l hl => zeta_abs_le (by linarith) hY (Nat.succ_le_of_lt hk) hl)
  have h1 : p * gk p q a b Y k ≤ p * (cc p k * L1 q b sgnv) := by
    rw [gk_identity (show (1 : ℝ) ≤ p by linarith) q Y hk, cc_mul_eq hp0]
    exact hloc
  exact le_of_mul_le_mul_left h1 hp0

lemma gk_lt {p q : ℝ} (hp : 5 ≤ p) (hq : 3 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) {k : ℕ} (hk : k < a) (hna : ∃ j < b, Y k j = Y k (j + 1)) :
    gk p q a b Y k < cc p k * L1 q b sgnv := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hμ0, hμ1⟩ := nu_range hp k
  have hloc := local_ineq_strict (P := p - 1) (μ := nu p k) (ζ := zeta p a Y (k + 1)) hq
    (by linarith) hμ0 hμ1 (hY k hk.le)
    (fun l hl => zeta_abs_le (by linarith) hY (Nat.succ_le_of_lt hk) hl) hna
  have h1 : p * gk p q a b Y k < p * (cc p k * L1 q b sgnv) := by
    rw [gk_identity (show (1 : ℝ) ≤ p by linarith) q Y hk, cc_mul_eq hp0]
    exact hloc
  exact lt_of_mul_lt_mul_left h1 hp0.le

/-- **Theorem 5 (inequality).** For real `p ≥ 5`, `q ≥ 3` and every sign matrix `Y`,
`‖T_a(p) Y T_b(q)ᵀ‖₁ ≤ d_a(p) d_b(q)`. -/
theorem thm5_le {p q : ℝ} (hp : 5 ≤ p) (hq : 3 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) : L1mat p q a b Y ≤ L1 p a sgnv * L1 q b sgnv := by
  have hp0 : 0 < p := by linarith
  have hp2 : 2 < p := by linarith
  have hq2 : 2 < q := by linarith
  rw [L1mat_eq_gk hp0, L1_sgnv hp2]
  have hsum : ∑ k ∈ range a, gk p q a b Y k ≤ ∑ k ∈ range a, cc p k * L1 q b sgnv :=
    Finset.sum_le_sum (fun k hk => gk_le hp hq hY (Finset.mem_range.mp hk))
  rw [← Finset.sum_mul] at hsum
  have hlast : L1 q b (Y a) ≤ L1 q b sgnv := L1_le_sgnv hq2 (hY a le_rfl)
  have h2 : nu p a * L1 q b (Y a) ≤ nu p a * L1 q b sgnv :=
    mul_le_mul_of_nonneg_left hlast (nu_pos hp2 a).le
  have h3 : ∑ k ∈ range a, gk p q a b Y k + nu p a * L1 q b (Y a) ≤
      (∑ k ∈ range a, cc p k + nu p a) * L1 q b sgnv := by
    rw [add_mul]
    linarith
  calc p ^ a * (∑ k ∈ range a, gk p q a b Y k + nu p a * L1 q b (Y a))
      ≤ p ^ a * ((∑ k ∈ range a, cc p k + nu p a) * L1 q b sgnv) :=
        mul_le_mul_of_nonneg_left h3 (pow_pos hp0 a).le
    _ = p ^ a * (∑ k ∈ range a, cc p k + nu p a) * L1 q b sgnv := by ring

lemma Mentry_prod (p q : ℝ) (a b : ℕ) {Y : ℕ → ℕ → ℝ} {e f : ℕ → ℝ}
    (hY : ∀ i ≤ a, ∀ l ≤ b, Y i l = e i * f l) (u v : ℕ) :
    Mentry p q a b Y u v = Tv p a e u * Tv q b f v := by
  unfold Mentry Tv
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hi hl
  rw [hY i (by omega) l (by omega)]
  ring

lemma L1mat_prod (p q : ℝ) (a b : ℕ) {Y : ℕ → ℕ → ℝ} {e f : ℕ → ℝ}
    (hY : ∀ i ≤ a, ∀ l ≤ b, Y i l = e i * f l) :
    L1mat p q a b Y = L1 p a e * L1 q b f := by
  unfold L1mat L1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Mentry_prod p q a b hY, abs_mul]

/-- **Theorem 5 (value at `s sᵀ`).** -/
theorem L1mat_sgnv (p q : ℝ) (a b : ℕ) :
    L1mat p q a b (fun i l => sgnv i * sgnv l) = L1 p a sgnv * L1 q b sgnv :=
  L1mat_prod p q a b (fun _ _ _ _ => rfl)

/-- **Theorem 5 (equality case).** Equality forces `Y = ± s sᵀ`. -/
theorem thm5_eq {p q : ℝ} (hp : 5 ≤ p) (hq : 3 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) (h : L1mat p q a b Y = L1 p a sgnv * L1 q b sgnv) :
    (∀ i ≤ a, ∀ l ≤ b, Y i l = sgnv i * sgnv l) ∨
      (∀ i ≤ a, ∀ l ≤ b, Y i l = -(sgnv i * sgnv l)) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 2 < p := by linarith
  have hq2 : 2 < q := by linarith
  have hDpos : 0 < L1 q b sgnv := L1_sgnv_pos hq2 b
  have hrows : ∀ i ≤ a, (∀ l ≤ b, Y i l = sgnv l) ∨ (∀ l ≤ b, Y i l = -sgnv l) := by
    have h' := h
    rw [L1mat_eq_gk hp0, L1_sgnv hp2] at h'
    have hpa := pow_pos hp0 a
    have hn1 : ∀ k ∈ range a, 0 ≤ cc p k * L1 q b sgnv - gk p q a b Y k :=
      fun k hk => sub_nonneg.2 (gk_le hp hq hY (Finset.mem_range.mp hk))
    have hn2 : 0 ≤ nu p a * (L1 q b sgnv - L1 q b (Y a)) :=
      mul_nonneg (nu_pos hp2 a).le (sub_nonneg.2 (L1_le_sgnv hq2 (hY a le_rfl)))
    have hS := Finset.sum_nonneg hn1
    have e1 : ∑ k ∈ range a, gk p q a b Y k + nu p a * L1 q b (Y a) =
        (∑ k ∈ range a, cc p k + nu p a) * L1 q b sgnv := by
      rw [mul_assoc] at h'
      exact mul_left_cancel₀ hpa.ne' h'
    have hzero : ∑ k ∈ range a, (cc p k * L1 q b sgnv - gk p q a b Y k) +
        nu p a * (L1 q b sgnv - L1 q b (Y a)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [add_mul] at e1
      linarith
    have hsum0 : ∑ k ∈ range a, (cc p k * L1 q b sgnv - gk p q a b Y k) = 0 := by linarith
    have hlast0 : nu p a * (L1 q b sgnv - L1 q b (Y a)) = 0 := by linarith
    intro i hi
    rcases lt_or_eq_of_le hi with hia | hia
    · apply alternating_eq (hY i hi)
      intro j hj hyj
      have hgi := (Finset.sum_eq_zero_iff_of_nonneg hn1).mp hsum0 i (Finset.mem_range.mpr hia)
      have hlt := gk_lt hp hq hY hia ⟨j, hj, hyj⟩
      linarith
    · rw [hia]
      apply L1_eq_sgnv hq2 (hY a le_rfl)
      rcases mul_eq_zero.mp hlast0 with h0 | h0
      · exact absurd h0 (nu_pos hp2 a).ne'
      · linarith
  have hYε : ∀ i ≤ a, ∀ l ≤ b, Y i l = Y i 0 * sgnv l := by
    intro i hi l hl
    rcases hrows i hi with hr | hr
    · rw [hr l hl, hr 0 (Nat.zero_le _), sgnv_zero, one_mul]
    · rw [hr l hl, hr 0 (Nat.zero_le _), sgnv_zero]
      ring
  have hεs : IsSign a (fun i => Y i 0) := fun i hi => hY i hi 0 (Nat.zero_le _)
  have hL : L1 p a (fun i => Y i 0) = L1 p a sgnv := by
    rw [L1mat_prod p q a b (e := fun i => Y i 0) (f := sgnv) hYε] at h
    exact mul_right_cancel₀ hDpos.ne' h
  rcases L1_eq_sgnv hp2 hεs hL with he | he
  · left
    intro i hi l hl
    have he' : Y i 0 = sgnv i := he i hi
    rw [hYε i hi l hl, he']
  · right
    intro i hi l hl
    have he' : Y i 0 = -sgnv i := he i hi
    rw [hYε i hi l hl, he']
    ring

end ICGGeneral

#print axioms ICGGeneral.thm5_le
#print axioms ICGGeneral.thm5_eq
#print axioms ICGGeneral.L1mat_sgnv
