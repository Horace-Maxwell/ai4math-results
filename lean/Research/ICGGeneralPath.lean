import Mathlib

/-!
# The weighted Ramanujan matrix `T_m(x)`: path identity and scalar potential

Formalisation of §1–§2 of `work/round3/icg-q3/q3-proof.md` (Lemmas 1 and 2).

For a real parameter `x` and `m : ℕ`, `T_m(x)` is the `(m+1) × (m+1)` matrix with entries
`Tent x m u j = φ(x^{m-u}) · c_{x^{m-j}}(x^u)` (Jiang–Yang (2.2)–(2.4)), where `φ(x^0) = 1`,
`φ(x^e) = x^{e-1}(x-1)` and the prime-power Ramanujan sum is `c_{x^k}(x^u) = 1` (`k = 0`),
`φ(x^k)` (`1 ≤ k ≤ u`), `-x^u` (`k = u+1`), `0` (`k > u+1`).

Vectors are functions `ℕ → ℝ` (only the coordinates `0..m` matter) and sums run over
`Finset.range (m+1)`.  `L1 x m w = ‖T_m(x) w‖₁`.

* `L1_path` (Lemma 1): `‖T_m(x) w‖₁ = x^m (|Z_0| + ∑_{k<m} |Z_k - Z_{k+1}|)` where
  `Z_k = x^{-(m-k)} ∑_{j ≥ k} φ(x^{m-j}) w_j` (`Z_k` is `z_{k-1}` of the note).
* `L1_sign` (Lemma 2): for `y ∈ {±1}^{m+1}` and `x > 2`,
  `‖T_m y‖₁ = x^m (∑_{k<m} c_k + ν_m - ∑_{k<m, y_k = y_{k+1}} 2 ν_{k+1} |Z_{k+1}|)`,
  hence `‖T_m y‖₁ ≤ d_m(x) := ‖T_m s‖₁` with equality iff `y = ±s`, `s = (1,-1,1,…)`.
-/

noncomputable section

namespace ICGGeneral

open Finset

/-- `φ(x^e)`: `1` for `e = 0`, else `x^(e-1) (x-1)`. -/
def phiX (x : ℝ) (e : ℕ) : ℝ := if e = 0 then 1 else x ^ (e - 1) * (x - 1)

/-- The prime-power Ramanujan sum `c_{x^k}(x^u)`. -/
def ramX (x : ℝ) (k u : ℕ) : ℝ :=
  if k = 0 then 1 else if k ≤ u then phiX x k else if k = u + 1 then -(x ^ u) else 0

/-- Entry `(u, j)` of the weighted Ramanujan matrix `T_m(x)`: `φ(x^{m-u}) c_{x^{m-j}}(x^u)`. -/
def Tent (x : ℝ) (m u j : ℕ) : ℝ := phiX x (m - u) * ramX x (m - j) u

/-- `(T_m(x) w)_u`. -/
def Tv (x : ℝ) (m : ℕ) (w : ℕ → ℝ) (u : ℕ) : ℝ := ∑ j ∈ range (m + 1), Tent x m u j * w j

/-- `‖T_m(x) w‖₁`. -/
def L1 (x : ℝ) (m : ℕ) (w : ℕ → ℝ) : ℝ := ∑ u ∈ range (m + 1), |Tv x m w u|

/-- The alternating vector `s = (1, -1, 1, …)`. -/
def sgnv (i : ℕ) : ℝ := (-1) ^ i

/-- `y` is a sign vector on `0..m`. -/
def IsSign (m : ℕ) (y : ℕ → ℝ) : Prop := ∀ i ≤ m, y i = 1 ∨ y i = -1

/-- Unnormalised path `W_k(w) = ∑_{j=k}^{m} φ(x^{m-j}) w_j`. -/
def Wp (x : ℝ) (m : ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Ico k (m + 1), phiX x (m - j) * w j

/-- Path `Z_k(w) = W_k(w) / x^{m-k}` (`z_{k-1}` in the note). -/
def Zp (x : ℝ) (m : ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ := Wp x m w k / x ^ (m - k)

/-- Potential `ν_k` (`μ_{k-1}` in the note): `ν_0 = 1`, `ν_{k+1} = (x - 1 - ν_k)/x`. -/
def nu (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (x - 1 - nu x k) / x

/-- `c_k = (x-1)(1+ν_k)/x`. -/
def cc (x : ℝ) (k : ℕ) : ℝ := (x - 1) * (1 + nu x k) / x

/-! ### Basic facts -/

@[simp] lemma phiX_zero (x : ℝ) : phiX x 0 = 1 := by simp [phiX]

lemma phiX_succ (x : ℝ) (e : ℕ) : phiX x (e + 1) = x ^ e * (x - 1) := by simp [phiX]

lemma nu_zero (x : ℝ) : nu x 0 = 1 := rfl

lemma nu_succ (x : ℝ) (k : ℕ) : nu x (k + 1) = (x - 1 - nu x k) / x := rfl

lemma sgnv_zero : sgnv 0 = 1 := by simp [sgnv]

lemma sgnv_succ (i : ℕ) : sgnv (i + 1) = -sgnv i := by simp [sgnv, pow_succ]

lemma sgnv_isSign (m : ℕ) : IsSign m sgnv := by
  intro i _
  rcases neg_one_pow_eq_or ℝ i with h | h
  · left; exact h
  · right; exact h

lemma Wp_self (x : ℝ) (m : ℕ) (w : ℕ → ℝ) : Wp x m w m = w m := by
  simp [Wp]

lemma Wp_eq_add (x : ℝ) (m : ℕ) (w : ℕ → ℝ) {k : ℕ} (hk : k ≤ m) :
    Wp x m w k = phiX x (m - k) * w k + Wp x m w (k + 1) := by
  unfold Wp
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

lemma Zp_self (x : ℝ) (m : ℕ) (w : ℕ → ℝ) : Zp x m w m = w m := by
  simp [Zp, Wp_self]

lemma Zp_rec {x : ℝ} (hx : x ≠ 0) (m : ℕ) (w : ℕ → ℝ) {k : ℕ} (hk : k < m) :
    Zp x m w k = (Zp x m w (k + 1) + (x - 1) * w k) / x := by
  unfold Zp
  rw [Wp_eq_add x m w hk.le]
  obtain ⟨d, rfl⟩ : ∃ d, m = k + 1 + d := ⟨m - k - 1, by omega⟩
  rw [show k + 1 + d - k = d + 1 by omega, show k + 1 + d - (k + 1) = d by omega, phiX_succ]
  field_simp
  ring

/-! ### Lemma 1: rows of `T_m(x)` are path increments -/

lemma Tv_row {x : ℝ} (hx : x ≠ 0) (k u : ℕ) (w : ℕ → ℝ) :
    Tv x (k + u + 1) w u =
      x ^ (k + u + 1) * (Zp x (k + u + 1) w (k + 1) - Zp x (k + u + 1) w k) := by
  have hmu : k + u + 1 - u = k + 1 := by omega
  unfold Tv Tent
  rw [hmu, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ k + u + 1 + 1 by omega),
    Finset.sum_range_succ]
  have h0 : ∑ j ∈ range k, phiX x (k + 1) * ramX x (k + u + 1 - j) u * w j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    have : ramX x (k + u + 1 - j) u = 0 := by
      unfold ramX
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [this]
    ring
  have hk : ramX x (k + u + 1 - k) u = -(x ^ u) := by
    unfold ramX
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hI : ∑ j ∈ Ico (k + 1) (k + u + 1 + 1), phiX x (k + 1) * ramX x (k + u + 1 - j) u * w j =
      phiX x (k + 1) * Wp x (k + u + 1) w (k + 1) := by
    unfold Wp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    have : ramX x (k + u + 1 - j) u = phiX x (k + u + 1 - j) := by
      unfold ramX
      by_cases h : k + u + 1 - j = 0
      · rw [if_pos h, h, phiX_zero]
      · rw [if_neg h, if_pos (by omega)]
    rw [this]
    ring
  rw [h0, hk, hI, zero_add]
  unfold Zp
  rw [Wp_eq_add x (k + u + 1) w (show k ≤ k + u + 1 by omega),
    show k + u + 1 - k = u + 1 by omega, show k + u + 1 - (k + 1) = u by omega,
    phiX_succ, phiX_succ]
  field_simp
  ring

lemma Tv_last {x : ℝ} (hx : x ≠ 0) (m : ℕ) (w : ℕ → ℝ) : Tv x m w m = x ^ m * Zp x m w 0 := by
  unfold Tv Tent Zp Wp
  rw [Nat.sub_self, Nat.sub_zero, mul_div_cancel₀ _ (pow_ne_zero m hx), Finset.range_eq_Ico]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [phiX_zero, one_mul]
  congr 1
  unfold ramX
  by_cases h : m - j = 0
  · rw [if_pos h, h, phiX_zero]
  · rw [if_neg h, if_pos (by omega)]

/-- **Lemma 1 (path identity).** -/
theorem L1_path {x : ℝ} (hx : 0 < x) (m : ℕ) (w : ℕ → ℝ) :
    L1 x m w = x ^ m * (|Zp x m w 0| + ∑ k ∈ range m, |Zp x m w k - Zp x m w (k + 1)|) := by
  unfold L1
  rw [Finset.sum_range_succ, Tv_last hx.ne', abs_mul, abs_of_pos (pow_pos hx m)]
  have h : ∑ u ∈ range m, |Tv x m w u| =
      x ^ m * ∑ k ∈ range m, |Zp x m w k - Zp x m w (k + 1)| := by
    rw [Finset.mul_sum]
    conv_lhs => rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨u, rfl⟩ : ∃ u, m = k + u + 1 := ⟨m - k - 1, by omega⟩
    rw [show k + u + 1 - 1 - k = u by omega, Tv_row hx.ne', abs_mul,
      abs_of_pos (pow_pos hx _), abs_sub_comm]
  rw [h]
  ring

/-! ### Linearity -/

lemma Tv_linear (x : ℝ) (m : ℕ) (α β : ℝ) (w w' : ℕ → ℝ) (u : ℕ) :
    Tv x m (fun i => α * w i + β * w' i) u = α * Tv x m w u + β * Tv x m w' u := by
  unfold Tv
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Tv_smul (x : ℝ) (m : ℕ) (α : ℝ) (w : ℕ → ℝ) (u : ℕ) :
    Tv x m (fun i => α * w i) u = α * Tv x m w u := by
  unfold Tv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma L1_smul (x : ℝ) (m : ℕ) (α : ℝ) (w : ℕ → ℝ) :
    L1 x m (fun i => α * w i) = |α| * L1 x m w := by
  unfold L1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Tv_smul, abs_mul]

lemma Zp_linear (x : ℝ) (m : ℕ) (α β : ℝ) (w w' : ℕ → ℝ) (k : ℕ) :
    Zp x m (fun i => α * w i + β * w' i) k = α * Zp x m w k + β * Zp x m w' k := by
  unfold Zp Wp
  rw [mul_div_assoc', mul_div_assoc', ← add_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Tv_congr (x : ℝ) (m : ℕ) {w w' : ℕ → ℝ} (h : ∀ i ≤ m, w i = w' i) (u : ℕ) :
    Tv x m w u = Tv x m w' u := by
  unfold Tv
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [h j (by omega)]

lemma L1_congr (x : ℝ) (m : ℕ) {w w' : ℕ → ℝ} (h : ∀ i ≤ m, w i = w' i) :
    L1 x m w = L1 x m w' := by
  unfold L1
  apply Finset.sum_congr rfl
  intro u _
  rw [Tv_congr x m h]

lemma Zp_congr (x : ℝ) (m : ℕ) {w w' : ℕ → ℝ} (h : ∀ i ≤ m, w i = w' i) (k : ℕ) :
    Zp x m w k = Zp x m w' k := by
  unfold Zp Wp
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [h j (by omega)]

/-- Constant vector: `Z_k(1) = 1`. -/
lemma Zp_one {x : ℝ} (hx : x ≠ 0) (m : ℕ) : ∀ k ≤ m, Zp x m (fun _ => 1) k = 1 := by
  have key : ∀ d k, k + d = m → Zp x m (fun _ => 1) k = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk
      simp only [Nat.add_zero] at hk
      subst hk
      rw [Zp_self]
    | succ d ih =>
      intro k hk
      rw [Zp_rec hx m _ (by omega), ih (k + 1) (by omega)]
      field_simp
      ring
  intro k hk
  exact key (m - k) k (by omega)

/-- Row sums: `T_m(x) 1 = x^m e_m`. -/
lemma Tv_one {x : ℝ} (hx : x ≠ 0) (m u : ℕ) (hu : u ≤ m) :
    Tv x m (fun _ => 1) u = if u = m then x ^ m else 0 := by
  by_cases h : u = m
  · subst h
    rw [if_pos rfl, Tv_last hx, Zp_one hx u 0 (Nat.zero_le _), mul_one]
  · rw [if_neg h]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + u + 1 := ⟨m - u - 1, by omega⟩
    rw [Tv_row hx, Zp_one hx _ (k + 1) (by omega), Zp_one hx _ k (by omega)]
    ring

/-! ### Bounds along the path -/

lemma Zp_abs_le {x : ℝ} (hx : 1 ≤ x) {m : ℕ} {w : ℕ → ℝ} (hw : ∀ i ≤ m, |w i| ≤ 1) :
    ∀ k ≤ m, |Zp x m w k| ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have key : ∀ d k, k + d = m → |Zp x m w k| ≤ 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk
      simp only [Nat.add_zero] at hk
      subst hk
      rw [Zp_self]
      exact hw _ le_rfl
    | succ d ih =>
      intro k hk
      rw [Zp_rec hx0.ne' m w (by omega : k < m), abs_div, abs_of_pos hx0, div_le_one hx0]
      have h1 := ih (k + 1) (by omega)
      have h2 := hw k (by omega)
      calc |Zp x m w (k + 1) + (x - 1) * w k|
          ≤ |Zp x m w (k + 1)| + |(x - 1) * w k| := abs_add_le _ _
        _ = |Zp x m w (k + 1)| + (x - 1) * |w k| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1)]
        _ ≤ 1 + (x - 1) * 1 := by
          have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ x - 1)
          linarith
        _ = x := by ring
  intro k hk
  exact key (m - k) k (by omega)

lemma isSign_abs_le {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) : ∀ i ≤ m, |y i| ≤ 1 := by
  intro i hi
  rcases hy i hi with h | h <;> simp [h]

lemma isSign_abs {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {i : ℕ} (hi : i ≤ m) : |y i| = 1 := by
  rcases hy i hi with h | h <;> simp [h]

lemma isSign_sq {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {i : ℕ} (hi : i ≤ m) : y i * y i = 1 := by
  rcases hy i hi with h | h <;> rw [h] <;> norm_num

/-- Sign of the path: `y_k Z_k(y) ≥ (x-2)/x`. -/
lemma Zp_sign {x : ℝ} (hx : 2 ≤ x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    ∀ k ≤ m, (x - 2) / x ≤ y k * Zp x m y k := by
  have hx0 : 0 < x := by linarith
  have hZ := Zp_abs_le (by linarith) (isSign_abs_le hy)
  intro k hk
  by_cases hkm : k = m
  · subst hkm
    rw [Zp_self, isSign_sq hy le_rfl, div_le_one hx0]
    linarith
  · have hk' : k < m := lt_of_le_of_ne hk hkm
    have hyk := isSign_sq hy hk
    have e : y k * Zp x m y k = (y k * Zp x m y (k + 1) + (x - 1)) / x := by
      rw [Zp_rec hx0.ne' m y hk', mul_div_assoc']
      congr 1
      linear_combination (x - 1) * hyk
    have hb : -1 ≤ y k * Zp x m y (k + 1) := by
      have h1 : |y k * Zp x m y (k + 1)| ≤ 1 := by
        rw [abs_mul, isSign_abs hy hk, one_mul]
        exact hZ (k + 1) hk'
      linarith [neg_abs_le (y k * Zp x m y (k + 1))]
    rw [e]
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith

lemma Zp_abs_eq {x : ℝ} (hx : 2 ≤ x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {k : ℕ}
    (hk : k ≤ m) : |Zp x m y k| = y k * Zp x m y k := by
  have h := Zp_sign hx hy k hk
  have hx0 : 0 < x := by linarith
  have hnn : 0 ≤ y k * Zp x m y k := le_trans (div_nonneg (by linarith) hx0.le) h
  rw [← abs_of_nonneg hnn, abs_mul, isSign_abs hy hk, one_mul]

lemma nu_bounds {x : ℝ} (hx : 2 ≤ x) : ∀ k, (x - 2) / x ≤ nu x k ∧ nu x k ≤ 1 := by
  have hx0 : 0 < x := by linarith
  intro k
  induction k with
  | zero =>
    rw [nu_zero, div_le_one hx0]
    constructor <;> linarith
  | succ k ih =>
    rw [nu_succ]
    have hl : 0 ≤ (x - 2) / x := div_nonneg (by linarith) hx0.le
    constructor
    · apply div_le_div_of_nonneg_right _ hx0.le
      linarith [ih.2]
    · rw [div_le_one hx0]
      linarith [ih.1]

lemma nu_pos {x : ℝ} (hx : 2 < x) (k : ℕ) : 0 < nu x k := by
  have hx0 : 0 < x := by linarith
  exact lt_of_lt_of_le (div_pos (by linarith) hx0) (nu_bounds hx.le k).1

/-! ### Lemma 2: the scalar potential -/

/-- One step of the potential: `f_k = c_k - [y_k = y_{k+1}] 2 ν_{k+1} |Z_{k+1}|`. -/
lemma fk_eq {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {k : ℕ} (hk : k < m) :
    |Zp x m y k - Zp x m y (k + 1)| + nu x k * |Zp x m y k| - nu x (k + 1) * |Zp x m y (k + 1)| =
      cc x k - (if y k = y (k + 1) then 2 * nu x (k + 1) * |Zp x m y (k + 1)| else 0) := by
  have hx0 : 0 < x := by linarith
  have hb1 : |Zp x m y (k + 1)| ≤ 1 := Zp_abs_le (by linarith) (isSign_abs_le hy) (k + 1) hk
  have hs1 := Zp_sign hx.le hy (k + 1) hk
  have hq : 0 < (x - 2) / x := div_pos (by linarith) hx0
  rw [Zp_rec hx0.ne' m y hk, nu_succ]
  unfold cc
  set Z := Zp x m y (k + 1) with hZ
  have hZle := le_abs_self Z
  have hZge := neg_abs_le Z
  rcases hy k hk.le with h0 | h0 <;> rcases hy (k + 1) hk with h1 | h1
  · -- y_k = 1, y_{k+1} = 1
    rw [h1, one_mul] at hs1
    have hZpos : 0 < Z := lt_of_lt_of_le hq hs1
    have e1 : (Z + (x - 1) * y k) / x - Z = (x - 1) * (1 - Z) / x := by
      rw [h0]; field_simp; ring
    have e2 : 0 < (Z + (x - 1) * y k) / x := by
      rw [h0]; apply div_pos _ hx0; linarith
    rw [e1, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_pos e2, abs_of_pos hZpos, if_pos (by rw [h0, h1]), h0]
    field_simp
    ring
  · -- y_k = 1, y_{k+1} = -1
    rw [h1] at hs1
    have hZneg : Z < 0 := by linarith
    have e1 : (Z + (x - 1) * y k) / x - Z = (x - 1) * (1 - Z) / x := by
      rw [h0]; field_simp; ring
    have e2 : 0 < (Z + (x - 1) * y k) / x := by
      rw [h0]; apply div_pos _ hx0; linarith
    rw [e1, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_pos e2, abs_of_neg hZneg, if_neg (by rw [h0, h1]; norm_num), h0]
    field_simp
    ring
  · -- y_k = -1, y_{k+1} = 1
    rw [h1, one_mul] at hs1
    have hZpos : 0 < Z := lt_of_lt_of_le hq hs1
    have e1 : (Z + (x - 1) * y k) / x - Z = -((x - 1) * (1 + Z) / x) := by
      rw [h0]; field_simp; ring
    have e2 : (Z + (x - 1) * y k) / x < 0 := by
      rw [h0]; apply div_neg_of_neg_of_pos _ hx0; linarith
    rw [e1, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_neg e2, abs_of_pos hZpos, if_neg (by rw [h0, h1]; norm_num), h0]
    field_simp
    ring
  · -- y_k = -1, y_{k+1} = -1
    rw [h1] at hs1
    have hZneg : Z < 0 := by linarith
    have e1 : (Z + (x - 1) * y k) / x - Z = -((x - 1) * (1 + Z) / x) := by
      rw [h0]; field_simp; ring
    have e2 : (Z + (x - 1) * y k) / x < 0 := by
      rw [h0]; apply div_neg_of_neg_of_pos _ hx0; linarith
    rw [e1, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_neg e2, abs_of_neg hZneg, if_pos (by rw [h0, h1]), h0]
    field_simp
    ring

/-- The slack of a sign vector (`≥ 0`, and `0` iff the vector alternates). -/
def slack (x : ℝ) (m : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, (if y k = y (k + 1) then 2 * nu x (k + 1) * |Zp x m y (k + 1)| else 0)

/-- **Lemma 2 (potential identity).** -/
theorem L1_sign {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    L1 x m y = x ^ m * (∑ k ∈ range m, cc x k + nu x m - slack x m y) := by
  have hx0 : 0 < x := by linarith
  rw [L1_path hx0]
  congr 1
  have hf : ∀ k ∈ range m, |Zp x m y k - Zp x m y (k + 1)| =
      (cc x k - (if y k = y (k + 1) then 2 * nu x (k + 1) * |Zp x m y (k + 1)| else 0)) -
        (nu x k * |Zp x m y k| - nu x (k + 1) * |Zp x m y (k + 1)|) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← fk_eq hx hy hk]
    ring
  have htel := Finset.sum_range_sub' (fun k => nu x k * |Zp x m y k|) m
  rw [Finset.sum_congr rfl hf, Finset.sum_sub_distrib, Finset.sum_sub_distrib, htel, nu_zero,
    one_mul, Zp_self, isSign_abs hy le_rfl, mul_one]
  unfold slack
  ring

lemma slack_nonneg {x : ℝ} (hx : 2 < x) (m : ℕ) (y : ℕ → ℝ) : 0 ≤ slack x m y := by
  unfold slack
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) (nu_pos hx _).le) (abs_nonneg _)
  · exact le_rfl

lemma slack_sgnv (x : ℝ) (m : ℕ) : slack x m sgnv = 0 := by
  unfold slack
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  rw [sgnv_succ]
  intro h
  have h0 : sgnv k ≠ 0 := by simp [sgnv]
  exact h0 (by linarith)

/-- `d_m(x) = ‖T_m(x) s‖₁ = x^m (∑_{k<m} c_k + ν_m)`. -/
theorem L1_sgnv {x : ℝ} (hx : 2 < x) (m : ℕ) :
    L1 x m sgnv = x ^ m * (∑ k ∈ range m, cc x k + nu x m) := by
  rw [L1_sign hx (sgnv_isSign m), slack_sgnv, sub_zero]

/-- **Lemma 2 (inequality).** -/
theorem L1_le_sgnv {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    L1 x m y ≤ L1 x m sgnv := by
  have hx0 : 0 < x := by linarith
  rw [L1_sign hx hy, L1_sgnv hx]
  have := slack_nonneg hx m y
  have hp := pow_pos hx0 m
  nlinarith

/-- Positive slack when two consecutive signs agree. -/
lemma slack_pos {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {k : ℕ} (hk : k < m)
    (hyk : y k = y (k + 1)) : 0 < slack x m y := by
  unfold slack
  apply Finset.sum_pos'
  · intro j _
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (nu_pos hx _).le) (abs_nonneg _)
    · exact le_rfl
  · refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [if_pos hyk]
    have hx0 : 0 < x := by linarith
    have h1 : 0 < |Zp x m y (k + 1)| := by
      rw [Zp_abs_eq hx.le hy hk]
      exact lt_of_lt_of_le (div_pos (by linarith) hx0) (Zp_sign hx.le hy (k + 1) hk)
    exact mul_pos (mul_pos (by norm_num) (nu_pos hx _)) h1

/-- An alternating sign vector is `±s`. -/
lemma alternating_eq {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) (halt : ∀ k < m, y k ≠ y (k + 1)) :
    (∀ i ≤ m, y i = sgnv i) ∨ (∀ i ≤ m, y i = -sgnv i) := by
  have key : ∀ i ≤ m, y i = y 0 * sgnv i := by
    intro i
    induction i with
    | zero => intro _; rw [sgnv_zero, mul_one]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hne := halt i (by omega)
      rw [sgnv_succ]
      rcases hy i (by omega) with a | a <;> rcases hy (i + 1) hi with b | b
      · exact absurd (a.trans b.symm) hne
      · rw [b]; linarith
      · rw [b]; linarith
      · exact absurd (a.trans b.symm) hne
  rcases hy 0 (Nat.zero_le _) with h | h
  · left; intro i hi; rw [key i hi, h, one_mul]
  · right; intro i hi; rw [key i hi, h]; ring

/-- **Lemma 2 (equality case).** -/
theorem L1_eq_sgnv {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y)
    (h : L1 x m y = L1 x m sgnv) : (∀ i ≤ m, y i = sgnv i) ∨ (∀ i ≤ m, y i = -sgnv i) := by
  apply alternating_eq hy
  intro k hk hyk
  have hx0 : 0 < x := by linarith
  have hpos := slack_pos hx hy hk hyk
  rw [L1_sign hx hy, L1_sgnv hx] at h
  have hp := pow_pos hx0 m
  have : x ^ m * slack x m y = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hp.ne'
  · exact absurd h1 hpos.ne'

lemma L1_neg_sgnv (x : ℝ) (m : ℕ) : L1 x m (fun i => -sgnv i) = L1 x m sgnv := by
  have := L1_smul x m (-1) sgnv
  simp only [neg_one_mul, abs_neg, abs_one, one_mul] at this
  exact this

/-- `(T_m(x) s)_m > 0`. -/
theorem Tv_sgnv_last_pos {x : ℝ} (hx : 2 < x) (m : ℕ) : 0 < Tv x m sgnv m := by
  have hx0 : 0 < x := by linarith
  rw [Tv_last hx0.ne']
  have h := Zp_sign hx.le (sgnv_isSign m) 0 (Nat.zero_le _)
  rw [sgnv_zero, one_mul] at h
  exact mul_pos (pow_pos hx0 m) (lt_of_lt_of_le (div_pos (by linarith) hx0) h)

lemma L1_sgnv_pos {x : ℝ} (hx : 2 < x) (m : ℕ) : 0 < L1 x m sgnv := by
  unfold L1
  rw [Finset.sum_range_succ]
  have := Tv_sgnv_last_pos hx m
  have h2 : 0 ≤ ∑ u ∈ range m, |Tv x m sgnv u| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [abs_of_pos this]
  linarith

end ICGGeneral
