import Mathlib
import Research.ICGEqualParityLemmas

/-!
# Theorem A (round 4): the exponent pair `(1, m)`, `m` odd

Formalisation of §2 of `work/round4/icg-equal-parity/PROOF.md` (sign-matrix form).

For sign vectors `u, v` on `0..m` (the two rows of `Y`, with `v_m = Y_{1m} = -1`) put
`w1 = u - v`, `w2 = R u + v` and

  `PhiA x R m u v = R ‖T_m(x) w1‖₁ + ‖T_m(x) w2‖₁ - 2 x^m max(0, -Z_0(w2))`,

which equals `G(Y) = 2E - n` for `Y = [u; v]` and `T_1(R+1)` on the row side
(`(T_1(r) Y)` has rows `-R (u - v)` and `R u + v`).  **Theorem A** (`thmA_le`):
for odd `m` and `(x ≥ 5, R ≥ 2)` or `(x = 3, R ≥ 4)`,

  `PhiA x R m u v ≤ (3R - 1) d_m(x) - 2 (R - 1) δ_m(x)`,

with `d_m(x) = ‖T_m(x) s‖₁ = L1 x m sgnv` and `δ_m(x) = (T_m(x) s)_m = Tv x m sgnv m`.
-/

noncomputable section

namespace ICGEqualParity

open Finset ICGGeneral

/-! ### Small helpers -/

lemma Zp_congr_from (x : ℝ) (m : ℕ) {w w' : ℕ → ℝ} (k : ℕ)
    (h : ∀ i, k ≤ i → i ≤ m → w i = w' i) : Zp x m w k = Zp x m w' k := by
  unfold Zp Wp
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [h j hj.1 (by omega)]

lemma Zp_abs_le_C {x : ℝ} (hx : 1 ≤ x) {m : ℕ} {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i ≤ m, |w i| ≤ C) : ∀ k ≤ m, |Zp x m w k| ≤ C := by
  have hx0 : 0 < x := by linarith
  have key : ∀ d k, k + d = m → |Zp x m w k| ≤ C := by
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
      rw [Zp_rec hx0.ne' m w (by omega : k < m), abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
      have h1 := ih (k + 1) (by omega)
      have h2 := hw k (by omega)
      calc |Zp x m w (k + 1) + (x - 1) * w k|
          ≤ |Zp x m w (k + 1)| + |(x - 1) * w k| := abs_add_le _ _
        _ = |Zp x m w (k + 1)| + (x - 1) * |w k| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1)]
        _ ≤ C + (x - 1) * C := by
          have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ x - 1)
          linarith
        _ = C * x := by ring
  intro k hk
  exact key (m - k) k (by omega)

lemma hcell_zero_left (P μ B : ℝ) : hcell P μ 0 B = 2 * μ * |B| := by
  unfold hcell
  simp only [zero_sub, abs_neg, mul_zero, add_zero, abs_zero]
  ring

lemma hcell_same_pos {P μ A B : ℝ} (hμ0 : 0 ≤ μ) (hPμ : μ ≤ P) (hB : 0 ≤ B) (hBA : B ≤ A) :
    hcell P μ A B = -2 * (P - μ) * B := by
  have hP : 0 ≤ P := le_trans hμ0 hPμ
  have hA : 0 ≤ A := le_trans hB hBA
  unfold hcell
  rw [abs_of_nonneg (by linarith : 0 ≤ A - B), abs_of_nonneg (by nlinarith : 0 ≤ B + P * A),
    abs_of_nonneg hB, abs_of_nonneg hA]
  ring

lemma sign_cases {m : ℕ} {u : ℕ → ℝ} (hu : IsSign m u) {i : ℕ} (hi : i ≤ m) :
    u i = 1 ∨ u i = -1 := hu i hi

/-- Budget of one position: `R|u-v| + |Ru+v|`. -/
lemma budget_eq {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    R * |a - b| + |R * a + b| = if a = b then R + 1 else 3 * R - 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [if_pos rfl, sub_self, abs_zero, mul_zero, zero_add, mul_one,
      abs_of_pos (by linarith : (0:ℝ) < R + 1)]
  · rw [if_neg (by norm_num)]
    rw [show (1 : ℝ) - -1 = 2 by norm_num, show R * 1 + -1 = R - 1 by ring,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 1)]
    ring
  · rw [if_neg (by norm_num)]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, show R * -1 + 1 = -(R - 1) by ring, abs_neg, abs_neg,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 1)]
    ring
  · rw [if_pos rfl]
    rw [show (-1 : ℝ) - -1 = 0 by norm_num, show R * -1 + -1 = -(R + 1) by ring, abs_neg,
      abs_zero, abs_of_pos (by linarith : (0:ℝ) < R + 1)]
    ring

/-! ### Parameters -/

/-- The parameter range of Theorem A. -/
def ParamOK (x R : ℝ) : Prop := (5 ≤ x ∧ 2 ≤ R) ∨ (x = 3 ∧ 4 ≤ R)

lemma ParamOK.basic {x R : ℝ} (h : ParamOK x R) :
    3 ≤ x ∧ 2 ≤ R ∧ R + 1 ≤ (x - 1) * (R - 1) := by
  rcases h with ⟨hx, hR⟩ | ⟨hx, hR⟩
  · refine ⟨by linarith, hR, ?_⟩
    nlinarith
  · subst hx
    refine ⟨le_rfl, by linarith, ?_⟩
    nlinarith

lemma nu_nonneg' {x : ℝ} (hx : 2 ≤ x) (k : ℕ) : 0 ≤ nu x k :=
  le_trans (div_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ x))
    (nu_bounds hx k).1

/-! ### The per-position slack -/

/-- `w1 = u - v`. -/
def w1 (u v : ℕ → ℝ) : ℕ → ℝ := fun i => u i - v i

/-- `w2 = R u + v`. -/
def w2 (R : ℝ) (u v : ℕ → ℝ) : ℕ → ℝ := fun i => R * u i + v i

/-- Slack of position `k < m`. -/
def slk (x R : ℝ) (m : ℕ) (u v : ℕ → ℝ) (k : ℕ) : ℝ :=
  cc x k * (3 * R - 1) - cc x k * (R * |u k - v k| + |R * u k + v k|) -
    (R * hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)) +
      hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (w2 R u v) (k + 1))) / x

/-- The `w2` cells are non-positive. -/
lemma h2_nonpos {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) :
    hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (w2 R u v) (k + 1)) ≤ 0 := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k
  apply hcell_nonpos (nu_nonneg' (x := x) (by linarith) k) hnb.2 (by linarith [hnb.2] : nu x k ≤ x - 1)
  have hB : |Zp x m (w2 R u v) (k + 1)| ≤ R + 1 := by
    apply Zp_abs_le_C (by linarith) _ (k + 1) hk
    intro i hi
    unfold w2
    rcases hu i hi with h1 | h1 <;> rcases hv i hi with h2 | h2 <;> rw [h1, h2]
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [show R * -1 + 1 = -(R - 1) by ring, abs_neg, abs_of_nonneg (by linarith)]; linarith
    · rw [show R * -1 + -1 = -(R + 1) by ring, abs_neg, abs_of_pos (by linarith)]
  have hA : R - 1 ≤ |R * u k + v k| := by
    rcases hu k hk.le with h1 | h1 <;> rcases hv k hk.le with h2 | h2 <;> rw [h1, h2]
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [show R * -1 + 1 = -(R - 1) by ring, abs_neg, abs_of_nonneg (by linarith)]
    · rw [show R * -1 + -1 = -(R + 1) by ring, abs_neg, abs_of_pos (by linarith)]; linarith
  have : (x - 1) * (R - 1) ≤ (x - 1) * |R * u k + v k| :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  linarith

lemma Zw1_abs_le {x : ℝ} (hx : 1 ≤ x) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k ≤ m) : |Zp x m (w1 u v) k| ≤ 2 := by
  apply Zp_abs_le_C hx _ k hk
  intro i hi
  unfold w1
  rcases hu i hi with h1 | h1 <;> rcases hv i hi with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- Positions where `u` and `v` differ: non-negative slack (and a lower bound). -/
lemma slk_D {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) (hne : u k ≠ v k) :
    (-(R * hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)))) / x ≤ slk x R m u v k ∧
      0 ≤ (-(R * hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)))) / x := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k
  have hnu0 : 0 ≤ nu x k := nu_nonneg' (x := x) (by linarith) k
  have hbud := budget_eq (by linarith : (1:ℝ) ≤ R) (hu k hk.le) (hv k hk.le)
  rw [if_neg hne] at hbud
  have h2 := h2_nonpos hp hu hv hk
  have h1 : hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)) ≤ 0 := by
    apply hcell_nonpos hnu0 hnb.2 (by linarith [hnb.2] : nu x k ≤ x - 1)
    have hB := Zw1_abs_le (x := x) (by linarith) hu hv (show k + 1 ≤ m from hk)
    have hA : |u k - v k| = 2 := by
      rcases hu k hk.le with a | a <;> rcases hv k hk.le with b | b <;> rw [a, b] at hne ⊢
      · exact absurd rfl hne
      · norm_num
      · norm_num
      · exact absurd rfl hne
    rw [hA]
    linarith
  set H1 := hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)) with hH1
  set H2 := hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (w2 R u v) (k + 1)) with hH2
  have key : slk x R m u v k = (-(R * H1)) / x + (-H2) / x := by
    unfold slk
    rw [hbud]
    ring
  have hA2 : 0 ≤ (-H2) / x := div_nonneg (by linarith) hx0.le
  have hA1 : 0 ≤ (-(R * H1)) / x := div_nonneg (by nlinarith) hx0.le
  constructor
  · rw [key]; linarith
  · exact hA1

/-- Positions where `u` and `v` agree: slack at least the surplus. -/
lemma slk_E {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) (heq : u k = v k) :
    2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x ≤ slk x R m u v k := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hbud := budget_eq (by linarith : (1:ℝ) ≤ R) (hu k hk.le) (hv k hk.le)
  rw [if_pos heq] at hbud
  have h2 := h2_nonpos hp hu hv hk
  have hw : u k - v k = 0 := by rw [heq]; ring
  set H2 := hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (w2 R u v) (k + 1)) with hH2
  have key : slk x R m u v k =
      (2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x) + (-H2) / x := by
    unfold slk
    rw [hbud, hw, hcell_zero_left]
    ring
  have hA2 : 0 ≤ (-H2) / x := div_nonneg (by linarith) hx0.le
  rw [key]
  linarith

lemma surplus_nonneg {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) :
    0 ≤ 2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k
  have hnu0 : 0 ≤ nu x k := nu_nonneg' (x := x) (by linarith) k
  have hB := Zw1_abs_le (x := x) (by linarith) hu hv (show k + 1 ≤ m from hk)
  have key : 2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x =
      (2 * (R - 1) * (x - 1) * (1 + nu x k) - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)|) / x := by
    unfold cc
    ring
  rw [key]
  apply div_nonneg _ hx0.le
  have h1 : 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| ≤ 2 * R * nu x k * 2 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h2 : 2 * (R - 1) * 2 * (1 + nu x k) ≤ 2 * (R - 1) * (x - 1) * (1 + nu x k) := by
    have : 0 ≤ 2 * (R - 1) * (1 + nu x k) := by nlinarith
    nlinarith
  nlinarith [hnb.2]

lemma slk_nonneg {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) : 0 ≤ slk x R m u v k := by
  by_cases h : u k = v k
  · exact le_trans (surplus_nonneg hp hu hv hk) (slk_E hp hu hv hk h)
  · have := slk_D hp hu hv hk h
    linarith [this.1, this.2]

/-! ### The refined argument for `x = 3` (only position 0 agrees) -/

lemma cell_pos1 {z : ℝ} (hz : 1 / 3 ≤ z) (hz1 : z ≤ 1) : hcell 2 (1 / 3) 2 (2 * z) ≤ -20 / 9 := by
  unfold hcell
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 - 2 * z), abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * z + 2 * 2),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * z), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

lemma cell_neg1 {z : ℝ} (hz : z ≤ -1 / 3) (hz1 : -1 ≤ z) : hcell 2 (1 / 3) (-2) (2 * z) ≤ -20 / 9 := by
  unfold hcell
  rw [abs_of_nonpos (by linarith : -2 - 2 * z ≤ (0:ℝ)), abs_of_nonpos (by linarith : 2 * z + 2 * -2 ≤ (0:ℝ)),
    abs_of_nonpos (by linarith : 2 * z ≤ (0:ℝ)), abs_of_nonpos (by norm_num : (-2:ℝ) ≤ 0)]
  linarith

lemma refine_x3 {R : ℝ} (hR : 4 ≤ R) {m : ℕ} (hm3 : 3 ≤ m) {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) (hD : ∀ i, 1 ≤ i → i ≤ m → v i = -u i) (h0eq : u 0 = v 0)
    (hnum3 : nu 3 m < 1 / 2) :
    2 * (R - 1) * nu 3 m ≤ ∑ j ∈ range m, slk 3 R m u v j := by
  have hp : ParamOK 3 R := Or.inr ⟨rfl, hR⟩
  have hRpos : 0 < R := by linarith
  have hslk := fun k (hk : k < m) => slk_nonneg hp hu hv hk
  have hZw1 : ∀ j, 1 ≤ j → Zp 3 m (w1 u v) j = 2 * Zp 3 m u j := by
    intro j hj
    rw [Zp_congr_from 3 m (w' := fun i => 2 * u i + 0 * u i) j
      (fun i hi him => by unfold w1; rw [hD i (by omega) him]; ring), Zp_linear]
    ring
  have hsum2 : slk 3 R m u v 0 + slk 3 R m u v 1 ≤ ∑ j ∈ range m, slk 3 R m u v j := by
    have hsub : ({0, 1} : Finset ℕ) ⊆ range m := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_range]
      omega
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj _ => hslk j (Finset.mem_range.mp hj))
    rw [Finset.sum_pair (by norm_num)] at this
    exact this
  have hsl1 := hslk 1 (by omega)
  have e0 : cc 3 0 = 4 / 3 := by unfold cc; rw [nu_zero]; norm_num
  have h0 := slk_E hp hu hv (by omega : 0 < m) h0eq
  rw [e0, nu_zero, hZw1 1 le_rfl, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h0
  have hZu1 : |Zp 3 m u 1| ≤ 1 := Zp_abs_le (by norm_num) (isSign_abs_le hu) 1 (by omega)
  have hm2 := mul_le_mul_of_nonneg_left hnum3.le (by linarith : (0:ℝ) ≤ 2 * (R - 1))
  by_cases hsmall : |Zp 3 m u 1| ≤ 5 * (R - 1) / (4 * R)
  · have hb : 4 * R * |Zp 3 m u 1| ≤ 5 * (R - 1) := by
      rw [le_div_iff₀ (by linarith)] at hsmall
      linarith
    linarith
  · push Not at hsmall
    have hu12 : u 1 = u 2 := by
      by_contra hne12
      have hstep := Zp_step_alt (x := 3) (by norm_num) hu (by omega : 1 < m) hne12
      have hs2 : (3 - 2) / 3 ≤ u 2 * Zp 3 m u 2 := Zp_sign (x := 3) (by norm_num) hu 2 (by omega)
      have hZ2 : |Zp 3 m u 2| = u 2 * Zp 3 m u 2 := Zp_abs_eq (by norm_num) hu (by omega : 2 ≤ m)
      have h59 : |Zp 3 m u 1| ≤ 5 / 9 := by
        rw [hstep, hZ2]
        norm_num at hs2 ⊢
        linarith
      have h1516 : 15 / 16 ≤ 5 * (R - 1) / (4 * R) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      linarith
    have hne1 : u 1 ≠ v 1 := by
      rw [hD 1 le_rfl (by omega)]
      intro h
      rcases hu 1 (by omega) with a | a <;> rw [a] at h <;> norm_num at h
    have hD1 := (slk_D hp hu hv (by omega : 1 < m) hne1).1
    have hcell1 : hcell (3 - 1) (nu 3 1) (u 1 - v 1) (Zp 3 m (w1 u v) (1 + 1)) ≤ -20 / 9 := by
      have hA : u 1 - v 1 = 2 * u 1 := by rw [hD 1 le_rfl (by omega)]; ring
      have hB : Zp 3 m (w1 u v) (1 + 1) = 2 * Zp 3 m u 2 := hZw1 2 (by norm_num)
      have e1 : nu 3 1 = 1 / 3 := by rw [nu_succ, nu_zero]; norm_num
      have e3 : (3:ℝ) - 1 = 2 := by norm_num
      rw [hA, hB, e1, e3]
      have hs2 : (3 - 2) / 3 ≤ u 2 * Zp 3 m u 2 := Zp_sign (x := 3) (by norm_num) hu 2 (by omega)
      have hZ2le : |Zp 3 m u 2| ≤ 1 := Zp_abs_le (by norm_num) (isSign_abs_le hu) 2 (by omega)
      have hZ2a := le_abs_self (Zp 3 m u 2)
      have hZ2b := neg_abs_le (Zp 3 m u 2)
      rcases hu 1 (by omega) with a | a
      · have hu2 : u 2 = 1 := by rw [← hu12, a]
        rw [hu2] at hs2
        rw [a, show (2:ℝ) * 1 = 2 by norm_num]
        exact cell_pos1 (by linarith) (by linarith)
      · have hu2 : u 2 = -1 := by rw [← hu12, a]
        rw [hu2] at hs2
        rw [a, show (2:ℝ) * -1 = -2 by norm_num]
        exact cell_neg1 (by linarith) (by linarith)
    have hRc := mul_le_mul_of_nonneg_left hcell1 hRpos.le
    have hpay : 20 * R / 27 ≤ slk 3 R m u v 1 := by
      have h' : 20 * R / 27 ≤
          (-(R * hcell (3 - 1) (nu 3 1) (u 1 - v 1) (Zp 3 m (w1 u v) (1 + 1)))) / 3 := by
        rw [le_div_iff₀ (by norm_num)]
        linarith
      linarith
    have hRZ1 := mul_le_mul_of_nonneg_left hZu1 hRpos.le
    linarith

/-! ### The main identity -/

lemma phi_identity {x R : ℝ} (hx : 1 < x) (m : ℕ) (u v : ℕ → ℝ) :
    R * L1 x m (w1 u v) + L1 x m (w2 R u v) =
      x ^ m * ((3 * R - 1) * ∑ k ∈ range m, cc x k - ∑ k ∈ range m, slk x R m u v k +
        nu x m * (R * |u m - v m| + |R * u m + v m|)) := by
  rw [L1_potential hx m (w1 u v), L1_potential hx m (w2 R u v)]
  unfold slk w1 w2
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  have e : ∀ k ∈ range m,
      (3 * R - 1) * cc x k - (cc x k * (3 * R - 1) - cc x k * (R * |u k - v k| + |R * u k + v k|) -
        (R * hcell (x - 1) (nu x k) (u k - v k) (Zp x m (fun i => u i - v i) (k + 1)) +
          hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (fun i => R * u i + v i) (k + 1))) / x) =
      R * (cc x k * |u k - v k|) + cc x k * |R * u k + v k| +
        (R * (hcell (x - 1) (nu x k) (u k - v k) (Zp x m (fun i => u i - v i) (k + 1)) / x) +
          hcell (x - 1) (nu x k) (R * u k + v k) (Zp x m (fun i => R * u i + v i) (k + 1)) / x) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ### Theorem A -/

theorem thmA_le {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : Odd m) {u v : ℕ → ℝ}
    (hu : IsSign m u) (hv : IsSign m v) (hvm : v m = -1) :
    R * L1 x m (w1 u v) + L1 x m (w2 R u v) -
        2 * x ^ m * max 0 (-(Zp x m (w2 R u v) 0)) ≤
      (3 * R - 1) * L1 x m sgnv - 2 * (R - 1) * Tv x m sgnv m := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hx2 : 2 < x := by linarith
  have hxm := pow_pos hx0 m
  have hTs : Tv x m sgnv m = x ^ m * nu x m := by rw [Tv_last hx0.ne', Zp_sgnv_zero hx2]
  have hLs := L1_sgnv hx2 m
  have hM0 : 0 ≤ max 0 (-(Zp x m (w2 R u v) 0)) := le_max_left _ _
  have hnum := nu_odd_lt (x := x) (by linarith) hm
  have hnupos := nu_pos hx2 m
  set L := (x - 1) / (x + 1) with hL
  have hslk := fun k (hk : k < m) => slk_nonneg hp hu hv hk
  have hsum0 : 0 ≤ ∑ k ∈ range m, slk x R m u v k :=
    Finset.sum_nonneg (fun k hk => hslk k (Finset.mem_range.mp hk))
  by_cases hIII : ∀ k ≤ m, u k ≠ v k
  · -- Case III: v = -u
    have hvu : ∀ i ≤ m, v i = -u i := by
      intro i hi
      rcases hu i hi with a | a <;> rcases hv i hi with b | b
      · exact absurd (a.trans b.symm) (hIII i hi)
      · rw [a, b]
      · rw [a, b]; norm_num
      · exact absurd (a.trans b.symm) (hIII i hi)
    have hw1 : L1 x m (w1 u v) = 2 * L1 x m u := by
      rw [L1_congr x m (w' := fun i => 2 * u i) (fun i hi => by unfold w1; rw [hvu i hi]; ring),
        L1_smul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hw2 : L1 x m (w2 R u v) = (R - 1) * L1 x m u := by
      rw [L1_congr x m (w' := fun i => (R - 1) * u i) (fun i hi => by unfold w2; rw [hvu i hi]; ring),
        L1_smul, abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 1)]
    have hz2 : Zp x m (w2 R u v) 0 = (R - 1) * Zp x m u 0 := by
      rw [Zp_congr x m (w' := fun i => (R - 1) * u i + 0 * u i)
        (fun i hi => by unfold w2; rw [hvu i hi]; ring), Zp_linear]
      ring
    have hum : u m = 1 := by
      have := hvu m le_rfl
      rw [hvm] at this
      linarith
    rw [hw1, hw2, hz2]
    rcases hu 0 (Nat.zero_le _) with hu0 | hu0
    · -- IIIa: u_0 = 1
      have hzpos : 0 < Zp x m u 0 := by
        have hs := Zp_sign hx2.le hu 0 (Nat.zero_le _)
        rw [hu0, one_mul] at hs
        exact lt_of_lt_of_le (div_pos (by linarith) hx0) hs
      have hmax : max 0 (-((R - 1) * Zp x m u 0)) = 0 := by
        apply max_eq_left
        nlinarith
      rw [hmax, L1_sign hx2 hu, hTs, hLs]
      have hB := lemmaB (by linarith : (3:ℝ) ≤ x) (by linarith : (1:ℝ) ≤ R) hm hu (by rw [hu0, hum])
      have hB' := mul_le_mul_of_nonneg_left hB.le hxm.le
      nlinarith
    · -- IIIb: u_0 = -1
      have hzneg : Zp x m u 0 < 0 := by
        have hs := Zp_sign hx2.le hu 0 (Nat.zero_le _)
        rw [hu0] at hs
        have : 0 < (x - 2) / x := div_pos (by linarith) hx0
        linarith
      have hmax : max 0 (-((R - 1) * Zp x m u 0)) = (R - 1) * |Zp x m u 0| := by
        rw [abs_of_neg hzneg]
        have hnn : 0 ≤ -((R - 1) * Zp x m u 0) := by nlinarith
        rw [max_eq_right hnn]
        ring
      rw [hmax, hTs]
      have hpath := L1_path hx0 m u
      have hC := noncorner_le hx2 hu
      rw [noncorner_sgnv hx2] at hC
      have hle := L1_le_sgnv hx2 hu
      rw [hLs] at hle ⊢
      have hR1 : 0 ≤ R - 1 := by linarith
      -- (3R-1) L1 u - 2 x^m (R-1)|Z0| = (R+1) L1 u + 2(R-1) x^m Σ|ΔZ|
      have e : 2 * L1 x m u * R + (R - 1) * L1 x m u - 2 * x ^ m * ((R - 1) * |Zp x m u 0|) =
          (R + 1) * L1 x m u + 2 * (R - 1) * (x ^ m *
            ∑ k ∈ range m, |Zp x m u k - Zp x m u (k + 1)|) := by
        rw [hpath]; ring
      have e2 : R * (2 * L1 x m u) + (R - 1) * L1 x m u -
          2 * x ^ m * ((R - 1) * |Zp x m u 0|) =
          (R + 1) * L1 x m u + 2 * (R - 1) * (x ^ m *
            ∑ k ∈ range m, |Zp x m u k - Zp x m u (k + 1)|) := by
        rw [← e]; ring
      rw [e2]
      have h1 : (R + 1) * L1 x m u ≤ (R + 1) * (x ^ m * (∑ k ∈ range m, cc x k + nu x m)) :=
        mul_le_mul_of_nonneg_left hle (by linarith)
      have h2 : 2 * (R - 1) * (x ^ m * ∑ k ∈ range m, |Zp x m u k - Zp x m u (k + 1)|) ≤
          2 * (R - 1) * (x ^ m * ∑ k ∈ range m, cc x k) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hC hxm.le
      nlinarith
  · -- Cases I and II
    push Not at hIII
    obtain ⟨k0, hk0m, hk0⟩ := hIII
    rw [phi_identity (by linarith) m u v, hTs, hLs]
    have hbudm := budget_eq (by linarith : (1:ℝ) ≤ R) (hu m le_rfl) (hv m le_rfl)
    by_cases hEm : u m = v m
    · -- Case I
      rw [hbudm, if_pos hEm]
      have h1 := mul_nonneg hxm.le hsum0
      have h2 := mul_nonneg hxm.le hM0
      nlinarith
    · -- Case II
      rw [hbudm, if_neg hEm]
      have hk0lt : k0 < m := lt_of_le_of_ne hk0m (fun h => hEm (h ▸ hk0))
      -- it suffices to show  ∑ slk ≥ 2 (R-1) ν_m
      suffices hS : 2 * (R - 1) * nu x m ≤ ∑ k ∈ range m, slk x R m u v k by
        have h1 := mul_le_mul_of_nonneg_left hS hxm.le
        have h2 := mul_nonneg hxm.le hM0
        nlinarith
      have hRm1 : 0 < R - 1 := by linarith
      -- generic numeric bound for an agreeing position k with ν_k small enough
      have hgen : ∀ k, k < m → u k = v k →
          (R - 1) * (x - 1) * (1 + nu x k * (x + 1)) - 2 * R * nu x k * (x + 1) ≥ 0 →
          2 * (R - 1) * nu x m ≤ ∑ j ∈ range m, slk x R m u v j := by
        intro k hk heq hnumk
        have h1 := slk_E hp hu hv hk heq
        have hB := Zw1_abs_le (x := x) (by linarith) hu hv (show k + 1 ≤ m from hk)
        have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k
        have hnu0 : 0 ≤ nu x k := nu_nonneg' (x := x) (by linarith) k
        have hsingle : slk x R m u v k ≤ ∑ j ∈ range m, slk x R m u v j :=
          Finset.single_le_sum (f := fun j => slk x R m u v j)
            (fun j hj => hslk j (Finset.mem_range.mp hj)) (Finset.mem_range.mpr hk)
        have hB2 : 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| ≤ 2 * R * nu x k * 2 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        have hsur : 2 * (R - 1) * L ≤
            2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x := by
          have key : 2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x =
              (2 * (R - 1) * (x - 1) * (1 + nu x k) - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)|) / x := by
            unfold cc
            ring
          have keyL : 2 * (R - 1) * L = (2 * (R - 1) * (x - 1)) / (x + 1) := by
            rw [hL]; ring
          rw [key, keyL, div_le_div_iff₀ (by linarith : (0:ℝ) < x + 1) hx0]
          have hZ' : 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| * (x + 1) ≤
              2 * R * nu x k * 2 * (x + 1) := mul_le_mul_of_nonneg_right hB2 (by linarith)
          nlinarith [hZ', hnumk]
        have hmL : 2 * (R - 1) * nu x m ≤ 2 * (R - 1) * L :=
          mul_le_mul_of_nonneg_left hnum.le (by linarith)
        linarith
      have hp' := hp
      rcases hp' with ⟨hx5, hR2⟩ | ⟨hx3, hR4⟩
      · -- x ≥ 5
        apply hgen k0 hk0lt hk0
        have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k0
        have hnu0 : 0 ≤ nu x k0 := nu_nonneg' (x := x) (by linarith) k0
        have ht : 0 ≤ R * (x - 3) - (x - 1) := by nlinarith
        have t1 : 0 ≤ nu x k0 * (x + 1) * (R * (x - 3) - (x - 1)) :=
          mul_nonneg (mul_nonneg hnu0 (by linarith)) ht
        have t2 : 0 ≤ (R - 1) * (x - 1) := by nlinarith
        have e : (R - 1) * (x - 1) * (1 + nu x k0 * (x + 1)) - 2 * R * nu x k0 * (x + 1) =
            (R - 1) * (x - 1) + nu x k0 * (x + 1) * (R * (x - 3) - (x - 1)) := by ring
        rw [ge_iff_le, e]
        linarith
      · -- x = 3
        subst hx3
        have hL3 : L = 1 / 2 := by rw [hL]; norm_num
        have hnum3 : nu 3 m < 1 / 2 := by rw [← hL3]; exact hnum
        by_cases hex : ∃ k, 1 ≤ k ∧ k < m ∧ u k = v k
        · obtain ⟨k, hk1, hkm, hkeq⟩ := hex
          apply hgen k hkm hkeq
          -- ν_k ≤ 5/9 for k ≥ 1
          have hle : nu 3 k ≤ 5 / 9 := by
            rcases Nat.even_or_odd k with he | ho
            · have h2 : 2 ≤ k := by
                rcases he with ⟨a, ha⟩; omega
              have := nu_even_le_two (x := 3) (by norm_num) he h2
              have e2 : nu 3 2 = 5 / 9 := by
                rw [nu_succ, nu_succ, nu_zero]; norm_num
              linarith
            · have := nu_odd_lt (x := (3:ℝ)) (by norm_num) ho
              norm_num at this
              linarith
          have e : (R - 1) * (3 - 1) * (1 + nu 3 k * (3 + 1)) - 2 * R * nu 3 k * (3 + 1) =
              2 * (R - 1) - 8 * nu 3 k := by ring
          rw [ge_iff_le, e]
          linarith
        · -- only position 0 agrees: refined argument
          push Not at hex
          have hk00 : k0 = 0 := by
            by_contra h0
            exact hex k0 (by omega) hk0lt hk0
          subst hk00
          by_cases hm1 : m = 1
          · subst hm1
            have e0 : cc 3 0 = 4 / 3 := by unfold cc; rw [nu_zero]; norm_num
            have h0 := slk_E hp hu hv (by omega : 0 < 1) hk0
            rw [e0, nu_zero] at h0
            have hz : |Zp 3 1 (w1 u v) 1| ≤ 2 := Zw1_abs_le (x := 3) (by norm_num) hu hv le_rfl
            have hsingle : slk 3 R 1 u v 0 ≤ ∑ j ∈ range 1, slk 3 R 1 u v j := by simp
            have e1 : nu 3 1 = 1 / 3 := by rw [nu_succ, nu_zero]; norm_num
            rw [e1]
            have hRZ : 2 * R * 1 * |Zp 3 1 (w1 u v) 1| ≤ 2 * R * 1 * 2 :=
              mul_le_mul_of_nonneg_left hz (by linarith)
            linarith
          · have hm3 : 3 ≤ m := by
              rcases hm with ⟨a, ha⟩; omega
            have hD : ∀ i, 1 ≤ i → i ≤ m → v i = -u i := by
              intro i hi1 him
              have hne : u i ≠ v i := by
                by_cases hi : i = m
                · rw [hi]; exact hEm
                · exact hex i hi1 (lt_of_le_of_ne him hi)
              rcases hu i him with a | a <;> rcases hv i him with b | b
              · exact absurd (a.trans b.symm) hne
              · rw [a, b]
              · rw [a, b]; norm_num
              · exact absurd (a.trans b.symm) hne
            exact refine_x3 hR4 hm3 hu hv hD hk0 hnum3

end ICGEqualParity
