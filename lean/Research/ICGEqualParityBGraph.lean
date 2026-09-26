import Mathlib
import Research.ICGEqualParityBMain

set_option autoImplicit false

/-!
# Theorem B (round 6): maximal energy of `ICG(p² q^b)` for even `b`

* `G_Ym`, `G_Yp`: `G(Y⁻) = G(Y⁺) = Θ`.
* `thmB'`: **Theorem B′** (real parameters `p ≥ 5, q ≥ 3` or `p = 3, q ≥ 5`).
* `two_L1mat_rows2`: `2E = G(Y) + n` for `n = p² q^b` and the sign matrix `Y = 2X - J` of `D`.
* `theoremB`: for distinct odd primes `p, q` and even `b ≥ 2`, every set `D` of proper divisors
  of `n = p² q^b` has `E(ICG_n(D)) ≤ ½[n + (5p² - 8p + 4) d_b(q)] - (p² - 2p + 2) δ_b(q)`, with
  equality iff `D = D⁻ = {p^i q^j : i + j odd}` or `D = D⁺ \ {n}`; here `d_b(q) = L1 q b sgnv`
  (`= ‖T_b(q) s‖₁`) and `δ_b(q) = Tv q b sgnv b` (`= (T_b(q) s)_b`), as in `corollaryA`.
* `corollaryB`: the same in the format of `ICGEqualParity.corollaryA`.
* `theoremB_swap`: the case `n = p^b q²` (exchange of the primes).

The energy is the genuine graph energy `ICGBridge.energy` (sum of the absolute values of the
eigenvalues of the adjacency matrix).
-/

noncomputable section

namespace ICGEqualParityB

open Finset ICGGeneral ICGEqualParity

/-! ### `G` only depends on the box `{0,1,2} × {0,…,b}` -/

lemma Gfun_congr {p q : ℝ} {b : ℕ} {Y Y' : ℕ → ℕ → ℝ} (h : ∀ i ≤ 2, ∀ l ≤ b, Y i l = Y' i l) :
    Gfun p q b Y = Gfun p q b Y' := by
  have h0 : ∀ l ≤ b, rw0 p Y l = rw0 p Y' l := fun l hl => by
    simp only [rw0]; rw [h 0 (by norm_num) l hl, h 1 (by norm_num) l hl, h 2 le_rfl l hl]
  have h1 : ∀ l ≤ b, rw1 p Y l = rw1 p Y' l := fun l hl => by
    simp only [rw1]; rw [h 0 (by norm_num) l hl, h 1 (by norm_num) l hl, h 2 le_rfl l hl]
  have h2 : ∀ l ≤ b, rw2 p Y l = rw2 p Y' l := fun l hl => by
    simp only [rw2]; rw [h 0 (by norm_num) l hl, h 1 (by norm_num) l hl, h 2 le_rfl l hl]
  unfold Gfun
  rw [L1_congr q b h0, L1_congr q b h1, L1_congr q b h2, Zp_congr q b h2 0]

/-! ### The two extremal sign matrices -/

theorem G_Ym {p q : ℝ} (hp : 1 ≤ p) (hq : 2 < q) (b : ℕ) : Gfun p q b Ym = Theta p q b := by
  have hq0 : 0 < q := by linarith
  have r0 : rw0 p Ym = fun l => (-(2 * (p - 1) * (p - 1 + 1))) * sgnv l := by
    funext l
    simp only [rw0, Ym, Mc0, sgnv_one', sgnv_two']
    ring
  have r1 : rw1 p Ym = fun l => (2 * (p - 1) ^ 2) * sgnv l := by
    funext l
    simp only [rw1, Ym, Mc1, sgnv_zero', sgnv_one', sgnv_two']
    ring
  have r2 : rw2 p Ym = fun l => (-((p - 1) ^ 2 + 1)) * sgnv l := by
    funext l
    simp only [rw2, Ym, Mc2, sgnv_zero', sgnv_one', sgnv_two']
    ring
  have hPP : 0 ≤ 2 * (p - 1) * (p - 1 + 1) := by nlinarith
  unfold Gfun Theta
  rw [r0, r1, r2, L1_smul, L1_smul, L1_smul, Zp_smul, Zp_sgnv_zero hq, Tv_last hq0.ne',
    Zp_sgnv_zero hq, abs_neg, abs_of_nonneg hPP, abs_of_nonneg (by positivity), abs_neg,
    abs_of_nonneg (by positivity)]
  have hM : max 0 (-(-((p - 1) ^ 2 + 1) * nu q b)) = ((p - 1) ^ 2 + 1) * nu q b := by
    rw [neg_mul, neg_neg]
    exact max_eq_right (mul_nonneg (by positivity) (nu_nonneg'' hq b))
  rw [hM]
  unfold Dp
  ring

lemma pat_neg {σ Z a Q q C : ℝ} (hσ : σ = 1 ∨ σ = -1) (hq : 0 < q) (hZ : |Z| ≤ C)
    (hC : C ≤ Q * a) : σ * ((Z + Q * (-σ * a)) / q) ≤ 0 := by
  rcases hσ with rfl | rfl
  · have e : (1:ℝ) * ((Z + Q * (-1 * a)) / q) = (Z - Q * a) / q := by ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ hq.le
    linarith [le_abs_self Z]
  · have e : (-1:ℝ) * ((Z + Q * (-(-1) * a)) / q) = (-Z - Q * a) / q := by ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ hq.le
    linarith [neg_abs_le Z]

lemma pat_pos {σ Z a Q q C : ℝ} (hσ : σ = 1 ∨ σ = -1) (hq : 0 < q) (hZ : |Z| ≤ C)
    (hC : C ≤ Q * a) : 0 ≤ σ * ((Z + Q * (-σ * (-a))) / q) := by
  rcases hσ with rfl | rfl
  · have e : (1:ℝ) * ((Z + Q * (-1 * (-a))) / q) = (Z + Q * a) / q := by ring
    rw [e]
    apply div_nonneg _ hq.le
    linarith [neg_abs_le Z]
  · have e : (-1:ℝ) * ((Z + Q * (-(-1) * (-a))) / q) = (-Z + Q * a) / q := by ring
    rw [e]
    apply div_nonneg _ hq.le
    linarith [le_abs_self Z]

/-- A cell with `A = σ a`, `a ≥ 0`, and a state of the opposite sign vanishes. -/
lemma cell_opp_sgn {Q μ σ a Z : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : 0 ≤ a) (hZ : σ * Z ≤ 0)
    (hZa : |Z| ≤ Q * a) : hcell Q μ (σ * a) Z = 0 := by
  rcases hσ with rfl | rfl
  · rw [one_mul] at hZ ⊢
    exact hcell_opp ha (by linarith) (by linarith [neg_abs_le Z])
  · rw [neg_one_mul] at hZ ⊢
    exact hcell_opp' (by linarith) (by linarith) (by linarith [le_abs_self Z])

theorem G_Yp {p q : ℝ} (hPQ : PQok (p - 1) (q - 1)) {b : ℕ} (hb : Even b) (hb2 : 2 ≤ b) :
    Gfun p q b (Yp b) = Theta p q b := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hPP : 0 ≤ 2 * (p - 1) * (p - 1 + 1) := by nlinarith
  have he : 0 ≤ (p - 1) ^ 2 + 1 := by positivity
  have hcol : ∀ l < b, rw0 p (Yp b) l = sgnv l * (2 * (p - 1) * (p - 1 + 1)) ∧
      rw1 p (Yp b) l = sgnv l * (-(2 * (p - 1) ^ 2)) ∧
      rw2 p (Yp b) l = sgnv l * ((p - 1) ^ 2 + 1) := by
    intro l hl
    have h0 : Yp b 0 l = sgnv l := by unfold Yp; rw [if_neg (by omega), sgnv_zero']; ring
    have h1 : Yp b 1 l = -sgnv l := by unfold Yp; rw [if_neg (by omega), sgnv_one']; ring
    have h2 : Yp b 2 l = sgnv l := by unfold Yp; rw [if_neg (by omega), sgnv_two']; ring
    simp only [rw0, rw1, rw2, Mc0, Mc1, Mc2]
    rw [h0, h1, h2]
    exact ⟨by ring, by ring, by ring⟩
  have hlast : rw0 p (Yp b) b = 0 ∧ rw1 p (Yp b) b = -(2 * (p - 1) * (p - 1 + 1)) ∧
      rw2 p (Yp b) b = (p - 1) ^ 2 - 1 := by
    have h0 : Yp b 0 b = 1 := by
      unfold Yp; rw [if_neg (by omega), sgnv_zero', sgnv_of_even hb]; ring
    have h1 : Yp b 1 b = -1 := by
      unfold Yp; rw [if_neg (by omega), sgnv_one', sgnv_of_even hb]; ring
    have h2 : Yp b 2 b = -1 := by unfold Yp; rw [if_pos ⟨rfl, rfl⟩]
    simp only [rw0, rw1, rw2]
    rw [h0, h1, h2]
    exact col_C (p - 1)
  have hY : SignMat b (Yp b) := by
    intro i hi l hl
    unfold Yp
    split_ifs
    · right; rfl
    · rcases sgnv_cases i with a | a <;> rcases sgnv_cases l with c | c <;> rw [a, c] <;> norm_num
  -- the sign pattern of the states
  have hpat : ∀ j < b, sgnv j * Zp q b (rw0 p (Yp b)) (j + 1) ≤ 0 ∧
      0 ≤ sgnv j * Zp q b (rw1 p (Yp b)) (j + 1) ∧ sgnv j * Zp q b (rw2 p (Yp b)) (j + 1) ≤ 0 := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) b with hj1 | hj1
    · obtain ⟨b0, b1, b2⟩ := Z_bounds (p := p) (q := q) (by linarith) (by linarith) hY
        (show j + 1 + 1 ≤ b by omega)
      obtain ⟨c0, c1, c2⟩ := hcol (j + 1) hj1
      have hs : sgnv (j + 1) = -sgnv j := sgnv_succ j
      rw [Zp_rec hq0.ne' b (rw0 p (Yp b)) hj1, Zp_rec hq0.ne' b (rw1 p (Yp b)) hj1,
        Zp_rec hq0.ne' b (rw2 p (Yp b)) hj1, c0, c1, c2, hs]
      refine ⟨pat_neg (sgnv_cases j) hq0 b0 ?_, pat_pos (sgnv_cases j) hq0 b1 ?_,
        pat_neg (sgnv_cases j) hq0 b2 ?_⟩
      · nlinarith
      · nlinarith
      · nlinarith [sq_nonneg (p - 1 - 1), mul_le_mul_of_nonneg_right hQ he]
    · have hjb : j + 1 = b := by omega
      obtain ⟨l0, l1, l2⟩ := hlast
      rw [hjb, Zp_self, Zp_self, Zp_self, l0, l1, l2, show j = b - 1 by omega,
        sgnv_pred hb (by omega)]
      refine ⟨by norm_num, by nlinarith, by nlinarith⟩
  -- all cells vanish
  have hS0 : ∀ k ∈ range b, ScY p q b (Yp b) k = 0 := by
    intro k hk
    rw [mem_range] at hk
    obtain ⟨b0, b1, b2⟩ := Z_bounds (p := p) (q := q) (by linarith) (by linarith) hY
      (show k + 1 ≤ b by omega)
    obtain ⟨c0, c1, c2⟩ := hcol k hk
    obtain ⟨p0, p1, p2⟩ := hpat k hk
    have hσ := sgnv_cases k
    have habs : |sgnv k| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have a0 : |sgnv k * (2 * (p - 1) * (p - 1 + 1))| = 2 * (p - 1) * (p - 1 + 1) := by
      rw [abs_mul, habs, one_mul, abs_of_nonneg hPP]
    have a1 : |sgnv k * -(2 * (p - 1) ^ 2)| = 2 * (p - 1) ^ 2 := by
      rw [abs_mul, habs, one_mul, abs_neg, abs_of_nonneg (by positivity)]
    have a2 : |sgnv k * ((p - 1) ^ 2 + 1)| = (p - 1) ^ 2 + 1 := by
      rw [abs_mul, habs, one_mul, abs_of_nonneg he]
    unfold ScY Sc
    rw [c0, c1, c2, a0, a1, a2]
    have k0 : hcell (q - 1) (nu q k) (sgnv k * (2 * (p - 1) * (p - 1 + 1)))
        (Zp q b (rw0 p (Yp b)) (k + 1)) = 0 :=
      cell_opp_sgn hσ hPP p0 (by nlinarith)
    have k1 : hcell (q - 1) (nu q k) (sgnv k * (-(2 * (p - 1) ^ 2)))
        (Zp q b (rw1 p (Yp b)) (k + 1)) = 0 := by
      have e : sgnv k * -(2 * (p - 1) ^ 2) = (-sgnv k) * (2 * (p - 1) ^ 2) := by ring
      rw [e]
      have hσ' : -sgnv k = 1 ∨ -sgnv k = -1 := by
        rcases hσ with h | h <;> rw [h] <;> norm_num
      exact cell_opp_sgn hσ' (by positivity) (by nlinarith) (by nlinarith)
    have k2 : hcell (q - 1) (nu q k) (sgnv k * ((p - 1) ^ 2 + 1))
        (Zp q b (rw2 p (Yp b)) (k + 1)) = 0 :=
      cell_opp_sgn hσ he p2 (by nlinarith [sq_nonneg (p - 1 - 1),
        mul_le_mul_of_nonneg_right hQ he])
    rw [k0, k1, k2]
    unfold Dp
    ring
  have hM : max 0 (-(Zp q b (rw2 p (Yp b)) 0)) = 0 := by
    apply max_eq_left
    obtain ⟨b0, b1, b2⟩ := Z_bounds (p := p) (q := q) (by linarith) (by linarith) hY
      (show 1 ≤ b by omega)
    obtain ⟨c0, c1, c2⟩ := hcol 0 (by omega)
    rw [Zp_rec hq0.ne' b _ (show 0 < b by omega), c2, sgnv_zero', one_mul]
    have : 0 ≤ (Zp q b (rw2 p (Yp b)) (0 + 1) + (q - 1) * ((p - 1) ^ 2 + 1)) / q := by
      apply div_nonneg _ hq0.le
      nlinarith [neg_abs_le (Zp q b (rw2 p (Yp b)) (0 + 1)), sq_nonneg (p - 1 - 1),
        mul_le_mul_of_nonneg_right hQ he]
    linarith
  have key := prop1 (p := p) hq b (Yp b)
  obtain ⟨l0, l1, l2⟩ := hlast
  rw [Finset.sum_eq_zero hS0, hM, l0, l1, l2, abs_zero, abs_neg, abs_of_nonneg hPP,
    abs_of_nonneg (by nlinarith)] at key
  unfold Dp at key
  have : Theta p q b - Gfun p q b (Yp b) = 0 := by rw [key]; ring
  linarith

/-- **Theorem B′.**  For real `(p ≥ 5, q ≥ 3)` or `(p = 3, q ≥ 5)`, even `b ≥ 2` and every sign
matrix `Y` on `{0,1,2} × {0,…,b}` with `Y_{2b} = -1`: `G(Y) ≤ Θ = d₂(p) d_b(q) - 2 δ₂(p) δ_b(q)`,
with equality iff `Y = Y⁻ = -s₂ sᵀ` or `Y = Y⁺ = s₂ sᵀ - 2 e₂ e_bᵀ` (on the box). -/
theorem thmB' {p q : ℝ} (hpq : ParamB p q) {b : ℕ} (hb : Even b) (hb2 : 2 ≤ b)
    {Y : ℕ → ℕ → ℝ} (hY : SignMat b Y) (hc : Y 2 b = -1) :
    Gfun p q b Y ≤ Theta p q b ∧
      (Gfun p q b Y = Theta p q b ↔
        (∀ i ≤ 2, ∀ l ≤ b, Y i l = Ym i l) ∨ (∀ i ≤ 2, ∀ l ≤ b, Y i l = Yp b i l)) := by
  have hPQ := hpq.pq
  obtain ⟨hP, hQ⟩ := hPQ.two
  obtain ⟨hle, himp⟩ := thmB'_main hPQ hb hb2 hY hc
  refine ⟨hle, ⟨himp, ?_⟩⟩
  rintro (h | h)
  · rw [Gfun_congr h, G_Ym (by linarith) (by linarith) b]
  · rw [Gfun_congr h, G_Yp hPQ hb hb2]

/-! ### The graph: `2E = G(Y) + n` for `n = p² q^b` -/

set_option linter.unnecessarySeqFocus false in
lemma Tent_two (x : ℝ) :
    Tent x 2 0 0 = 0 ∧ Tent x 2 0 1 = -(x * (x - 1)) ∧ Tent x 2 0 2 = x * (x - 1) ∧
    Tent x 2 1 0 = -(x * (x - 1)) ∧ Tent x 2 1 1 = (x - 1) * (x - 1) ∧ Tent x 2 1 2 = x - 1 ∧
    Tent x 2 2 0 = x * (x - 1) ∧ Tent x 2 2 1 = x - 1 ∧ Tent x 2 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Tent, phiX, ramX] <;> ring

lemma Mentry_rows2 (p q : ℝ) (b : ℕ) (Y : ℕ → ℕ → ℝ) (v : ℕ) :
    Mentry p q 2 b Y 0 v = Tv q b (rw0 p Y) v ∧ Mentry p q 2 b Y 1 v = Tv q b (rw1 p Y) v ∧
      Mentry p q 2 b Y 2 v = Tv q b (rw2 p Y) v := by
  obtain ⟨t00, t01, t02, t10, t11, t12, t20, t21, t22⟩ := Tent_two p
  have hsum : ∀ u : ℕ, Mentry p q 2 b Y u v =
      Tent p 2 u 0 * Tv q b (Y 0) v + Tent p 2 u 1 * Tv q b (Y 1) v +
        Tent p 2 u 2 * Tv q b (Y 2) v := by
    intro u
    rw [Mentry_eq]
    unfold Tv
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hlin : ∀ α β γ : ℝ, α * Tv q b (Y 0) v + β * Tv q b (Y 1) v + γ * Tv q b (Y 2) v =
      Tv q b (fun l => α * Y 0 l + β * Y 1 l + γ * Y 2 l) v := by
    intro α β γ
    unfold Tv
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, t00, t01, t02, hlin]
    unfold Tv
    apply Finset.sum_congr rfl
    intro l _
    simp only [rw0, Mc0]
    ring
  · rw [hsum, t10, t11, t12, hlin]
    unfold Tv
    apply Finset.sum_congr rfl
    intro l _
    simp only [rw1, Mc1]
    ring
  · rw [hsum, t20, t21, t22, hlin]
    unfold Tv
    apply Finset.sum_congr rfl
    intro l _
    simp only [rw2, Mc2]
    ring

/-- `2 ‖T₂(p) X T_b(q)ᵀ‖₁ = G(2X - J) + p² q^b` for a `0/1` matrix `X`. -/
theorem two_L1mat_rows2 {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q) (b : ℕ) (X : ℕ → ℕ → ℝ)
    (hX : ∀ i ≤ 2, ∀ l ≤ b, X i l = 0 ∨ X i l = 1) :
    2 * L1mat p q 2 b X = Gfun p q b (fun c e => 2 * X c e - 1) + p ^ 2 * q ^ b := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  set Y : ℕ → ℕ → ℝ := fun c e => 2 * X c e - 1 with hY
  have hYs : SignMat b Y := by
    intro i hi l hl
    rcases hX i hi l hl with h | h
    · right; simp only [hY, h]; norm_num
    · left; simp only [hY, h]; norm_num
  rw [two_L1mat]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hrow : ∀ u, u < 2 → ∀ w : ℕ → ℝ, (∀ v, Mentry p q 2 b Y u v = Tv q b w v) →
      ∑ v ∈ range (b + 1), |Mentry p q 2 b Y u v + Mentry p q 2 b (fun _ _ => 1) u v| =
        L1 q b w := by
    intro u hu w hw
    unfold L1
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_range] at hv
    rw [Mentry_ones hp0.ne' hq0.ne' 2 b (by omega) (by omega), if_neg (by omega), add_zero, hw]
  rw [hrow 0 (by norm_num) (rw0 p Y) (fun v => (Mentry_rows2 p q b Y v).1),
    hrow 1 (by norm_num) (rw1 p Y) (fun v => (Mentry_rows2 p q b Y v).2.1)]
  -- row 2
  have hZ0 : |Zp q b (rw2 p Y) 0| ≤ (p - 1 + 1) ^ 2 :=
    (Z_bounds (p := p) (q := q) hp hq.le hYs (Nat.zero_le _)).2.2
  have hrow2 : ∑ v ∈ range (b + 1), |Mentry p q 2 b Y 2 v + Mentry p q 2 b (fun _ _ => 1) 2 v| =
      L1 q b (rw2 p Y) - 2 * q ^ b * max 0 (-(Zp q b (rw2 p Y) 0)) + p ^ 2 * q ^ b := by
    unfold L1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hrest : ∑ v ∈ range b, |Mentry p q 2 b Y 2 v + Mentry p q 2 b (fun _ _ => 1) 2 v| =
        ∑ v ∈ range b, |Tv q b (rw2 p Y) v| := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_range] at hv
      rw [Mentry_ones hp0.ne' hq0.ne' 2 b le_rfl (by omega), if_neg (by omega), add_zero,
        (Mentry_rows2 p q b Y v).2.2]
    rw [hrest, Mentry_ones hp0.ne' hq0.ne' 2 b le_rfl le_rfl, if_pos ⟨rfl, rfl⟩,
      (Mentry_rows2 p q b Y b).2.2, Tv_last hq0.ne']
    set Z := Zp q b (rw2 p Y) 0 with hZ
    have hqm := pow_pos hq0 b
    have hZp : -(p ^ 2) ≤ Z := by
      have := neg_abs_le Z
      have e : (p - 1 + 1) ^ 2 = p ^ 2 := by ring
      rw [e] at hZ0
      linarith
    have hnn : 0 ≤ q ^ b * Z + p ^ 2 * q ^ b := by nlinarith
    rw [abs_of_nonneg hnn, abs_mul, abs_of_pos hqm]
    rcases le_or_gt 0 Z with hz | hz
    · rw [max_eq_left (by linarith), abs_of_nonneg hz]
      ring
    · rw [max_eq_right (by linarith), abs_of_neg hz]
      ring
  rw [hrow2]
  unfold Gfun
  ring

/-! ### The divisor sets -/

variable {p q : ℕ}

/-- `D⁺ \ {n}` for `n = p² q^b`. -/
def DtruncB (p q b : ℕ) : Finset ℕ := (DstarPQ p q 2 b).erase (p ^ 2 * q ^ b)

lemma DtruncB_subset (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℕ) :
    DtruncB p q b ⊆ (p ^ 2 * q ^ b).properDivisors := by
  intro x hx
  unfold DtruncB at hx
  rw [Finset.mem_erase] at hx
  obtain ⟨hxn, hxs⟩ := hx
  obtain ⟨i, hi, j, hj, _, rfl⟩ := mem_DstarPQ_iff.mp hxs
  rw [Nat.mem_properDivisors]
  have hdvd : p ^ i * q ^ j ∣ p ^ 2 * q ^ b := (pq_dvd_iff hp hq hpq).mpr ⟨hi, hj⟩
  have hpos : 0 < p ^ 2 * q ^ b := by
    have := hp.pos
    have := hq.pos
    positivity
  exact ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) hxn⟩

lemma sign_of_mem {D : Finset ℕ} {x : ℕ} :
    2 * (if x ∈ D then (1 : ℝ) else 0) - 1 = if x ∈ D then 1 else -1 := by
  split_ifs <;> norm_num

lemma Ym_eq (c e : ℕ) : Ym c e = if Odd (c + e) then 1 else -1 := by
  unfold Ym
  rw [sgnv_mul]
  by_cases h : Even (c + e)
  · rw [if_pos h, if_neg (Nat.not_odd_iff_even.mpr h)]
  · rw [if_neg h, if_pos (Nat.not_even_iff_odd.mp h)]
    norm_num

lemma Yp_eq {b : ℕ} (c e : ℕ) :
    Yp b c e = if (Even (c + e) ∧ ¬ (c = 2 ∧ e = b)) then 1 else -1 := by
  unfold Yp
  by_cases h2 : c = 2 ∧ e = b
  · rw [if_pos h2, if_neg (fun h => h.2 h2)]
  · rw [if_neg h2, sgnv_mul]
    by_cases h : Even (c + e)
    · rw [if_pos h, if_pos ⟨h, h2⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]

lemma anti_sign (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {b : ℕ} :
    ∀ i ≤ 2, ∀ l ≤ b,
      2 * (if p ^ i * q ^ l ∈ DantiPQ p q 2 b then (1 : ℝ) else 0) - 1 = Ym i l := by
  intro i hi l hl
  rw [sign_of_mem, Ym_eq]
  by_cases h : Odd (i + l)
  · rw [if_pos ((pq_mem_DantiPQ hp hq hpq hi hl).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((pq_mem_DantiPQ hp hq hpq hi hl).mp h')), if_neg h]

lemma trunc_sign (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {b : ℕ} :
    ∀ i ≤ 2, ∀ l ≤ b,
      2 * (if p ^ i * q ^ l ∈ DtruncB p q b then (1 : ℝ) else 0) - 1 = Yp b i l := by
  intro i hi l hl
  have hmem : p ^ i * q ^ l ∈ DtruncB p q b ↔ (Even (i + l) ∧ ¬ (i = 2 ∧ l = b)) := by
    unfold DtruncB
    rw [Finset.mem_erase, pq_mem_DstarPQ hp hq hpq hi hl]
    constructor
    · rintro ⟨hne, hev⟩
      exact ⟨hev, fun h => hne (by rw [h.1, h.2])⟩
    · rintro ⟨hev, hce⟩
      exact ⟨fun h => hce ((pq_inj hp hq hpq).mp h), hev⟩
  rw [sign_of_mem, Yp_eq]
  by_cases h : Even (i + l) ∧ ¬ (i = 2 ∧ l = b)
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]

lemma paramB_of_primes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) :
    ParamB (p : ℝ) (q : ℝ) := by
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · have hp3' : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3'
    have hq5 : 5 ≤ q := by
      rcases Nat.lt_or_ge q 5 with h | h
      · interval_cases q
        · exact absurd rfl hpq
        · exact absurd hq (by norm_num)
      · exact h
    right
    exact ⟨by norm_num, by exact_mod_cast hq5⟩
  · left
    exact ⟨by exact_mod_cast hp5, by exact_mod_cast hq3⟩

section Energy

variable (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q)
include hp hq hpq hp3 hq3

/-- `2 E(ICG_n(D)) = G(Y_D) + n` for `n = p² q^b`. -/
lemma two_energy (b : ℕ) (D : Finset ℕ) :
    2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) =
      Gfun p q b (fun c e => 2 * (if p ^ c * q ^ e ∈ D then (1 : ℝ) else 0) - 1) +
        (p : ℝ) ^ 2 * (q : ℝ) ^ b := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  rw [energy_icgAdj_pq p q 2 b hp hq hpq]
  exact two_L1mat_rows2 (by linarith) (by linarith) b _
    (fun i _ l _ => by split_ifs <;> simp)

end Energy

lemma sign_mat_of (b : ℕ) (D : Finset ℕ) :
    SignMat b (fun c e => 2 * (if p ^ c * q ^ e ∈ D then (1 : ℝ) else 0) - 1) := by
  intro i _ l _
  dsimp only
  split_ifs
  · left; norm_num
  · right; norm_num

/-- **Theorem B.**  Let `p, q` be distinct odd primes, `b ≥ 2` even, `n = p² q^b`.  Every set `D`
of proper divisors of `n` satisfies
`E(ICG_n(D)) ≤ ½ [n + (5p² - 8p + 4) d_b(q)] - (p² - 2p + 2) δ_b(q)`
(`d_b(q) = ‖T_b(q) s‖₁`, `δ_b(q) = (T_b(q) s)_b`), with equality iff `D = D⁻ = {p^i q^j : i + j odd}`
or `D = D⁺ \ {n}`, `D⁺ = {p^i q^j : i + j even}`. -/
theorem theoremB (p q b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hb : Even b) (hb2 : 2 ≤ b) (D : Finset ℕ)
    (hD : D ⊆ (p ^ 2 * q ^ b).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((p : ℝ) ^ 2 * (q : ℝ) ^ b + (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv) / 2 -
          ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b ∧
      (ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) =
          ((p : ℝ) ^ 2 * (q : ℝ) ^ b + (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv) / 2 -
            ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b ↔
        D = DantiPQ p q 2 b ∨ D = DtruncB p q b) := by
  have hpq' := paramB_of_primes hp hq hpq hp3 hq3
  have hE := two_energy hp hq hpq hp3 hq3 b D
  set Y : ℕ → ℕ → ℝ := fun c e => 2 * (if p ^ c * q ^ e ∈ D then (1 : ℝ) else 0) - 1 with hYdef
  have hnot : p ^ 2 * q ^ b ∉ D := by
    intro hmem
    exact lt_irrefl _ (Nat.mem_properDivisors.mp (hD hmem)).2
  have hc : Y 2 b = -1 := by
    simp only [hYdef]
    rw [if_neg hnot]
    norm_num
  obtain ⟨hle, hiff⟩ := thmB' hpq' hb hb2 (sign_mat_of b D) hc
  have hTheta : Theta p q b = (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv -
      2 * ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b := by
    unfold Theta Dp
    ring
  rw [hTheta] at hle hiff
  have hrep : ∀ x ∈ D, ∃ c ≤ 2, ∃ e ≤ b, x = p ^ c * q ^ e := fun x hx =>
    pq_dvd_rep hp hq (Nat.mem_properDivisors.mp (hD hx)).1
  have hmemY : ∀ c ≤ 2, ∀ e ≤ b, (p ^ c * q ^ e ∈ D ↔ Y c e = 1) := by
    intro c _ e _
    simp only [hYdef]
    constructor
    · intro h; rw [if_pos h]; norm_num
    · intro h
      by_contra hn
      rw [if_neg hn] at h
      norm_num at h
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have hG : Gfun p q b Y = (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv -
        2 * ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b := by linarith
    rcases hiff.mp hG with h | h
    · left
      have hiff' : ∀ c ≤ 2, ∀ e ≤ b, p ^ c * q ^ e ∈ D ↔ Odd (c + e) := by
        intro c hc e he
        have h' : Y c e = Ym c e := h c hc e he
        rw [hmemY c hc e he, h', Ym_eq]
        split_ifs with ho
        · exact ⟨fun _ => ho, fun _ => rfl⟩
        · exact ⟨fun h => by norm_num at h, fun h => absurd h ho⟩
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, e, he, rfl⟩ := hrep x hx
        exact (pq_mem_DantiPQ hp hq hpq hc he).mpr ((hiff' c hc e he).mp hx)
      · intro hx
        obtain ⟨i, hi, j, hj, hodd, rfl⟩ := mem_DantiPQ_iff.mp hx
        exact (hiff' i hi j hj).mpr hodd
    · right
      have hiff' : ∀ c ≤ 2, ∀ e ≤ b,
          p ^ c * q ^ e ∈ D ↔ (Even (c + e) ∧ ¬ (c = 2 ∧ e = b)) := by
        intro c hc e he
        have h' : Y c e = Yp b c e := h c hc e he
        rw [hmemY c hc e he, h', Yp_eq]
        split_ifs with ho
        · exact ⟨fun _ => ho, fun _ => rfl⟩
        · exact ⟨fun h => by norm_num at h, fun h => absurd h ho⟩
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, e, he, rfl⟩ := hrep x hx
        obtain ⟨hev, hce⟩ := (hiff' c hc e he).mp hx
        unfold DtruncB
        rw [Finset.mem_erase]
        refine ⟨?_, (pq_mem_DstarPQ hp hq hpq hc he).mpr hev⟩
        intro h
        exact hce ((pq_inj hp hq hpq).mp h)
      · intro hx
        unfold DtruncB at hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hxn, hxs⟩ := hx
        obtain ⟨i, hi, j, hj, hev, rfl⟩ := mem_DstarPQ_iff.mp hxs
        refine (hiff' i hi j hj).mpr ⟨hev, ?_⟩
        rintro ⟨rfl, rfl⟩
        exact hxn rfl
  · rintro (rfl | rfl)
    · have hG : Gfun p q b Y = (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv -
          2 * ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b :=
        hiff.mpr (Or.inl (anti_sign hp hq hpq))
      linarith
    · have hG : Gfun p q b Y = (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv -
          2 * ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b :=
        hiff.mpr (Or.inr (trunc_sign hp hq hpq))
      linarith

/-- **Theorem B** in the format of `ICGEqualParity.corollaryA`: both `D⁻` and `D⁺ \ {n}` are
admissible, `2E(D⁻) = n + (5p² - 8p + 4) d_b(q) - 2(p² - 2p + 2) δ_b(q)`, `E(D⁺ \ {n}) = E(D⁻)`,
and every admissible `D` has `E(D) ≤ E(D⁻)`, with equality only for these two sets. -/
theorem corollaryB (p q b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hb : Even b) (hb2 : 2 ≤ b) :
    DantiPQ p q 2 b ⊆ (p ^ 2 * q ^ b).properDivisors ∧
      DtruncB p q b ⊆ (p ^ 2 * q ^ b).properDivisors ∧
      2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) (DantiPQ p q 2 b))
          (ICGBridge.icgAdj_isHermitian _ _) =
        (p : ℝ) ^ 2 * (q : ℝ) ^ b + (5 * (p : ℝ) ^ 2 - 8 * p + 4) * L1 q b sgnv -
          2 * ((p : ℝ) ^ 2 - 2 * p + 2) * Tv q b sgnv b ∧
      ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) (DtruncB p q b))
          (ICGBridge.icgAdj_isHermitian _ _) =
        ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) (DantiPQ p q 2 b))
          (ICGBridge.icgAdj_isHermitian _ _) ∧
      ∀ D : Finset ℕ, D ⊆ (p ^ 2 * q ^ b).properDivisors →
        ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) ≤
          ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) (DantiPQ p q 2 b))
            (ICGBridge.icgAdj_isHermitian _ _) ∧
        (ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) =
          ICGBridge.energy (ICGBridge.icgAdj (p ^ 2 * q ^ b) (DantiPQ p q 2 b))
            (ICGBridge.icgAdj_isHermitian _ _) → D = DantiPQ p q 2 b ∨ D = DtruncB p q b) := by
  have hev : Even (2 + b) := by obtain ⟨r, hr⟩ := hb; exact ⟨r + 1, by omega⟩
  have hA := DantiPQ_subset hp hq hpq hev
  have hT := DtruncB_subset hp hq hpq b
  have eA := (theoremB p q b hp hq hpq hp3 hq3 hb hb2 _ hA).2.mpr (Or.inl rfl)
  have eT := (theoremB p q b hp hq hpq hp3 hq3 hb hb2 _ hT).2.mpr (Or.inr rfl)
  refine ⟨hA, hT, by rw [eA]; ring, by rw [eT, eA], ?_⟩
  intro D hD
  obtain ⟨hle, hiff⟩ := theoremB p q b hp hq hpq hp3 hq3 hb hb2 D hD
  refine ⟨by rw [eA]; exact hle, fun h => hiff.mp (by rw [h, eA])⟩

/-! ### Exchange of the primes: `n = p^b q²` -/

lemma DantiPQ_swap (p q a b : ℕ) : DantiPQ q p a b = DantiPQ p q b a := by
  ext x
  rw [mem_DantiPQ_iff (p := q) (q := p), mem_DantiPQ_iff (p := p) (q := q)]
  constructor
  · rintro ⟨i, hi, j, hj, hodd, rfl⟩
    exact ⟨j, hj, i, hi, by rwa [add_comm], mul_comm _ _⟩
  · rintro ⟨i, hi, j, hj, hodd, rfl⟩
    exact ⟨j, hj, i, hi, by rwa [add_comm], mul_comm _ _⟩

lemma DstarPQ_swap (p q a b : ℕ) : DstarPQ q p a b = DstarPQ p q b a := by
  ext x
  rw [mem_DstarPQ_iff (p := q) (q := p), mem_DstarPQ_iff (p := p) (q := q)]
  constructor
  · rintro ⟨i, hi, j, hj, hodd, rfl⟩
    exact ⟨j, hj, i, hi, by rwa [add_comm], mul_comm _ _⟩
  · rintro ⟨i, hi, j, hj, hodd, rfl⟩
    exact ⟨j, hj, i, hi, by rwa [add_comm], mul_comm _ _⟩

/-- **Theorem B, exchanged primes.**  For distinct odd primes `p, q`, even `b ≥ 2` and
`n = p^b q²`: every set `D` of proper divisors of `n` has
`E(ICG_n(D)) ≤ ½ [n + (5q² - 8q + 4) d_b(p)] - (q² - 2q + 2) δ_b(p)`, with equality iff
`D = {p^i q^j : i + j odd}` or `D = {p^i q^j : i + j even} \ {n}`. -/
theorem theoremB_swap (p q b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hb : Even b) (hb2 : 2 ≤ b) (D : Finset ℕ)
    (hD : D ⊆ (p ^ b * q ^ 2).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ b * q ^ 2) D) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((p : ℝ) ^ b * (q : ℝ) ^ 2 + (5 * (q : ℝ) ^ 2 - 8 * q + 4) * L1 p b sgnv) / 2 -
          ((q : ℝ) ^ 2 - 2 * q + 2) * Tv p b sgnv b ∧
      (ICGBridge.energy (ICGBridge.icgAdj (p ^ b * q ^ 2) D) (ICGBridge.icgAdj_isHermitian _ _) =
          ((p : ℝ) ^ b * (q : ℝ) ^ 2 + (5 * (q : ℝ) ^ 2 - 8 * q + 4) * L1 p b sgnv) / 2 -
            ((q : ℝ) ^ 2 - 2 * q + 2) * Tv p b sgnv b ↔
        D = DantiPQ p q b 2 ∨ D = (DstarPQ p q b 2).erase (p ^ b * q ^ 2)) := by
  have hn : p ^ b * q ^ 2 = q ^ 2 * p ^ b := mul_comm _ _
  rw [hn] at hD ⊢
  have h := theoremB q p b hq hp (Ne.symm hpq) hq3 hp3 hb hb2 D hD
  unfold DtruncB at h
  rw [DantiPQ_swap, DstarPQ_swap] at h
  have e : (q : ℝ) ^ 2 * (p : ℝ) ^ b = (p : ℝ) ^ b * (q : ℝ) ^ 2 := mul_comm _ _
  rw [e] at h
  exact h

end ICGEqualParityB
