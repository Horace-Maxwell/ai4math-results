import Mathlib
import Research.ICGEqualParityBFD

set_option autoImplicit false

/-!
# Theorem B′ (round 6): the sign-matrix form for `T₂(p) Y T_b(q)ᵀ`, `b` even

Formalisation of §1 (Proposition 1) and §5 (proof of Theorem B′, Lemma EQ) of
`work/round6/equal-parity-a2/PROOF.md`.  `Y : ℕ → ℕ → ℝ` is a sign matrix on
`{0,1,2} × {0,…,b}`; `rw0/rw1/rw2 p Y` are the rows of `T₂(p) Y`, so the rows of
`Z = T₂(p) Y T_b(q)ᵀ` are `T_b(q) (rwᵢ p Y)` and

  `Gfun p q b Y = Σ_{(i,j) ≠ (2,b)} |Z_ij| + Z_{2b}`   (`= 2E - n` for the sign matrix of `D`),
  `Theta p q b = d₂(p) d_b(q) - 2 δ₂(p) δ_b(q)`.

* `prop1` (Proposition 1): `Θ - G = q^b (Σ_{k<b} s_k + ρ Δ(c_b) + κ - 2 δ₂(p) ρ)`.
* `thmB'` (**Theorem B′**): for `(p ≥ 5, q ≥ 3)` or `(p = 3, q ≥ 5)` real, `b ≥ 2` even and
  `Y_{2b} = -1`: `G(Y) ≤ Θ`, with equality iff `Y = Y⁻ = -s₂ sᵀ` or `Y = Y⁺ = s₂ sᵀ - 2 e₂ e_bᵀ`.
-/

noncomputable section

namespace ICGEqualParityB

open Finset ICGGeneral ICGEqualParity

/-! ### Sign vectors and the potential -/

lemma sgnv_mul_self (l : ℕ) : sgnv l * sgnv l = 1 := by
  unfold sgnv
  rw [← pow_add]
  exact Even.neg_one_pow ⟨l, rfl⟩

lemma sgnv_cases (l : ℕ) : sgnv l = 1 ∨ sgnv l = -1 := neg_one_pow_eq_or ℝ l

lemma sgnv_of_even {b : ℕ} (hb : Even b) : sgnv b = 1 := by
  unfold sgnv
  exact hb.neg_one_pow

lemma sgnv_pred {b : ℕ} (hb : Even b) (hb1 : 1 ≤ b) : sgnv (b - 1) = -1 := by
  have h := sgnv_succ (b - 1)
  rw [show b - 1 + 1 = b by omega, sgnv_of_even hb] at h
  linarith

lemma sgnv_zero' : sgnv 0 = 1 := by simp [sgnv]
lemma sgnv_one' : sgnv 1 = -1 := by simp [sgnv]
lemma sgnv_two' : sgnv 2 = 1 := by simp [sgnv]

lemma Mc_neg (P c0 c1 c2 : ℝ) :
    Mc0 P (-c0) (-c1) (-c2) = -Mc0 P c0 c1 c2 ∧ Mc1 P (-c0) (-c1) (-c2) = -Mc1 P c0 c1 c2 ∧
      Mc2 P (-c0) (-c1) (-c2) = -Mc2 P c0 c1 c2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma Zp_smul (x : ℝ) (m : ℕ) (c : ℝ) (w : ℕ → ℝ) (k : ℕ) :
    Zp x m (fun l => c * w l) k = c * Zp x m w k := by
  unfold Zp Wp
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Zp_sgnv_eq {x : ℝ} (hx : 2 < x) {m j : ℕ} (hj : j ≤ m) :
    Zp x m sgnv j = sgnv j * nu x (m - j) := by
  have h1 := Zp_alt_tail hx.le (sgnv_isSign m) (m - j) j (by omega) (by
    intro i _ _ h
    rw [sgnv_succ] at h
    have h0 : sgnv i ≠ 0 := by simp [sgnv]
    exact h0 (by linarith))
  have h2 := Zp_abs_eq hx.le (sgnv_isSign m) hj
  calc Zp x m sgnv j = sgnv j * (sgnv j * Zp x m sgnv j) := by
        rw [← mul_assoc, sgnv_mul_self, one_mul]
    _ = sgnv j * nu x (m - j) := by rw [← h2, h1]

lemma nu_rec' {q : ℝ} (hq : 0 < q) (k : ℕ) : (q - 1 + 1) * nu q (k + 1) = q - 1 - nu q k := by
  rw [nu_succ]
  field_simp
  ring

lemma nu_lo' {q : ℝ} (hq : 2 < q) (k : ℕ) : q - 1 - 1 ≤ (q - 1 + 1) * nu q k := by
  have h := (nu_bounds hq.le k).1
  rw [div_le_iff₀ (by linarith)] at h
  linarith

lemma nu_nonneg'' {q : ℝ} (hq : 2 < q) (k : ℕ) : 0 ≤ nu q k := (nu_pos hq k).le

lemma nu_two_eq {q : ℝ} (hq : 0 < q) : q ^ 2 * nu q 2 = (q - 1) ^ 2 + 1 := by
  rw [nu_succ, nu_succ, nu_zero]
  field_simp
  ring

lemma nu_le_two {q : ℝ} (hq : 2 < q) {k : ℕ} (hk : 1 ≤ k) : nu q k ≤ nu q 2 := by
  rcases Nat.even_or_odd k with he | ho
  · exact nu_even_le_two (by linarith) he (by obtain ⟨r, hr⟩ := he; omega)
  · have h1 := nu_odd_lt (by linarith : (1:ℝ) < q) ho
    have h2 := nu_even_gt (by linarith : (1:ℝ) < q) (even_two : Even 2)
    linarith

lemma nu_hi' {q : ℝ} (hq : 2 < q) {k : ℕ} (hk : 1 ≤ k) :
    (q - 1 + 1) ^ 2 * nu q k ≤ (q - 1) ^ 2 + 1 := by
  have h1 := nu_le_two hq hk
  have h2 := nu_two_eq (q := q) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg q)
  rw [show q - 1 + 1 = q by ring]
  linarith

lemma nu_gtL' {q : ℝ} (hq : 2 < q) {k : ℕ} (hk : Even k) : q - 1 < (q - 1 + 2) * nu q k := by
  have h := nu_even_gt (by linarith : (1:ℝ) < q) hk
  rw [div_lt_iff₀ (by linarith)] at h
  linarith

/-! ### Rows, `G`, `Θ` and the column surplus -/

/-- Rows of `T₂(p) Y` (with `P = p - 1`). -/
def rw0 (p : ℝ) (Y : ℕ → ℕ → ℝ) (l : ℕ) : ℝ := Mc0 (p - 1) (Y 0 l) (Y 1 l) (Y 2 l)
/-- Row `1` of `T₂(p) Y`. -/
def rw1 (p : ℝ) (Y : ℕ → ℕ → ℝ) (l : ℕ) : ℝ := Mc1 (p - 1) (Y 0 l) (Y 1 l) (Y 2 l)
/-- Row `2` of `T₂(p) Y`. -/
def rw2 (p : ℝ) (Y : ℕ → ℕ → ℝ) (l : ℕ) : ℝ := Mc2 (p - 1) (Y 0 l) (Y 1 l) (Y 2 l)

/-- `G(Y) = Σ_{(i,j) ≠ (2,b)} |Z_ij| + Z_{2b}`, `Z = T₂(p) Y T_b(q)ᵀ`. -/
def Gfun (p q : ℝ) (b : ℕ) (Y : ℕ → ℕ → ℝ) : ℝ :=
  L1 q b (rw0 p Y) + L1 q b (rw1 p Y) + L1 q b (rw2 p Y) -
    2 * q ^ b * max 0 (-(Zp q b (rw2 p Y) 0))

/-- `Θ = d₂(p) d_b(q) - 2 δ₂(p) δ_b(q)` with `d_b(q) = L1 q b sgnv`, `δ_b(q) = Tv q b sgnv b`. -/
def Theta (p q : ℝ) (b : ℕ) : ℝ :=
  Dp (p - 1) * L1 q b sgnv - 2 * ((p - 1) ^ 2 + 1) * Tv q b sgnv b

/-- `q` times the surplus `s_k` of column `k`. -/
def ScY (p q : ℝ) (b : ℕ) (Y : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  Sc (p - 1) (q - 1) (nu q k) (rw0 p Y k) (rw1 p Y k) (rw2 p Y k)
    (Zp q b (rw0 p Y) (k + 1)) (Zp q b (rw1 p Y) (k + 1)) (Zp q b (rw2 p Y) (k + 1))

/-- `Y` is a sign matrix on `{0,1,2} × {0,…,b}`. -/
def SignMat (b : ℕ) (Y : ℕ → ℕ → ℝ) : Prop := ∀ i ≤ 2, ∀ l ≤ b, Y i l = 1 ∨ Y i l = -1

/-- Column `l` of `Y` is the anti-checkerboard column `(-1)^{l+1} s₂`. -/
def IsAntiCol (Y : ℕ → ℕ → ℝ) (l : ℕ) : Prop :=
  Y 0 l = -sgnv l ∧ Y 1 l = sgnv l ∧ Y 2 l = -sgnv l

/-- Column `l` of `Y` is `(-1)^l s₂`. -/
def IsPlusCol (Y : ℕ → ℕ → ℝ) (l : ℕ) : Prop :=
  Y 0 l = sgnv l ∧ Y 1 l = -sgnv l ∧ Y 2 l = sgnv l

/-- The parameter range of Theorem B′ (real parameters). -/
def ParamB (p q : ℝ) : Prop := (5 ≤ p ∧ 3 ≤ q) ∨ (p = 3 ∧ 5 ≤ q)

lemma ParamB.pq {p q : ℝ} (h : ParamB p q) : PQok (p - 1) (q - 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-! ### Proposition 1 -/

/-- **Proposition 1.** -/
theorem prop1 {p q : ℝ} (hq : 2 < q) (b : ℕ) (Y : ℕ → ℕ → ℝ) :
    Theta p q b - Gfun p q b Y = q ^ b * ((∑ k ∈ range b, ScY p q b Y k) / q +
      nu q b * (Dp (p - 1) - (|rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b|)) +
      2 * max 0 (-(Zp q b (rw2 p Y) 0)) - 2 * ((p - 1) ^ 2 + 1) * nu q b) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  unfold Theta Gfun
  rw [L1_potential hq1 b (rw0 p Y), L1_potential hq1 b (rw1 p Y), L1_potential hq1 b (rw2 p Y),
    L1_sgnv hq b, Tv_last hq0.ne', Zp_sgnv_zero hq]
  have hS : ∀ k ∈ range b, ScY p q b Y k / q =
      Dp (p - 1) * cc q k - (cc q k * |rw0 p Y k| + cc q k * |rw1 p Y k| + cc q k * |rw2 p Y k|) -
      (hcell (q - 1) (nu q k) (rw0 p Y k) (Zp q b (rw0 p Y) (k + 1)) / q +
        hcell (q - 1) (nu q k) (rw1 p Y k) (Zp q b (rw1 p Y) (k + 1)) / q +
        hcell (q - 1) (nu q k) (rw2 p Y k) (Zp q b (rw2 p Y) (k + 1)) / q) := by
    intro k _
    unfold ScY Sc cc
    field_simp
  have hsum : (∑ k ∈ range b, ScY p q b Y k) / q =
      Dp (p - 1) * ∑ k ∈ range b, cc q k - (∑ k ∈ range b, cc q k * |rw0 p Y k| +
        ∑ k ∈ range b, cc q k * |rw1 p Y k| + ∑ k ∈ range b, cc q k * |rw2 p Y k|) -
      (∑ k ∈ range b, hcell (q - 1) (nu q k) (rw0 p Y k) (Zp q b (rw0 p Y) (k + 1)) / q +
        ∑ k ∈ range b, hcell (q - 1) (nu q k) (rw1 p Y k) (Zp q b (rw1 p Y) (k + 1)) / q +
        ∑ k ∈ range b, hcell (q - 1) (nu q k) (rw2 p Y k) (Zp q b (rw2 p Y) (k + 1)) / q) := by
    rw [Finset.sum_div, Finset.sum_congr rfl hS]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_div]
  ring

/-! ### Bounds -/

lemma rw_bounds {p : ℝ} (hp : 1 ≤ p) {b : ℕ} {Y : ℕ → ℕ → ℝ} (hY : SignMat b Y) {l : ℕ}
    (hl : l ≤ b) :
    |rw0 p Y l| ≤ 2 * (p - 1) * (p - 1 + 1) ∧ |rw1 p Y l| ≤ 2 * (p - 1) * (p - 1 + 1) ∧
      |rw2 p Y l| ≤ (p - 1 + 1) ^ 2 := by
  have h : ∀ i ≤ 2, |Y i l| ≤ 1 := fun i hi => by rcases hY i hi l hl with h | h <;> simp [h]
  exact Mc_abs_le (by linarith) (h 0 (by norm_num)) (h 1 (by norm_num)) (h 2 le_rfl)

lemma Z_bounds {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) {b : ℕ} {Y : ℕ → ℕ → ℝ} (hY : SignMat b Y)
    {j : ℕ} (hj : j ≤ b) :
    |Zp q b (rw0 p Y) j| ≤ 2 * (p - 1) * (p - 1 + 1) ∧
      |Zp q b (rw1 p Y) j| ≤ 2 * (p - 1) * (p - 1 + 1) ∧
      |Zp q b (rw2 p Y) j| ≤ (p - 1 + 1) ^ 2 :=
  ⟨Zp_abs_le_C hq (fun _ hl => (rw_bounds hp hY hl).1) j hj,
    Zp_abs_le_C hq (fun _ hl => (rw_bounds hp hY hl).2.1) j hj,
    Zp_abs_le_C hq (fun _ hl => (rw_bounds hp hY hl).2.2) j hj⟩

/-- Lemma S for the columns of `Y`. -/
lemma ScY_nonneg {p q : ℝ} (hPQ : PQok (p - 1) (q - 1)) {b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : SignMat b Y) {k : ℕ} (hk : k < b) :
    0 ≤ ScY p q b Y k ∧
      (¬ ((Y 0 k = 1 ∧ Y 1 k = -1 ∧ Y 2 k = 1) ∨ (Y 0 k = -1 ∧ Y 1 k = 1 ∧ Y 2 k = -1)) →
        0 < ScY p q b Y k) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  obtain ⟨b0, b1, b2⟩ := Z_bounds (p := p) (by linarith) (by linarith) hY (show k + 1 ≤ b by omega)
  exact lemS hPQ (nu_nonneg'' hq k) (nu_bounds hq.le k).2 (hY 0 (by norm_num) k hk.le)
    (hY 1 (by norm_num) k hk.le) (hY 2 le_rfl k hk.le) b0 b1 b2

lemma sum_ScY_nonneg {p q : ℝ} (hPQ : PQok (p - 1) (q - 1)) {b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : SignMat b Y) : ∀ k ∈ range b, 0 ≤ ScY p q b Y k :=
  fun _ hk => (ScY_nonneg hPQ hY (mem_range.mp hk)).1

/-! ### States along the anti-checkerboard tail and the `B`-chain -/

lemma anti_state {p q : ℝ} (hq : 2 < q) {b : ℕ} {Y : ℕ → ℕ → ℝ} {J : ℕ} (hJ : J < b)
    (hanti : ∀ l, J < l → l ≤ b → IsAntiCol Y l) :
    Zp q b (rw0 p Y) (J + 1) = sgnv J * (nu q (b - (J + 1)) * (2 * (p - 1) * (p - 1 + 1))) ∧
    Zp q b (rw1 p Y) (J + 1) = sgnv J * (nu q (b - (J + 1)) * (-(2 * (p - 1) ^ 2))) ∧
    Zp q b (rw2 p Y) (J + 1) = sgnv J * (nu q (b - (J + 1)) * ((p - 1) ^ 2 + 1)) := by
  have hs := Zp_sgnv_eq hq (m := b) (show J + 1 ≤ b by omega)
  have hsJ : sgnv (J + 1) = -sgnv J := sgnv_succ J
  refine ⟨?_, ?_, ?_⟩
  · rw [Zp_congr_from q b (w' := fun l => (-(2 * (p - 1) * (p - 1 + 1))) * sgnv l) (J + 1)
      (fun l h1 h2 => by
        obtain ⟨a0, a1, a2⟩ := hanti l (by omega) h2
        simp only [rw0, Mc0]
        rw [a1, a2]
        ring), Zp_smul, hs, hsJ]
    ring
  · rw [Zp_congr_from q b (w' := fun l => (2 * (p - 1) ^ 2) * sgnv l) (J + 1)
      (fun l h1 h2 => by
        obtain ⟨a0, a1, a2⟩ := hanti l (by omega) h2
        simp only [rw1, Mc1]
        rw [a0, a1, a2]
        ring), Zp_smul, hs, hsJ]
    ring
  · rw [Zp_congr_from q b (w' := fun l => (-((p - 1) ^ 2 + 1)) * sgnv l) (J + 1)
      (fun l h1 h2 => by
        obtain ⟨a0, a1, a2⟩ := hanti l (by omega) h2
        simp only [rw2, Mc2]
        rw [a0, a1, a2]
        ring), Zp_smul, hs, hsJ]
    ring

/-- The state at column `b - 2` on the `B`-chain: `-μ₀ α(B)`. -/
lemma chain_state {p q : ℝ} (hq : 2 < q) {b : ℕ} (hb1 : 1 ≤ b) {Y : ℕ → ℕ → ℝ}
    (hB : Y 0 b = 1 ∧ Y 1 b = 1 ∧ Y 2 b = -1)
    (hB' : Y 0 (b - 1) = -1 ∧ Y 1 (b - 1) = -1 ∧ Y 2 (b - 1) = 1) :
    Zp q b (rw0 p Y) (b - 1) = nu q 1 * (2 * (p - 1) * (p - 1 + 1)) ∧
    Zp q b (rw1 p Y) (b - 1) = nu q 1 * (2 * (p - 1)) ∧
    Zp q b (rw2 p Y) (b - 1) = -(nu q 1 * ((p - 1) ^ 2 + 2 * (p - 1) - 1)) := by
  have hq0 : 0 < q := by linarith
  have hb' : b - 1 + 1 = b := by omega
  have hν : nu q 1 = (q - 1 - 1) / q := by rw [nu_succ, nu_zero]
  obtain ⟨u0, u1, u2⟩ := hB
  obtain ⟨v0, v1, v2⟩ := hB'
  refine ⟨?_, ?_, ?_⟩
  · rw [Zp_rec hq0.ne' b _ (show b - 1 < b by omega), hb', Zp_self, hν]
    simp only [rw0, Mc0]
    rw [u1, u2, v1, v2]
    field_simp
    ring
  · rw [Zp_rec hq0.ne' b _ (show b - 1 < b by omega), hb', Zp_self, hν]
    simp only [rw1, Mc1]
    rw [u0, u1, u2, v0, v1, v2]
    field_simp
    ring
  · rw [Zp_rec hq0.ne' b _ (show b - 1 < b by omega), hb', Zp_self, hν]
    simp only [rw2, Mc2]
    rw [u0, u1, u2, v0, v1, v2]
    field_simp
    ring

/-! ### The cases of the proof of Theorem B′ -/

section Cases

variable {p q : ℝ} {b : ℕ} {Y : ℕ → ℕ → ℝ}

lemma Theta_sub_pos (hq : 2 < q) {X : ℝ} (h : Theta p q b - Gfun p q b Y = q ^ b * X)
    (hX : 0 < X) : Gfun p q b Y < Theta p q b := by
  have := mul_pos (pow_pos (by linarith : (0:ℝ) < q) b) hX
  linarith

/-- Case `J < b`: the first deviation from `Y⁻` (scanning from the corner) pays (Lemma FD1). -/
lemma case_first_dev (hPQ : PQok (p - 1) (q - 1)) (hb : Even b) (hY : SignMat b Y) {J : ℕ}
    (hJ : J < b) (hanti : ∀ l, J < l → l ≤ b → IsAntiCol Y l) (hnot : ¬ IsAntiCol Y J) :
    Gfun p q b Y < Theta p q b := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have key := prop1 (p := p) hq b Y
  have hFb : |rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b| = Dp (p - 1) := by
    obtain ⟨a0, a1, a2⟩ := hanti b hJ le_rfl
    simp only [rw0, rw1, rw2]
    rw [a0, a1, a2, sgnv_of_even hb]
    obtain ⟨e0, e1, e2⟩ := col_nA (p - 1)
    rw [e0, e1, e2]
    unfold Dp
    rw [abs_neg, abs_of_nonneg (by nlinarith), abs_of_nonneg (by positivity), abs_neg,
      abs_of_nonneg (by positivity)]
    ring
  have hS := sum_ScY_nonneg hPQ hY (p := p) (q := q)
  have hsingle : ScY p q b Y J ≤ ∑ k ∈ range b, ScY p q b Y k :=
    Finset.single_le_sum hS (mem_range.mpr hJ)
  have hJpay : 2 * (q - 1 + 1) * ((p - 1) ^ 2 + 1) * nu q b < ScY p q b Y J := by
    obtain ⟨s0, s1, s2⟩ := anti_state (p := p) hq hJ hanti
    unfold ScY
    rw [s0, s1, s2]
    have hμ0 := nu_lo' hq J
    have hμ1 := (nu_bounds hq.le J).2
    have hm0 := nu_lo' hq (b - (J + 1))
    have hm1 := (nu_bounds hq.le (b - (J + 1))).2
    have hρ := nu_hi' hq (k := b) (by omega)
    have hreg : (nu q J = 1 ∧ (q - 1 + 1) * nu q b = q - 1 - nu q (b - (J + 1))) ∨
        (nu q (b - (J + 1)) = 1 ∧ (q - 1 + 1) * nu q b = q - 1 - nu q J) ∨
        (q - 1 + 1) ^ 2 * nu q (b - (J + 1)) ≤ (q - 1) ^ 2 + 1 := by
      rcases Nat.eq_zero_or_pos J with h0 | h0
      · left
        subst h0
        refine ⟨nu_zero q, ?_⟩
        have := nu_rec' hq0 (b - 1)
        rw [show b - 1 + 1 = b by omega] at this
        simpa using this
      · by_cases hJb : J = b - 1
        · right; left
          subst hJb
          refine ⟨by rw [show b - (b - 1 + 1) = 0 by omega, nu_zero], ?_⟩
          have := nu_rec' hq0 (b - 1)
          rw [show b - 1 + 1 = b by omega] at this
          exact this
        · right; right
          exact nu_hi' hq (by omega)
    have c0 := hY 0 (by norm_num) J hJ.le
    have c1 := hY 1 (by norm_num) J hJ.le
    have c2 := hY 2 le_rfl J hJ.le
    simp only [rw0, rw1, rw2]
    unfold IsAntiCol at hnot
    rcases sgnv_cases J with hs | hs
    · rw [hs] at hnot ⊢
      simp only [one_mul]
      exact fd1 hPQ hμ0 hμ1 hm0 hm1 hρ hreg c0 c1 c2 (fun h => hnot ⟨h.1, h.2.1, h.2.2⟩)
    · rw [hs] at hnot ⊢
      simp only [neg_one_mul]
      rw [← Sc_neg']
      obtain ⟨n0, n1, n2⟩ := Mc_neg (p - 1) (Y 0 J) (Y 1 J) (Y 2 J)
      rw [← n0, ← n1, ← n2]
      refine fd1 hPQ hμ0 hμ1 hm0 hm1 hρ hreg ?_ ?_ ?_ ?_
      · rcases c0 with h | h <;> rw [h] <;> norm_num
      · rcases c1 with h | h <;> rw [h] <;> norm_num
      · rcases c2 with h | h <;> rw [h] <;> norm_num
      · rintro ⟨h0, h1, h2⟩
        exact hnot ⟨by linarith, by linarith, by linarith⟩
  apply Theta_sub_pos hq key
  rw [hFb, sub_self, mul_zero, add_zero]
  have h1 : 2 * ((p - 1) ^ 2 + 1) * nu q b < (∑ k ∈ range b, ScY p q b Y k) / q := by
    rw [lt_div_iff₀ hq0]
    nlinarith
  have h2 : 0 ≤ max 0 (-(Zp q b (rw2 p Y) 0)) := le_max_left _ _
  linarith

/-- Case `c_b = -E = (-1,-1,-1)`. -/
lemma case_negE (hPQ : PQok (p - 1) (q - 1)) (hY : SignMat b Y)
    (hE : Y 0 b = -1 ∧ Y 1 b = -1 ∧ Y 2 b = -1) : Gfun p q b Y < Theta p q b := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have key := prop1 (p := p) hq b Y
  have hFb : |rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b| = (p - 1 + 1) ^ 2 := by
    obtain ⟨a0, a1, a2⟩ := hE
    simp only [rw0, rw1, rw2]
    rw [a0, a1, a2]
    obtain ⟨e0, e1, e2⟩ := col_nE (p - 1)
    rw [e0, e1, e2, abs_zero, abs_neg, abs_of_nonneg (sq_nonneg _)]
    ring
  have hS := sum_ScY_nonneg hPQ hY (p := p) (q := q)
  have hsum : 0 ≤ ∑ k ∈ range b, ScY p q b Y k := Finset.sum_nonneg hS
  have hν := nu_pos hq b
  apply Theta_sub_pos hq key
  rw [hFb]
  unfold Dp
  have h2 : 0 ≤ max 0 (-(Zp q b (rw2 p Y) 0)) := le_max_left _ _
  have h3 : 0 ≤ (∑ k ∈ range b, ScY p q b Y k) / q := div_nonneg hsum hq0.le
  have h4 : 0 < nu q b * ((p - 1) ^ 2 - 1) := mul_pos hν (by nlinarith)
  nlinarith

/-- Case `c_b = C = (1,-1,-1)`: `G ≤ Θ`, and equality forces `Y = Y⁺` (Lemma EQ). -/
lemma case_C_le (hPQ : PQok (p - 1) (q - 1))
    (hC : Y 0 b = 1 ∧ Y 1 b = -1 ∧ Y 2 b = -1) :
    Theta p q b - Gfun p q b Y =
      q ^ b * ((∑ k ∈ range b, ScY p q b Y k) / q + 2 * max 0 (-(Zp q b (rw2 p Y) 0))) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have key := prop1 (p := p) hq b Y
  have hFb : |rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b| =
      2 * (p - 1) * (p - 1 + 1) + ((p - 1) ^ 2 - 1) := by
    obtain ⟨a0, a1, a2⟩ := hC
    simp only [rw0, rw1, rw2]
    rw [a0, a1, a2]
    obtain ⟨e0, e1, e2⟩ := col_C (p - 1)
    rw [e0, e1, e2, abs_zero, abs_neg, abs_of_nonneg (by nlinarith),
      abs_of_nonneg (by nlinarith)]
    ring
  rw [key, hFb]
  unfold Dp
  ring

/-- One step of Lemma EQ: a vanishing surplus at a column whose state has the sign
`-(-1)^j` in row 2 forces the column `(-1)^j s₂`, and propagates the sign. -/
lemma eq_step (hPQ : PQok (p - 1) (q - 1)) (hY : SignMat b Y) {j : ℕ} (hj : j < b)
    (hS0 : ScY p q b Y j = 0) (hinv : 0 < -sgnv j * Zp q b (rw2 p Y) (j + 1)) :
    IsPlusCol Y j ∧ 0 < sgnv j * Zp q b (rw2 p Y) j := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨b0, b1, b2⟩ := Z_bounds (p := p) (q := q) (by linarith) (by linarith) hY
    (show j + 1 ≤ b by omega)
  have hμ0 := nu_nonneg'' hq j
  have hμ1 := (nu_bounds hq.le j).2
  have hstrict : (p - 1 + 1) ^ 2 < (q - 1) * ((p - 1) ^ 2 + 1) := by
    nlinarith [sq_nonneg (p - 1 - 1), mul_le_mul_of_nonneg_right hQ
      (by positivity : (0:ℝ) ≤ (p - 1) ^ 2 + 1)]
  have hrec : Zp q b (rw2 p Y) j = (Zp q b (rw2 p Y) (j + 1) + (q - 1) * rw2 p Y j) / q :=
    Zp_rec hq0.ne' b _ hj
  have hPP : 0 ≤ 2 * (p - 1) * (p - 1 + 1) := by nlinarith
  have hne : ¬ ¬ ((Y 0 j = 1 ∧ Y 1 j = -1 ∧ Y 2 j = 1) ∨ (Y 0 j = -1 ∧ Y 1 j = 1 ∧ Y 2 j = -1)) := by
    intro h
    have := (ScY_nonneg hPQ hY (p := p) (q := q) hj).2 h
    linarith
  push Not at hne
  rcases hne with ⟨y0, y1, y2⟩ | ⟨y0, y1, y2⟩
  · -- c_j = s₂
    have hcol : ScY p q b Y j = Sc (p - 1) (q - 1) (nu q j) (2 * (p - 1) * (p - 1 + 1))
        (-(2 * (p - 1) ^ 2)) ((p - 1) ^ 2 + 1) (Zp q b (rw0 p Y) (j + 1))
        (Zp q b (rw1 p Y) (j + 1)) (Zp q b (rw2 p Y) (j + 1)) := by
      unfold ScY
      simp only [rw0, rw1, rw2]
      rw [y0, y1, y2]
      obtain ⟨e0, e1, e2⟩ := col_A (p - 1)
      rw [e0, e1, e2]
    obtain ⟨h0, h1, h2, hSc⟩ := lemS_A (Q := q - 1) (μ := nu q j)
      (A0 := 2 * (p - 1) * (p - 1 + 1)) (A1 := -(2 * (p - 1) ^ 2)) (A2 := (p - 1) ^ 2 + 1)
      hPQ hμ0 hμ1 (abs_of_nonneg hPP) (by rw [abs_neg, abs_of_nonneg (by positivity)])
      (abs_of_nonneg (by positivity)) b0 b1 b2
    rw [hcol, hSc] at hS0
    have hz : hcell (q - 1) (nu q j) ((p - 1) ^ 2 + 1) (Zp q b (rw2 p Y) (j + 1)) = 0 := by
      linarith
    have hZ := hc_zero_imp hμ0 hμ1 (by linarith) (by positivity) (by linarith) hz
    have hsj : sgnv j = 1 := by
      rcases sgnv_cases j with h | h
      · exact h
      · rw [h] at hinv; linarith
    refine ⟨⟨by rw [y0, hsj], by rw [y1, hsj], by rw [y2, hsj]⟩, ?_⟩
    rw [hsj, one_mul, hrec]
    simp only [rw2, Mc2]
    rw [y0, y1, y2]
    apply div_pos _ hq0
    have := neg_abs_le (Zp q b (rw2 p Y) (j + 1))
    nlinarith
  · -- c_j = -s₂
    have hcol : ScY p q b Y j = Sc (p - 1) (q - 1) (nu q j) (-(2 * (p - 1) * (p - 1 + 1)))
        (2 * (p - 1) ^ 2) (-((p - 1) ^ 2 + 1)) (Zp q b (rw0 p Y) (j + 1))
        (Zp q b (rw1 p Y) (j + 1)) (Zp q b (rw2 p Y) (j + 1)) := by
      unfold ScY
      simp only [rw0, rw1, rw2]
      rw [y0, y1, y2]
      obtain ⟨e0, e1, e2⟩ := col_nA (p - 1)
      rw [e0, e1, e2]
    obtain ⟨h0, h1, h2, hSc⟩ := lemS_A (Q := q - 1) (μ := nu q j)
      (A0 := -(2 * (p - 1) * (p - 1 + 1))) (A1 := 2 * (p - 1) ^ 2) (A2 := -((p - 1) ^ 2 + 1))
      hPQ hμ0 hμ1 (by rw [abs_neg, abs_of_nonneg hPP]) (abs_of_nonneg (by positivity))
      (by rw [abs_neg, abs_of_nonneg (by positivity)]) b0 b1 b2
    rw [hcol, hSc] at hS0
    have hz : hcell (q - 1) (nu q j) (-((p - 1) ^ 2 + 1)) (Zp q b (rw2 p Y) (j + 1)) = 0 := by
      linarith
    have hZ := hc_zero_imp' hμ0 hμ1 (by linarith) (by nlinarith) (by rw [neg_neg]; linarith) hz
    have hsj : sgnv j = -1 := by
      rcases sgnv_cases j with h | h
      · rw [h] at hinv; linarith
      · exact h
    refine ⟨⟨by rw [y0, hsj], by rw [y1, hsj]; norm_num, by rw [y2, hsj]⟩, ?_⟩
    rw [hsj, hrec]
    simp only [rw2, Mc2]
    rw [y0, y1, y2, neg_one_mul, ← neg_div]
    apply div_pos _ hq0
    have := le_abs_self (Zp q b (rw2 p Y) (j + 1))
    nlinarith

/-- **Lemma EQ.** If `c_b = C` and all surpluses vanish, then `Y = Y⁺` on columns `< b`. -/
lemma eq_all (hPQ : PQok (p - 1) (q - 1)) (hb : Even b) (hb2 : 2 ≤ b) (hY : SignMat b Y)
    (hC : Y 0 b = 1 ∧ Y 1 b = -1 ∧ Y 2 b = -1) (hS0 : ∀ k < b, ScY p q b Y k = 0) :
    ∀ l < b, IsPlusCol Y l := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hinv : ∀ d, d < b → 0 < -sgnv (b - 1 - d) * Zp q b (rw2 p Y) (b - 1 - d + 1) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [show b - 1 - 0 + 1 = b by omega, Zp_self, show b - 1 - 0 = b - 1 by omega,
        sgnv_pred hb (by omega)]
      simp only [rw2, Mc2]
      obtain ⟨a0, a1, a2⟩ := hC
      rw [a0, a1, a2]
      nlinarith
    | succ d ih =>
      intro hd
      have h := (eq_step hPQ hY (show b - 1 - d < b by omega) (hS0 _ (by omega))
        (ih (by omega))).2
      have e1 : b - 1 - (d + 1) + 1 = b - 1 - d := by omega
      have e2 : sgnv (b - 1 - d) = -sgnv (b - 1 - (d + 1)) := by
        rw [← sgnv_succ, e1]
      rw [e1]
      rw [e2] at h
      linarith
  intro l hl
  have h := eq_step hPQ hY hl (hS0 l hl) (by
    have := hinv (b - 1 - l) (by omega)
    rwa [show b - 1 - (b - 1 - l) = l by omega] at this)
  exact h.1

/-- Case `c_b = B = (1,1,-1)`: Lemma FD2. -/
lemma case_B (hPQ : PQok (p - 1) (q - 1)) (hb : Even b) (hb2 : 2 ≤ b) (hY : SignMat b Y)
    (hB : Y 0 b = 1 ∧ Y 1 b = 1 ∧ Y 2 b = -1) : Gfun p q b Y < Theta p q b := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have key := prop1 (p := p) hq b Y
  have hbb : b - 1 + 1 = b := by omega
  have hFb : |rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b| =
      2 * (p - 1) * (p - 1 + 1) + 2 * (p - 1) + ((p - 1) ^ 2 + 2 * (p - 1) - 1) := by
    obtain ⟨a0, a1, a2⟩ := hB
    simp only [rw0, rw1, rw2]
    rw [a0, a1, a2]
    obtain ⟨e0, e1, e2⟩ := col_B (p - 1)
    rw [e0, e1, e2, abs_neg, abs_of_nonneg (by nlinarith), abs_neg,
      abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
  have hS := sum_ScY_nonneg hPQ hY (p := p) (q := q)
  have hρrec : (q - 1 + 1) * nu q b = q - 1 - nu q (b - 1) := by
    have := nu_rec' hq0 (b - 1)
    rwa [hbb] at this
  -- the surplus of column `b - 1`
  have hlast : ScY p q b Y (b - 1) = Sc (p - 1) (q - 1) (nu q (b - 1))
      (Mc0 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (Mc1 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (Mc2 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (-(2 * (p - 1) * (p - 1 + 1))) (-(2 * (p - 1))) ((p - 1) ^ 2 + 2 * (p - 1) - 1) := by
    unfold ScY
    rw [hbb, Zp_self, Zp_self, Zp_self]
    simp only [rw0, rw1, rw2]
    obtain ⟨a0, a1, a2⟩ := hB
    rw [a0, a1, a2]
    obtain ⟨e0, e1, e2⟩ := col_B (p - 1)
    rw [e0, e1, e2]
  have c0 := hY 0 (by norm_num) (b - 1) (by omega)
  have c1 := hY 1 (by norm_num) (b - 1) (by omega)
  have c2 := hY 2 le_rfl (b - 1) (by omega)
  have hμ1 := (nu_bounds hq.le (b - 1)).2
  have hμ0 := nu_nonneg'' hq (b - 1)
  -- it suffices that the surplus sum exceeds `4 P q ρ`
  suffices hsuff : 4 * (p - 1) * ((q - 1 + 1) * nu q b) < ∑ k ∈ range b, ScY p q b Y k by
    apply Theta_sub_pos hq key
    rw [hFb]
    unfold Dp
    have h1 : 4 * (p - 1) * nu q b < (∑ k ∈ range b, ScY p q b Y k) / q := by
      rw [lt_div_iff₀ hq0]
      nlinarith
    have h2 : 0 ≤ max 0 (-(Zp q b (rw2 p Y) 0)) := le_max_left _ _
    nlinarith
  by_cases hcase : ¬ (Y 0 (b - 1) = -1 ∧ Y 1 (b - 1) = -1 ∧ Y 2 (b - 1) = 1) ∨ 4 ≤ p - 1
  · -- FD2 (a)
    have ha := fd2a hPQ hμ0 hμ1 c0 c1 c2 hcase
    rw [← hlast] at ha
    have hsingle : ScY p q b Y (b - 1) ≤ ∑ k ∈ range b, ScY p q b Y k :=
      Finset.single_le_sum hS (mem_range.mpr (by omega))
    rw [hρrec]
    linarith
  · -- FD2 (b): `p = 3` and the chain column at `b - 1`
    push Not at hcase
    obtain ⟨⟨v0, v1, v2⟩, hp4⟩ := hcase
    have hP2 : p - 1 = 2 := by
      rcases hPQ with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · exact h1
    have hQ4 : 4 ≤ q - 1 := by
      rcases hPQ with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · exact h2
    -- column `b - 1`: the chain cost
    have hS1 : 2 * (q - 1) * (1 + nu q (b - 1)) ≤ ScY p q b Y (b - 1) := by
      rw [hlast, v0, v1, v2]
      obtain ⟨e0, e1, e2⟩ := col_nB (p - 1)
      rw [e0, e1, e2]
      have hL := Sc_ge_small (P := p - 1) (Q := q - 1) (μ := nu q (b - 1))
        (A0 := 2 * (p - 1) * (p - 1 + 1)) (A1 := 2 * (p - 1))
        (A2 := -((p - 1) ^ 2 + 2 * (p - 1) - 1)) (B0 := -(2 * (p - 1) * (p - 1 + 1)))
        (B1 := -(2 * (p - 1))) (B2 := (p - 1) ^ 2 + 2 * (p - 1) - 1) hμ0 hμ1 (by linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg (2 * (p - 1) * (p - 1 + 1))); linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg (2 * (p - 1))); linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg ((p - 1) ^ 2 + 2 * (p - 1) - 1)); linarith)
      have hPP : 0 ≤ 2 * (p - 1) * (p - 1 + 1) := by nlinarith
      have hf : 0 ≤ (p - 1) ^ 2 + 2 * (p - 1) - 1 := by nlinarith
      rw [abs_of_nonneg hPP, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (p - 1)), abs_neg,
        abs_of_nonneg hf] at hL
      unfold Dp at hL
      have hval : (q - 1) * (1 + nu q (b - 1)) * (5 * (p - 1) ^ 2 + 2 * (p - 1) + 1 -
          (2 * (p - 1) * (p - 1 + 1) + 2 * (p - 1) + ((p - 1) ^ 2 + 2 * (p - 1) - 1))) =
          2 * (q - 1) * (1 + nu q (b - 1)) := by
        rw [hP2]; ring
      linarith
    -- column `b - 2`: dominance at the state `-μ₀ α(B)`
    have hS2 : 2 * (q - 1) * (1 + nu q (b - 2)) ≤ ScY p q b Y (b - 2) := by
      obtain ⟨s0, s1, s2⟩ := chain_state (p := p) hq (by omega : 1 ≤ b) hB ⟨v0, v1, v2⟩
      have hb2' : b - 2 + 1 = b - 1 := by omega
      unfold ScY
      rw [hb2', s0, s1, s2]
      simp only [rw0, rw1, rw2]
      have hm : (q - 1 + 1) * nu q 1 = q - 1 - 1 := by
        have := nu_rec' hq0 0
        rwa [nu_zero] at this
      exact fd2dom hP2 hQ4 (nu_lo' hq (b - 2)) (nu_bounds hq.le (b - 2)).2 hm
        (hY 0 (by norm_num) (b - 2) (by omega)) (hY 1 (by norm_num) (b - 2) (by omega))
        (hY 2 le_rfl (b - 2) (by omega))
    have hsub : ({b - 2, b - 1} : Finset ℕ) ⊆ range b := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_range]
      omega
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hS j hj)
    rw [Finset.sum_pair (by omega)] at hpair
    have hx : (q - 1 + 1) * nu q (b - 1) = q - 1 - nu q (b - 2) := by
      have := nu_rec' hq0 (b - 2)
      rwa [show b - 2 + 1 = b - 1 by omega] at this
    have hy := nu_gtL' hq (k := b - 2) (by obtain ⟨r, hr⟩ := hb; exact ⟨r - 1, by omega⟩)
    have h2c := two_col hQ4 hx hρrec hy
    rw [hP2]
    nlinarith

end Cases

/-! ### Theorem B′ -/

/-- The anti-checkerboard sign matrix `Y⁻ = -s₂ sᵀ`. -/
def Ym (i l : ℕ) : ℝ := -(sgnv i * sgnv l)

/-- `Y⁺ = s₂ sᵀ - 2 e₂ e_bᵀ`. -/
def Yp (b : ℕ) (i l : ℕ) : ℝ := if i = 2 ∧ l = b then -1 else sgnv i * sgnv l

/-- **Theorem B′** (inequality and equality cases). -/
theorem thmB'_main {p q : ℝ} (hPQ : PQok (p - 1) (q - 1)) {b : ℕ} (hb : Even b) (hb2 : 2 ≤ b)
    {Y : ℕ → ℕ → ℝ} (hY : SignMat b Y) (hc : Y 2 b = -1) :
    Gfun p q b Y ≤ Theta p q b ∧
      (Gfun p q b Y = Theta p q b →
        (∀ i ≤ 2, ∀ l ≤ b, Y i l = Ym i l) ∨ (∀ i ≤ 2, ∀ l ≤ b, Y i l = Yp b i l)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  by_cases hall : ∀ l ≤ b, IsAntiCol Y l
  · -- `Y = Y⁻`
    have hYm : ∀ i ≤ 2, ∀ l ≤ b, Y i l = Ym i l := by
      intro i hi l hl
      obtain ⟨a0, a1, a2⟩ := hall l hl
      unfold Ym
      interval_cases i
      · rw [a0, sgnv_zero']; ring
      · rw [a1, sgnv_one']; ring
      · rw [a2, sgnv_two']; ring
    have key := prop1 (p := p) hq b Y
    have hFb : |rw0 p Y b| + |rw1 p Y b| + |rw2 p Y b| = Dp (p - 1) := by
      obtain ⟨a0, a1, a2⟩ := hall b le_rfl
      simp only [rw0, rw1, rw2]
      rw [a0, a1, a2, sgnv_of_even hb]
      obtain ⟨e0, e1, e2⟩ := col_nA (p - 1)
      rw [e0, e1, e2]
      unfold Dp
      rw [abs_neg, abs_of_nonneg (by nlinarith), abs_of_nonneg (by positivity), abs_neg,
        abs_of_nonneg (by positivity)]
      ring
    have hZ : Zp q b (rw2 p Y) 0 = -(((p - 1) ^ 2 + 1) * nu q b) := by
      rw [Zp_congr q b (w' := fun l => (-((p - 1) ^ 2 + 1)) * sgnv l) (fun l hl => by
        obtain ⟨a0, a1, a2⟩ := hall l hl
        simp only [rw2, Mc2]
        rw [a0, a1, a2]
        ring), Zp_smul, Zp_sgnv_zero hq]
      ring
    have hM : max 0 (-(Zp q b (rw2 p Y) 0)) = ((p - 1) ^ 2 + 1) * nu q b := by
      rw [hZ, neg_neg]
      exact max_eq_right (mul_nonneg (by positivity) (nu_nonneg'' hq b))
    have hsum : 0 ≤ ∑ k ∈ range b, ScY p q b Y k := Finset.sum_nonneg (sum_ScY_nonneg hPQ hY)
    rw [hFb, hM, sub_self, mul_zero, add_zero] at key
    have : 0 ≤ Theta p q b - Gfun p q b Y := by
      rw [key]
      apply mul_nonneg (pow_pos hq0 b).le
      have := div_nonneg hsum hq0.le
      linarith
    exact ⟨by linarith, fun _ => Or.inl hYm⟩
  · push Not at hall
    classical
    set S := (range (b + 1)).filter (fun l => ¬ IsAntiCol Y l) with hSdef
    have hSne : S.Nonempty := by
      obtain ⟨l, hl, hn⟩ := hall
      exact ⟨l, by rw [hSdef, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hn⟩⟩
    set J := S.max' hSne with hJdef
    have hJS : J ∈ S := Finset.max'_mem S hSne
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hJS
    obtain ⟨hJb, hJnot⟩ := hJS
    have hanti : ∀ l, J < l → l ≤ b → IsAntiCol Y l := by
      intro l hl1 hl2
      by_contra hn
      have hlS : l ∈ S := by
        rw [hSdef, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hn⟩
      have := Finset.le_max' S l hlS
      rw [← hJdef] at this
      omega
    rcases Nat.lt_or_ge J b with hJlt | hJge
    · have := case_first_dev hPQ hb hY hJlt hanti hJnot
      exact ⟨this.le, fun h => absurd h this.ne⟩
    · have hJeq : J = b := by omega
      rw [hJeq] at hJnot
      have y0 := hY 0 (by norm_num) b le_rfl
      have y1 := hY 1 (by norm_num) b le_rfl
      rcases y0 with y0 | y0 <;> rcases y1 with y1 | y1
      · have := case_B hPQ hb hb2 hY ⟨y0, y1, hc⟩
        exact ⟨this.le, fun h => absurd h this.ne⟩
      · -- c_b = C
        have hC : Y 0 b = 1 ∧ Y 1 b = -1 ∧ Y 2 b = -1 := ⟨y0, y1, hc⟩
        have hkey := case_C_le (p := p) (q := q) (Y := Y) hPQ hC
        have hsum : 0 ≤ ∑ k ∈ range b, ScY p q b Y k :=
          Finset.sum_nonneg (sum_ScY_nonneg hPQ hY)
        have hM : 0 ≤ max 0 (-(Zp q b (rw2 p Y) 0)) := le_max_left _ _
        have hnn : 0 ≤ Theta p q b - Gfun p q b Y := by
          rw [hkey]
          apply mul_nonneg (pow_pos hq0 b).le
          have := div_nonneg hsum hq0.le
          linarith
        refine ⟨by linarith, fun heq => Or.inr ?_⟩
        have h0 : (∑ k ∈ range b, ScY p q b Y k) / q + 2 * max 0 (-(Zp q b (rw2 p Y) 0)) = 0 := by
          have h1 : q ^ b * ((∑ k ∈ range b, ScY p q b Y k) / q +
              2 * max 0 (-(Zp q b (rw2 p Y) 0))) = 0 := by rw [← hkey]; linarith
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (pow_pos hq0 b).ne'
          · exact h
        have hsum0 : ∑ k ∈ range b, ScY p q b Y k = 0 := by
          have := div_nonneg hsum hq0.le
          have h2 : (∑ k ∈ range b, ScY p q b Y k) / q = 0 := by linarith
          rcases div_eq_zero_iff.mp h2 with h | h
          · exact h
          · exact absurd h hq0.ne'
        have hS0 : ∀ k < b, ScY p q b Y k = 0 := fun k hk =>
          (Finset.sum_eq_zero_iff_of_nonneg (sum_ScY_nonneg hPQ hY)).mp hsum0 k (mem_range.mpr hk)
        have hplus := eq_all hPQ hb hb2 hY hC hS0
        intro i hi l hl
        unfold Yp
        rcases Nat.lt_or_ge l b with hlb | hlb
        · rw [if_neg (by omega)]
          obtain ⟨a0, a1, a2⟩ := hplus l hlb
          interval_cases i
          · rw [a0, sgnv_zero']; ring
          · rw [a1, sgnv_one']; ring
          · rw [a2, sgnv_two']; ring
        · have hlb' : l = b := by omega
          subst hlb'
          interval_cases i
          · rw [if_neg (by omega), y0, sgnv_zero', sgnv_of_even hb]; ring
          · rw [if_neg (by omega), y1, sgnv_one', sgnv_of_even hb]; ring
          · rw [if_pos ⟨rfl, rfl⟩, hc]
      · exfalso
        apply hJnot
        refine ⟨by rw [y0, sgnv_of_even hb], by rw [y1, sgnv_of_even hb], by
          rw [hc, sgnv_of_even hb]⟩
      · have := case_negE hPQ hY ⟨y0, y1, hc⟩
        exact ⟨this.le, fun h => absurd h this.ne⟩

end ICGEqualParityB
