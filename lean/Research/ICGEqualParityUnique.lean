import Mathlib
import Research.ICGEqualParityGraph

/-!
# Corollary A, uniqueness (round 4)

`thmA_lt`: under the hypotheses of `thmA_le`, the inequality is strict unless `(u, v)` is the
anti-checkerboard `(-s, s)` or the truncated checkerboard `(s, -s with v_m = -1)`.

`energy_lt_anti`: for distinct odd primes `p, q`, odd `m` and every set `D` of proper divisors of
`p q^m` different from `D⁻ = {p^i q^j : i + j odd}` and from `D⁺ \ {n}` (`D⁺ = {p^i q^j : i + j even}`),
`E(ICG(p q^m, D)) < E(ICG(p q^m, D⁻))`.
-/

noncomputable section

namespace ICGEqualParity

open Finset ICGGeneral

/-! ### Strict helper facts -/

lemma ParamOK.strict {x R : ℝ} (h : ParamOK x R) : R + 1 < (x - 1) * (R - 1) := by
  rcases h with ⟨hx, hR⟩ | ⟨hx, hR⟩
  · nlinarith
  · subst hx
    nlinarith

lemma surplus_pos {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k < m) :
    0 < 2 * (R - 1) * cc x k - 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| / x := by
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
  apply div_pos _ hx0
  have h1 : 2 * R * nu x k * |Zp x m (w1 u v) (k + 1)| ≤ 2 * R * nu x k * 2 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  rcases hp with ⟨hx5, hR2⟩ | ⟨hx3, hR4⟩
  · have h2 : 2 * (R - 1) * 4 * (1 + nu x k) ≤ 2 * (R - 1) * (x - 1) * (1 + nu x k) := by
      have : 0 ≤ 2 * (R - 1) * (1 + nu x k) := by nlinarith
      nlinarith
    nlinarith [hnb.2]
  · subst hx3
    have e : 2 * (R - 1) * (3 - 1) * (1 + nu 3 k) - 2 * R * nu 3 k * 2 =
        4 * (R - 1 - nu 3 k) := by ring
    nlinarith [hnb.2]

/-- The corner of `w2` has the sign of `u_0`. -/
lemma Zw2_zero_neg {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : 0 < m) {u v : ℕ → ℝ}
    (hu : IsSign m u) (hv : IsSign m v) (hu0 : u 0 = -1) : Zp x m (w2 R u v) 0 < 0 := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hs := hp.strict
  have hx0 : 0 < x := by linarith
  have hB : |Zp x m (w2 R u v) 1| ≤ R + 1 := by
    apply Zp_abs_le_C (by linarith) _ 1 hm
    intro i hi
    unfold w2
    rcases hu i hi with h1 | h1 <;> rcases hv i hi with h2 | h2 <;> rw [h1, h2]
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [show R * -1 + 1 = -(R - 1) by ring, abs_neg, abs_of_nonneg (by linarith)]; linarith
    · rw [show R * -1 + -1 = -(R + 1) by ring, abs_neg, abs_of_pos (by linarith)]
  rw [Zp_rec hx0.ne' m _ hm]
  apply div_neg_of_neg_of_pos _ hx0
  have hw : w2 R u v 0 ≤ -(R - 1) := by
    unfold w2
    rw [hu0]
    rcases hv 0 (Nat.zero_le _) with h | h <;> rw [h] <;> linarith
  have hle := le_abs_self (Zp x m (w2 R u v) 1)
  have : (x - 1) * w2 R u v 0 ≤ (x - 1) * (-(R - 1)) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  nlinarith

/-- A disagreeing position `k ≤ m-2` followed by a disagreeing position `k+1` with `u_k = u_{k+1}`
has strictly positive slack. -/
lemma slk_D_pos {x R : ℝ} (hp : ParamOK x R) {m : ℕ} {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) {k : ℕ} (hk : k + 1 < m) (hne : u k ≠ v k) (hne1 : u (k + 1) ≠ v (k + 1))
    (hsame : u k = u (k + 1)) : 0 < slk x R m u v k := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hnb := nu_bounds (by linarith : (2 : ℝ) ≤ x) k
  have hD := slk_D hp hu hv (by omega) hne
  -- v = -u at k and k+1
  have hvk : v k = -u k := by
    rcases hu k (by omega) with a | a <;> rcases hv k (by omega) with b | b
    · exact absurd (a.trans b.symm) hne
    · rw [a, b]
    · rw [a, b]; norm_num
    · exact absurd (a.trans b.symm) hne
  have hvk1 : v (k + 1) = -u (k + 1) := by
    rcases hu (k + 1) (by omega) with a | a <;> rcases hv (k + 1) (by omega) with b | b
    · exact absurd (a.trans b.symm) hne1
    · rw [a, b]
    · rw [a, b]; norm_num
    · exact absurd (a.trans b.symm) hne1
  -- the path value B = Z_{k+1}(w1) has the sign of u_{k+1} and |B| ≤ 2
  have hB2 : |Zp x m (w1 u v) (k + 2)| ≤ 2 := Zw1_abs_le (x := x) (by linarith) hu hv (by omega)
  have hrec : Zp x m (w1 u v) (k + 1) =
      (Zp x m (w1 u v) (k + 2) + (x - 1) * (2 * u (k + 1))) / x := by
    rw [Zp_rec hx0.ne' m _ hk]
    unfold w1
    rw [hvk1]
    ring_nf
  have hBle : |Zp x m (w1 u v) (k + 1)| ≤ 2 := Zw1_abs_le (x := x) (by linarith) hu hv (by omega)
  have hA : u k - v k = 2 * u k := by rw [hvk]; ring
  have hcellneg : hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)) < 0 := by
    rw [hA]
    have hlo := neg_abs_le (Zp x m (w1 u v) (k + 2))
    have hhi := le_abs_self (Zp x m (w1 u v) (k + 2))
    rcases hu k (by omega) with a | a
    · have hu1 : u (k + 1) = 1 := by rw [← hsame, a]
      rw [hu1] at hrec
      have hBpos : 0 < Zp x m (w1 u v) (k + 1) := by
        rw [hrec]; apply div_pos _ hx0; nlinarith
      have hBle' : Zp x m (w1 u v) (k + 1) ≤ 2 := le_trans (le_abs_self _) hBle
      rw [a, hcell_same_pos (nu_nonneg' (x := x) (by linarith) k) (by linarith [hnb.2])
        hBpos.le (by linarith)]
      have : 0 < x - 1 - nu x k := by linarith [hnb.2]
      nlinarith
    · have hu1 : u (k + 1) = -1 := by rw [← hsame, a]
      rw [hu1] at hrec
      have hBneg : Zp x m (w1 u v) (k + 1) < 0 := by
        rw [hrec]; apply div_neg_of_neg_of_pos _ hx0; nlinarith
      have hBge : -2 ≤ Zp x m (w1 u v) (k + 1) := by linarith [neg_abs_le (Zp x m (w1 u v) (k + 1))]
      have hneg := hcell_neg (x - 1) (nu x k) 2 (-(Zp x m (w1 u v) (k + 1)))
      rw [neg_neg] at hneg
      rw [a, show (2:ℝ) * -1 = -2 by norm_num, hneg,
        hcell_same_pos (nu_nonneg' (x := x) (by linarith) k) (by linarith [hnb.2]) (by linarith)
          (by linarith)]
      have : 0 < x - 1 - nu x k := by linarith [hnb.2]
      nlinarith
  have hR0 : 0 < R := by linarith
  have : 0 < (-(R * hcell (x - 1) (nu x k) (u k - v k) (Zp x m (w1 u v) (k + 1)))) / x := by
    apply div_pos _ hx0
    nlinarith
  linarith [hD.1]

/-- An alternating vector with `u_0 = 1` is `s` on `0..j`. -/
lemma alt_eq_sgnv {m : ℕ} {u : ℕ → ℝ} (hu : IsSign m u) (hu0 : u 0 = 1) {j : ℕ} (hj : j ≤ m)
    (halt : ∀ k, k < j → u k ≠ u (k + 1)) : ∀ i ≤ j, u i = sgnv i := by
  intro i
  induction i with
  | zero => intro _; rw [hu0, sgnv_zero]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hne := halt i (by omega)
    rw [sgnv_succ]
    rcases hu i (by omega) with a | a <;> rcases hu (i + 1) (by omega) with b | b
    · exact absurd (a.trans b.symm) hne
    · rw [b, ← h1, a]
    · rw [b, ← h1, a]; norm_num
    · exact absurd (a.trans b.symm) hne

/-! ### Case II, strict -/

lemma agree_strict {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : Odd m) {u v : ℕ → ℝ}
    (hu : IsSign m u) (hv : IsSign m v) {k : ℕ} (hk : k < m) (heq : u k = v k)
    (hnumk : (R - 1) * (x - 1) * (1 + nu x k * (x + 1)) - 2 * R * nu x k * (x + 1) ≥ 0) :
    2 * (R - 1) * nu x m < ∑ j ∈ range m, slk x R m u v j := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hnum := nu_odd_lt (x := x) (by linarith) hm
  set L := (x - 1) / (x + 1) with hL
  have hslk := fun j (hj : j < m) => slk_nonneg hp hu hv hj
  have h1 := slk_E hp hu hv hk heq
  have hB := Zw1_abs_le (x := x) (by linarith) hu hv (show k + 1 ≤ m from hk)
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
  have hmL : 2 * (R - 1) * nu x m < 2 * (R - 1) * L :=
    mul_lt_mul_of_pos_left hnum (by linarith)
  linarith

/-- The `x = 3` refinement with the stronger conclusion `R - 1 ≤ ∑ slk`. -/
lemma refine_x3' {R : ℝ} (hR : 4 ≤ R) {m : ℕ} (hm3 : 3 ≤ m) {u v : ℕ → ℝ} (hu : IsSign m u)
    (hv : IsSign m v) (hD : ∀ i, 1 ≤ i → i ≤ m → v i = -u i) (h0eq : u 0 = v 0) :
    R - 1 ≤ ∑ j ∈ range m, slk 3 R m u v j := by
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

/-! ### Theorem A, strict form -/

/-- The anti-checkerboard pattern. -/
def IsAnti (m : ℕ) (u v : ℕ → ℝ) : Prop := ∀ i ≤ m, u i = -sgnv i ∧ v i = sgnv i

/-- The truncated-checkerboard pattern. -/
def IsTrunc (m : ℕ) (u v : ℕ → ℝ) : Prop :=
  (∀ i ≤ m, u i = sgnv i) ∧ (∀ i < m, v i = -sgnv i) ∧ v m = -1

theorem thmA_lt {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : Odd m) {u v : ℕ → ℝ}
    (hu : IsSign m u) (hv : IsSign m v) (hvm : v m = -1)
    (hnot : ¬ (IsAnti m u v ∨ IsTrunc m u v)) :
    R * L1 x m (w1 u v) + L1 x m (w2 R u v) -
        2 * x ^ m * max 0 (-(Zp x m (w2 R u v) 0)) <
      (3 * R - 1) * L1 x m sgnv - 2 * (R - 1) * Tv x m sgnv m := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hx0 : 0 < x := by linarith
  have hx2 : 2 < x := by linarith
  have hxm := pow_pos hx0 m
  have hm0 : 0 < m := by rcases hm with ⟨a, ha⟩; omega
  have hTs : Tv x m sgnv m = x ^ m * nu x m := by rw [Tv_last hx0.ne', Zp_sgnv_zero hx2]
  have hLs := L1_sgnv hx2 m
  have hM0 : 0 ≤ max 0 (-(Zp x m (w2 R u v) 0)) := le_max_left _ _
  have hnum := nu_odd_lt (x := x) (by linarith) hm
  have hslk := fun k (hk : k < m) => slk_nonneg hp hu hv hk
  have hsum0 : 0 ≤ ∑ k ∈ range m, slk x R m u v k :=
    Finset.sum_nonneg (fun k hk => hslk k (Finset.mem_range.mp hk))
  have hsm : (-1 : ℝ) = sgnv m := by unfold sgnv; rw [hm.neg_one_pow]
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
    · -- IIIa: u_0 = 1 (strict by Lemma B)
      have hzpos : 0 < Zp x m u 0 := by
        have hs := Zp_sign hx2.le hu 0 (Nat.zero_le _)
        rw [hu0, one_mul] at hs
        exact lt_of_lt_of_le (div_pos (by linarith) hx0) hs
      have hmax : max 0 (-((R - 1) * Zp x m u 0)) = 0 := by
        apply max_eq_left
        nlinarith
      rw [hmax, L1_sign hx2 hu, hTs, hLs]
      have hB := lemmaB (by linarith : (3:ℝ) ≤ x) (by linarith : (1:ℝ) ≤ R) hm hu (by rw [hu0, hum])
      have hB' := mul_lt_mul_of_pos_left hB hxm
      nlinarith
    · -- IIIb: u_0 = -1: strict unless u = -s (anti-checkerboard)
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
      -- L1 u < L1 s, otherwise u = ±s, hence u = -s and (u,v) is the anti-checkerboard
      have hlt : L1 x m u < L1 x m sgnv := by
        rcases lt_or_eq_of_le (L1_le_sgnv hx2 hu) with h | h
        · exact h
        · exfalso
          rcases L1_eq_sgnv hx2 hu h with hs | hs
          · have := hs 0 (Nat.zero_le _)
            rw [hu0, sgnv_zero] at this
            norm_num at this
          · apply hnot
            left
            intro i hi
            refine ⟨hs i hi, ?_⟩
            rw [hvu i hi, hs i hi]
            ring
      rw [hmax, hTs]
      have hpath := L1_path hx0 m u
      have hC := noncorner_le hx2 hu
      rw [noncorner_sgnv hx2] at hC
      rw [hLs] at hlt ⊢
      have e2 : R * (2 * L1 x m u) + (R - 1) * L1 x m u -
          2 * x ^ m * ((R - 1) * |Zp x m u 0|) =
          (R + 1) * L1 x m u + 2 * (R - 1) * (x ^ m *
            ∑ k ∈ range m, |Zp x m u k - Zp x m u (k + 1)|) := by
        rw [hpath]; ring
      rw [e2]
      have h1 : (R + 1) * L1 x m u < (R + 1) * (x ^ m * (∑ k ∈ range m, cc x k + nu x m)) :=
        mul_lt_mul_of_pos_left hlt (by linarith)
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
    · -- Case I: need ∑ slk + 2M > 0
      rw [hbudm, if_pos hEm]
      suffices hpos : 0 < ∑ k ∈ range m, slk x R m u v k + 2 * max 0 (-(Zp x m (w2 R u v) 0)) by
        have := mul_pos hxm hpos
        nlinarith
      by_cases hag : ∃ k, k < m ∧ u k = v k
      · obtain ⟨k, hk, hkeq⟩ := hag
        have h1 := slk_E hp hu hv hk hkeq
        have h2 := surplus_pos hp hu hv hk
        have hsingle : slk x R m u v k ≤ ∑ j ∈ range m, slk x R m u v j :=
          Finset.single_le_sum (f := fun j => slk x R m u v j)
            (fun j hj => hslk j (Finset.mem_range.mp hj)) (Finset.mem_range.mpr hk)
        linarith
      · push Not at hag
        rcases hu 0 (Nat.zero_le _) with hu0 | hu0
        · -- u_0 = 1: some non-alternation of u on 0..m-1 gives positive slack; else truncated
          by_cases halt : ∀ k, k < m - 1 → u k ≠ u (k + 1)
          · exfalso
            apply hnot
            right
            have hus := alt_eq_sgnv hu hu0 (j := m - 1) (by omega) halt
            have hum : u m = -1 := by rw [hEm, hvm]
            refine ⟨?_, ?_, hvm⟩
            · intro i hi
              by_cases him : i = m
              · rw [him, hum, hsm]
              · exact hus i (by omega)
            · intro i hi
              have hne := hag i hi
              have hui := hus i (by omega)
              rcases hu i (by omega) with a | a <;> rcases hv i (by omega) with b | b
              · exact absurd (a.trans b.symm) hne
              · rw [b]; rw [a] at hui; rw [← hui]
              · rw [b]; rw [a] at hui; rw [← hui]; norm_num
              · exact absurd (a.trans b.symm) hne
          · push Not at halt
            obtain ⟨k, hk, hsame⟩ := halt
            have hpos := slk_D_pos hp hu hv (by omega : k + 1 < m) (hag k (by omega))
              (hag (k + 1) (by omega)) hsame
            have hsingle : slk x R m u v k ≤ ∑ j ∈ range m, slk x R m u v j :=
              Finset.single_le_sum (f := fun j => slk x R m u v j)
                (fun j hj => hslk j (Finset.mem_range.mp hj)) (Finset.mem_range.mpr (by omega))
            linarith
        · -- u_0 = -1: the corner term is positive
          have hz := Zw2_zero_neg hp hm0 hu hv hu0
          have : 0 < max 0 (-(Zp x m (w2 R u v) 0)) := lt_max_of_lt_right (by linarith)
          linarith
    · -- Case II: strict
      rw [hbudm, if_neg hEm]
      have hk0lt : k0 < m := lt_of_le_of_ne hk0m (fun h => hEm (h ▸ hk0))
      suffices hS : 2 * (R - 1) * nu x m < ∑ k ∈ range m, slk x R m u v k by
        have h1 := mul_lt_mul_of_pos_left hS hxm
        have h2 := mul_nonneg hxm.le hM0
        nlinarith
      have hp' := hp
      rcases hp' with ⟨hx5, hR2⟩ | ⟨hx3, hR4⟩
      · apply agree_strict hp hm hu hv hk0lt hk0
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
      · subst hx3
        have hL3 : (3 - 1 : ℝ) / (3 + 1) = 1 / 2 := by norm_num
        have hnum3 : nu 3 m < 1 / 2 := by rw [← hL3]; exact hnum
        by_cases hex : ∃ k, 1 ≤ k ∧ k < m ∧ u k = v k
        · obtain ⟨k, hk1, hkm, hkeq⟩ := hex
          apply agree_strict hp hm hu hv hkm hkeq
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
        · push Not at hex
          have hk00 : k0 = 0 := by
            by_contra h0
            exact hex k0 (by omega) hk0lt hk0
          subst hk00
          have hm2 := mul_lt_mul_of_pos_left hnum3 (by linarith : (0:ℝ) < 2 * (R - 1))
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
            have := refine_x3' hR4 hm3 hu hv hD hk0
            linarith

/-! ### Graph-level uniqueness -/

/-- The truncated checkerboard `D⁺ \ {n}` for `n = p q^m`. -/
def DtruncPQ (p q m : ℕ) : Finset ℕ := (DstarPQ p q 1 m).erase (p ^ 1 * q ^ m)

/-- **Corollary A** (uniqueness): every admissible `D` other than `D⁻` and `D⁺ \ {n}` has strictly
smaller energy than `D⁻`. -/
theorem energy_lt_anti (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hm : Odd m) (D : Finset ℕ) (hD : D ⊆ (p ^ 1 * q ^ m).properDivisors)
    (hne1 : D ≠ DantiPQ p q 1 m) (hne2 : D ≠ DtruncPQ p q m) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D) (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hanti := energy_anti p q m hp hq hpq hp3 hq3
  set X : ℕ → ℕ → ℝ := fun c e => if p ^ c * q ^ e ∈ D then 1 else 0 with hX
  have hE : 2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D)
      (ICGBridge.icgAdj_isHermitian _ _) = 2 * L1mat p q 1 m X := by
    rw [energy_icgAdj_pq p q 1 m hp hq hpq]
  rw [two_L1mat_rows (by linarith) (by linarith) m X
    (by intro i _ l _; simp only [hX]; split_ifs <;> simp)] at hE
  have hu : IsSign m (fun l => 2 * X 0 l - 1) := by
    intro l _; simp only [hX]; split_ifs
    · left; norm_num
    · right; norm_num
  have hv : IsSign m (fun l => 2 * X 1 l - 1) := by
    intro l _; simp only [hX]; split_ifs
    · left; norm_num
    · right; norm_num
  have hnot_n : p ^ 1 * q ^ m ∉ D := by
    intro hmem
    exact lt_irrefl _ (Nat.mem_properDivisors.mp (hD hmem)).2
  have hvm : (fun l => 2 * X 1 l - 1) m = -1 := by
    simp only [hX]
    rw [if_neg hnot_n]
    norm_num
  -- elements of D are divisors p^c q^e with c ≤ 1, e ≤ m
  have hrep : ∀ x ∈ D, ∃ c ≤ 1, ∃ e ≤ m, x = p ^ c * q ^ e := fun x hx =>
    pq_dvd_rep hp hq (Nat.mem_properDivisors.mp (hD hx)).1
  -- membership of p^c q^e in D in terms of the sign rows
  have hmemY : ∀ c ≤ 1, ∀ e ≤ m, (p ^ c * q ^ e ∈ D ↔ 2 * X c e - 1 = 1) := by
    intro c _ e _
    simp only [hX]
    constructor
    · intro h; rw [if_pos h]; norm_num
    · intro h
      by_contra hn
      rw [if_neg hn] at h
      norm_num at h
  have hnot : ¬ (IsAnti m (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1) ∨
      IsTrunc m (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) := by
    rintro (hA | hT)
    · apply hne1
      -- p^c q^e ∈ D ↔ Odd (c + e)
      have hiff : ∀ c ≤ 1, ∀ e ≤ m, p ^ c * q ^ e ∈ D ↔ Odd (c + e) := by
        intro c hc e he
        rw [hmemY c hc e he]
        interval_cases c
        · have h0 := (hA e he).1
          simp only at h0
          rw [h0]
          unfold sgnv
          rcases Nat.even_or_odd e with hev | hod
          · rw [hev.neg_one_pow]; simp only [zero_add]
            constructor
            · intro h; norm_num at h
            · intro h; exact absurd h (Nat.not_odd_iff_even.mpr hev)
          · rw [hod.neg_one_pow]; simp only [zero_add]
            constructor
            · intro _; exact hod
            · intro _; norm_num
        · have h1 := (hA e he).2
          simp only at h1
          rw [h1]
          unfold sgnv
          rcases Nat.even_or_odd e with hev | hod
          · rw [hev.neg_one_pow]
            constructor
            · intro _; rw [add_comm]; exact hev.add_one
            · intro _; trivial
          · rw [hod.neg_one_pow]
            constructor
            · intro h; norm_num at h
            · intro h
              exact absurd (by rw [add_comm] at h; exact h) (Nat.not_odd_iff_even.mpr hod.add_one)
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, e, he, rfl⟩ := hrep x hx
        exact (pq_mem_DantiPQ hp hq hpq hc he).mpr ((hiff c hc e he).mp hx)
      · intro hx
        obtain ⟨i, hi, j, hj, hodd, rfl⟩ := mem_DantiPQ_iff.mp hx
        exact (hiff i hi j hj).mpr hodd
    · apply hne2
      obtain ⟨hTu, hTv, _⟩ := hT
      -- p^c q^e ∈ D ↔ Even (c + e) ∧ (c, e) ≠ (1, m)
      have hiff : ∀ c ≤ 1, ∀ e ≤ m, p ^ c * q ^ e ∈ D ↔ (Even (c + e) ∧ ¬ (c = 1 ∧ e = m)) := by
        intro c hc e he
        rw [hmemY c hc e he]
        interval_cases c
        · have h0 := hTu e he
          simp only at h0
          rw [h0]
          unfold sgnv
          rcases Nat.even_or_odd e with hev | hod
          · rw [hev.neg_one_pow]; simp only [zero_add]
            constructor
            · intro _; exact ⟨hev, by omega⟩
            · intro _; trivial
          · rw [hod.neg_one_pow]; simp only [zero_add]
            constructor
            · intro h; norm_num at h
            · intro h; exact absurd h.1 (Nat.not_even_iff_odd.mpr hod)
        · by_cases hem : e = m
          · subst hem
            have hv1 := hvm
            simp only at hv1
            rw [hv1]
            constructor
            · intro h; norm_num at h
            · intro h; exact absurd ⟨rfl, rfl⟩ h.2
          · have h1 := hTv e (lt_of_le_of_ne he hem)
            simp only at h1
            rw [h1]
            unfold sgnv
            rcases Nat.even_or_odd e with hev | hod
            · rw [hev.neg_one_pow]
              constructor
              · intro h; norm_num at h
              · intro h
                exact absurd (by rw [add_comm] at h; exact h.1) (Nat.not_even_iff_odd.mpr hev.add_one)
            · rw [hod.neg_one_pow]
              constructor
              · intro _; exact ⟨by rw [add_comm]; exact hod.add_one, by omega⟩
              · intro _; norm_num
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, e, he, rfl⟩ := hrep x hx
        obtain ⟨hev, hce⟩ := (hiff c hc e he).mp hx
        unfold DtruncPQ
        rw [Finset.mem_erase]
        refine ⟨?_, (pq_mem_DstarPQ hp hq hpq hc he).mpr hev⟩
        intro h
        exact hce ((pq_inj hp hq hpq).mp h)
      · intro hx
        unfold DtruncPQ at hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hxn, hxs⟩ := hx
        obtain ⟨i, hi, j, hj, hev, rfl⟩ := mem_DstarPQ_iff.mp hxs
        refine (hiff i hi j hj).mpr ⟨hev, ?_⟩
        rintro ⟨rfl, rfl⟩
        exact hxn rfl
  have hA := thmA_lt (paramOK_of_primes hp hq hpq hp3 hq3) hm hu hv hvm hnot
  have e1 : (3 * ((p : ℝ) - 1) - 1) = 3 * (p : ℝ) - 4 := by ring
  have e2 : ((p : ℝ) - 1 - 1) = (p : ℝ) - 2 := by ring
  rw [e1, e2] at hA
  nlinarith

/-! ### The truncated checkerboard attains the maximum -/

lemma hcell_opp {P μ A B : ℝ} (hA : 0 ≤ A) (hB : B ≤ 0) (hBA : -(P * A) ≤ B) :
    hcell P μ A B = 0 := by
  unfold hcell
  rw [abs_of_nonneg (by linarith : 0 ≤ A - B), abs_of_nonneg (by linarith : 0 ≤ B + P * A),
    abs_of_nonpos hB, abs_of_nonneg hA]
  ring

lemma hcell_opp' {P μ A B : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B) (hBA : B ≤ -(P * A)) :
    hcell P μ A B = 0 := by
  rw [← hcell_neg]
  exact hcell_opp (by linarith) (by linarith) (by linarith)

/-- The truncated rows: `u = s`, `v = -s` except `v_m = -1`. -/
def vtr (m : ℕ) : ℕ → ℝ := fun i => if i < m then -sgnv i else -1

lemma vtr_isSign (m : ℕ) : IsSign m (vtr m) := by
  intro i hi
  unfold vtr
  split_ifs
  · rcases sgnv_isSign m i hi with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  · right; rfl

lemma w2tr_abs_le {R : ℝ} (hR : 1 ≤ R) (m : ℕ) : ∀ i ≤ m, |w2 R sgnv (vtr m) i| ≤ R + 1 := by
  intro i hi
  unfold w2
  rcases sgnv_isSign m i hi with h1 | h1 <;> rcases vtr_isSign m i hi with h2 | h2 <;> rw [h1, h2]
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [show R * -1 + 1 = -(R - 1) by ring, abs_neg, abs_of_nonneg (by linarith)]; linarith
  · rw [show R * -1 + -1 = -(R + 1) by ring, abs_neg, abs_of_pos (by linarith)]

/-- The `w1` cells of the truncated checkerboard vanish. -/
lemma w1tr_cell {x : ℝ} (hx : 3 ≤ x) {m : ℕ} (hm : Odd m) {k : ℕ} (hk : k < m) :
    hcell (x - 1) (nu x k) (sgnv k - vtr m k) (Zp x m (w1 sgnv (vtr m)) (k + 1)) = 0 := by
  have hx0 : 0 < x := by linarith
  have hsm : sgnv m = -1 := by unfold sgnv; rw [hm.neg_one_pow]
  have hvk : vtr m k = -sgnv k := by unfold vtr; rw [if_pos hk]
  rw [hvk]
  by_cases hkm : k + 1 = m
  · rw [hkm, Zp_self]
    have h0 : w1 sgnv (vtr m) m = 0 := by
      unfold w1 vtr; rw [if_neg (lt_irrefl m), hsm]; ring
    rw [h0]
    rcases sgnv_isSign m k hk.le with h | h <;> rw [h]
    · exact hcell_opp (by norm_num) le_rfl (by linarith)
    · exact hcell_opp' (by norm_num) le_rfl (by linarith)
  · have hk1 : k + 1 < m := by omega
    have hB2 : |Zp x m (w1 sgnv (vtr m)) (k + 2)| ≤ 2 :=
      Zw1_abs_le (x := x) (by linarith) (sgnv_isSign m) (vtr_isSign m) (by omega)
    have hBle : |Zp x m (w1 sgnv (vtr m)) (k + 1)| ≤ 2 :=
      Zw1_abs_le (x := x) (by linarith) (sgnv_isSign m) (vtr_isSign m) (by omega)
    have hrec : Zp x m (w1 sgnv (vtr m)) (k + 1) =
        (Zp x m (w1 sgnv (vtr m)) (k + 2) + (x - 1) * (2 * sgnv (k + 1))) / x := by
      rw [Zp_rec hx0.ne' m _ hk1]
      unfold w1 vtr
      rw [if_pos hk1]
      ring_nf
    have hlo := neg_abs_le (Zp x m (w1 sgnv (vtr m)) (k + 2))
    have hhi := le_abs_self (Zp x m (w1 sgnv (vtr m)) (k + 2))
    have hBl := neg_abs_le (Zp x m (w1 sgnv (vtr m)) (k + 1))
    have hBh := le_abs_self (Zp x m (w1 sgnv (vtr m)) (k + 1))
    rw [sgnv_succ] at hrec
    rcases sgnv_isSign m k hk.le with h | h <;> rw [h] at hrec ⊢
    · have hnum : Zp x m (w1 sgnv (vtr m)) (k + 2) + (x - 1) * (2 * -1) ≤ 0 := by linarith
      have hBneg : Zp x m (w1 sgnv (vtr m)) (k + 1) ≤ 0 := by
        rw [hrec]; exact div_nonpos_of_nonpos_of_nonneg hnum hx0.le
      rw [show (1:ℝ) - -1 = 2 by norm_num]
      exact hcell_opp (by norm_num) hBneg (by linarith)
    · have hnum : 0 ≤ Zp x m (w1 sgnv (vtr m)) (k + 2) + (x - 1) * (2 * -(-1)) := by linarith
      have hBpos : 0 ≤ Zp x m (w1 sgnv (vtr m)) (k + 1) := by
        rw [hrec]; exact div_nonneg hnum hx0.le
      rw [show (-1:ℝ) - -(-1) = -2 by norm_num]
      exact hcell_opp' (by norm_num) hBpos (by linarith)

/-- The `w2` cells of the truncated checkerboard vanish. -/
lemma w2tr_cell {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : Odd m) {k : ℕ} (hk : k < m) :
    hcell (x - 1) (nu x k) (R * sgnv k + vtr m k) (Zp x m (w2 R sgnv (vtr m)) (k + 1)) = 0 := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hs := hp.strict
  have hx0 : 0 < x := by linarith
  have hsm : sgnv m = -1 := by unfold sgnv; rw [hm.neg_one_pow]
  have hvk : vtr m k = -sgnv k := by unfold vtr; rw [if_pos hk]
  rw [hvk, show R * sgnv k + -sgnv k = (R - 1) * sgnv k by ring]
  by_cases hkm : k + 1 = m
  · rw [hkm, Zp_self]
    have hw : w2 R sgnv (vtr m) m = -(R + 1) := by
      unfold w2 vtr; rw [if_neg (lt_irrefl m), hsm]; ring
    rw [hw]
    have hsk : sgnv k = 1 := by
      have h1 : sgnv (k + 1) = -1 := by rw [hkm, hsm]
      rw [sgnv_succ] at h1
      linarith
    rw [hsk, mul_one]
    exact hcell_opp (by linarith) (by linarith) (by linarith)
  · have hk1 : k + 1 < m := by omega
    have hB2 : |Zp x m (w2 R sgnv (vtr m)) (k + 2)| ≤ R + 1 :=
      Zp_abs_le_C (by linarith) (w2tr_abs_le (by linarith) m) (k + 2) (by omega)
    have hBle : |Zp x m (w2 R sgnv (vtr m)) (k + 1)| ≤ R + 1 :=
      Zp_abs_le_C (by linarith) (w2tr_abs_le (by linarith) m) (k + 1) (by omega)
    have hrec : Zp x m (w2 R sgnv (vtr m)) (k + 1) =
        (Zp x m (w2 R sgnv (vtr m)) (k + 2) + (x - 1) * ((R - 1) * sgnv (k + 1))) / x := by
      rw [Zp_rec hx0.ne' m _ hk1]
      unfold w2 vtr
      rw [if_pos hk1]
      ring_nf
    have hlo := neg_abs_le (Zp x m (w2 R sgnv (vtr m)) (k + 2))
    have hhi := le_abs_self (Zp x m (w2 R sgnv (vtr m)) (k + 2))
    have hBl := neg_abs_le (Zp x m (w2 R sgnv (vtr m)) (k + 1))
    have hBh := le_abs_self (Zp x m (w2 R sgnv (vtr m)) (k + 1))
    rw [sgnv_succ] at hrec
    rcases sgnv_isSign m k hk.le with h | h <;> rw [h] at hrec ⊢
    · have hnum : Zp x m (w2 R sgnv (vtr m)) (k + 2) + (x - 1) * ((R - 1) * -1) ≤ 0 := by
        have e : (x - 1) * ((R - 1) * -1) = -((x - 1) * (R - 1)) := by ring
        rw [e]; linarith
      have hBneg : Zp x m (w2 R sgnv (vtr m)) (k + 1) ≤ 0 := by
        rw [hrec]; exact div_nonpos_of_nonpos_of_nonneg hnum hx0.le
      rw [mul_one]
      exact hcell_opp (by linarith) hBneg (by linarith)
    · have hnum : 0 ≤ Zp x m (w2 R sgnv (vtr m)) (k + 2) + (x - 1) * ((R - 1) * -(-1)) := by
        have e : (x - 1) * ((R - 1) * -(-1)) = (x - 1) * (R - 1) := by ring
        rw [e]; linarith
      have hBpos : 0 ≤ Zp x m (w2 R sgnv (vtr m)) (k + 1) := by
        rw [hrec]; exact div_nonneg hnum hx0.le
      have e2 : (R - 1) * -1 = -(R - 1) := by ring
      rw [e2]
      exact hcell_opp' (by linarith) hBpos (by linarith)

theorem trunc_value {x R : ℝ} (hp : ParamOK x R) {m : ℕ} (hm : Odd m) :
    R * L1 x m (w1 sgnv (vtr m)) + L1 x m (w2 R sgnv (vtr m)) -
        2 * x ^ m * max 0 (-(Zp x m (w2 R sgnv (vtr m)) 0)) =
      (3 * R - 1) * L1 x m sgnv - 2 * (R - 1) * Tv x m sgnv m := by
  obtain ⟨hx, hR, hxR⟩ := hp.basic
  have hs := hp.strict
  have hx0 : 0 < x := by linarith
  have hx2 : 2 < x := by linarith
  have hm0 : 0 < m := by rcases hm with ⟨a, ha⟩; omega
  have hsm : sgnv m = -1 := by unfold sgnv; rw [hm.neg_one_pow]
  have hTs : Tv x m sgnv m = x ^ m * nu x m := by rw [Tv_last hx0.ne', Zp_sgnv_zero hx2]
  have hLs := L1_sgnv hx2 m
  have hZ2pos : 0 < Zp x m (w2 R sgnv (vtr m)) 0 := by
    have hB : |Zp x m (w2 R sgnv (vtr m)) 1| ≤ R + 1 :=
      Zp_abs_le_C (by linarith) (w2tr_abs_le (by linarith) m) 1 hm0
    have hle := neg_abs_le (Zp x m (w2 R sgnv (vtr m)) 1)
    rw [Zp_rec hx0.ne' m _ hm0]
    have hw0 : w2 R sgnv (vtr m) 0 = R - 1 := by
      unfold w2 vtr
      rw [if_pos hm0, sgnv_zero]
      ring
    rw [hw0]
    apply div_pos _ hx0
    linarith
  have hmax : max 0 (-(Zp x m (w2 R sgnv (vtr m)) 0)) = 0 := max_eq_left (by linarith)
  rw [hmax, phi_identity (by linarith) m sgnv (vtr m), hTs, hLs]
  have hslk0 : ∀ k < m, slk x R m sgnv (vtr m) k = 0 := by
    intro k hk
    have hvk : vtr m k = -sgnv k := by unfold vtr; rw [if_pos hk]
    have hbud : R * |sgnv k - vtr m k| + |R * sgnv k + vtr m k| = 3 * R - 1 := by
      have := budget_eq (by linarith : (1:ℝ) ≤ R) (sgnv_isSign m k hk.le) (vtr_isSign m k hk.le)
      rw [if_neg (by rw [hvk]; rcases sgnv_isSign m k hk.le with h | h <;> rw [h] <;> norm_num)]
        at this
      exact this
    unfold slk
    rw [hbud, w1tr_cell (by linarith) hm hk, w2tr_cell hp hm hk]
    ring
  rw [Finset.sum_eq_zero (fun k hk => hslk0 k (Finset.mem_range.mp hk))]
  have hbm : R * |sgnv m - vtr m m| + |R * sgnv m + vtr m m| = R + 1 := by
    have hv : vtr m m = -1 := by unfold vtr; rw [if_neg (lt_irrefl m)]
    rw [hsm, hv, show (-1:ℝ) - -1 = 0 by norm_num, abs_zero, mul_zero, zero_add,
      show R * -1 + -1 = -(R + 1) by ring, abs_neg, abs_of_pos (by linarith)]
  rw [hbm]
  ring

/-- The truncated checkerboard `D⁺ \ {n}` also attains the maximal energy. -/
theorem energy_trunc (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hm : Odd m) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DtruncPQ p q m))
        (ICGBridge.icgAdj_isHermitian _ _) =
      ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hanti := energy_anti p q m hp hq hpq hp3 hq3
  set X : ℕ → ℕ → ℝ := fun c e => if p ^ c * q ^ e ∈ DtruncPQ p q m then 1 else 0 with hX
  have hE : 2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DtruncPQ p q m))
      (ICGBridge.icgAdj_isHermitian _ _) = 2 * L1mat p q 1 m X := by
    rw [energy_icgAdj_pq p q 1 m hp hq hpq]
  rw [two_L1mat_rows (by linarith) (by linarith) m X
    (by intro i _ l _; simp only [hX]; split_ifs <;> simp)] at hE
  -- the rows of the truncated checkerboard
  have hmem : ∀ c ≤ 1, ∀ e ≤ m, p ^ c * q ^ e ∈ DtruncPQ p q m ↔ (Even (c + e) ∧ ¬ (c = 1 ∧ e = m)) := by
    intro c hc e he
    unfold DtruncPQ
    rw [Finset.mem_erase, pq_mem_DstarPQ hp hq hpq hc he]
    constructor
    · rintro ⟨hne, hev⟩
      exact ⟨hev, fun h => hne (by rw [h.1, h.2])⟩
    · rintro ⟨hev, hce⟩
      exact ⟨fun h => hce ((pq_inj hp hq hpq).mp h), hev⟩
  have hrow0 : ∀ l ≤ m, 2 * X 0 l - 1 = sgnv l := by
    intro l hl
    simp only [hX]
    unfold sgnv
    rcases Nat.even_or_odd l with hev | hod
    · rw [if_pos ((hmem 0 (by norm_num) l hl).mpr ⟨by simpa using hev, by omega⟩), hev.neg_one_pow]
      norm_num
    · rw [if_neg (fun h => (Nat.not_even_iff_odd.mpr hod) (by simpa using ((hmem 0 (by norm_num) l hl).mp h).1)),
        hod.neg_one_pow]
      norm_num
  have hrow1 : ∀ l ≤ m, 2 * X 1 l - 1 = vtr m l := by
    intro l hl
    simp only [hX]
    unfold vtr
    by_cases hlm : l < m
    · rw [if_pos hlm]
      unfold sgnv
      rcases Nat.even_or_odd l with hev | hod
      · rw [if_neg (fun h => (Nat.not_even_iff_odd.mpr (by rw [add_comm]; exact hev.add_one))
          ((hmem 1 le_rfl l hl).mp h).1), hev.neg_one_pow]
        norm_num
      · rw [if_pos ((hmem 1 le_rfl l hl).mpr ⟨by rw [add_comm]; exact hod.add_one, by omega⟩),
          hod.neg_one_pow]
        norm_num
    · rw [if_neg hlm]
      have hl' : l = m := by omega
      rw [if_neg (fun h => ((hmem 1 le_rfl l hl).mp h).2 ⟨rfl, hl'⟩)]
      norm_num
  have hw1 : L1 q m (w1 (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) =
      L1 q m (w1 sgnv (vtr m)) :=
    L1_congr q m (fun l hl => by unfold w1; dsimp only; rw [hrow0 l hl, hrow1 l hl])
  have hw2 : L1 q m (w2 ((p : ℝ) - 1) (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) =
      L1 q m (w2 ((p : ℝ) - 1) sgnv (vtr m)) :=
    L1_congr q m (fun l hl => by unfold w2; dsimp only; rw [hrow0 l hl, hrow1 l hl])
  have hz2 : Zp q m (w2 ((p : ℝ) - 1) (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) 0 =
      Zp q m (w2 ((p : ℝ) - 1) sgnv (vtr m)) 0 :=
    Zp_congr q m (fun l hl => by unfold w2; dsimp only; rw [hrow0 l hl, hrow1 l hl]) 0
  rw [hw1, hw2, hz2] at hE
  have hv := trunc_value (paramOK_of_primes hp hq hpq hp3 hq3) hm
  have e1 : (3 * ((p : ℝ) - 1) - 1) = 3 * (p : ℝ) - 4 := by ring
  have e2 : ((p : ℝ) - 1 - 1) = (p : ℝ) - 2 := by ring
  rw [e1, e2] at hv
  linarith

lemma DtruncPQ_subset {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (m : ℕ) :
    DtruncPQ p q m ⊆ (p ^ 1 * q ^ m).properDivisors := by
  intro x hx
  unfold DtruncPQ at hx
  rw [Finset.mem_erase] at hx
  obtain ⟨hxn, hxs⟩ := hx
  obtain ⟨i, hi, j, hj, _, rfl⟩ := mem_DstarPQ_iff.mp hxs
  rw [Nat.mem_properDivisors]
  have hdvd : p ^ i * q ^ j ∣ p ^ 1 * q ^ m := (pq_dvd_iff hp hq hpq).mpr ⟨hi, hj⟩
  have hpos : 0 < p ^ 1 * q ^ m := by
    have := hp.pos
    have := hq.pos
    positivity
  exact ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) hxn⟩

/-- **Corollary A** (all parts): for distinct odd primes `p, q` and odd `m`, with `n = p q^m`:
both `D⁻ = {p^i q^j : i + j odd}` and `D⁺ \ {n}` are admissible, they have the same energy
`E = (n + (3p-4) d_m(q) - 2(p-2) δ_m(q)) / 2`, and every admissible `D` has energy at most `E`,
with equality only for these two sets. -/
theorem corollaryA (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hm : Odd m) :
    DantiPQ p q 1 m ⊆ (p ^ 1 * q ^ m).properDivisors ∧
      DtruncPQ p q m ⊆ (p ^ 1 * q ^ m).properDivisors ∧
      2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
          (ICGBridge.icgAdj_isHermitian _ _) =
        (p : ℝ) * (q : ℝ) ^ m + (3 * (p : ℝ) - 4) * L1 q m sgnv -
          2 * ((p : ℝ) - 2) * Tv q m sgnv m ∧
      ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DtruncPQ p q m))
          (ICGBridge.icgAdj_isHermitian _ _) =
        ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
          (ICGBridge.icgAdj_isHermitian _ _) ∧
      ∀ D : Finset ℕ, D ⊆ (p ^ 1 * q ^ m).properDivisors →
        ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D) (ICGBridge.icgAdj_isHermitian _ _) ≤
          ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
            (ICGBridge.icgAdj_isHermitian _ _) ∧
        (ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D) (ICGBridge.icgAdj_isHermitian _ _) =
          ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
            (ICGBridge.icgAdj_isHermitian _ _) → D = DantiPQ p q 1 m ∨ D = DtruncPQ p q m) := by
  have hev : Even (1 + m) := by rcases hm with ⟨a, ha⟩; exact ⟨a + 1, by omega⟩
  refine ⟨DantiPQ_subset hp hq hpq hev, DtruncPQ_subset hp hq hpq m,
    energy_anti p q m hp hq hpq hp3 hq3, energy_trunc p q m hp hq hpq hp3 hq3 hm, ?_⟩
  intro D hD
  refine ⟨energy_le_anti p q m hp hq hpq hp3 hq3 hm D hD, ?_⟩
  intro heq
  by_contra hcon
  push Not at hcon
  have := energy_lt_anti p q m hp hq hpq hp3 hq3 hm D hD hcon.1 hcon.2
  linarith

end ICGEqualParity


#print axioms ICGEqualParity.trunc_value
#print axioms ICGEqualParity.energy_trunc


#print axioms ICGEqualParity.thmA_lt
#print axioms ICGEqualParity.energy_lt_anti
#print axioms ICGEqualParity.corollaryA
