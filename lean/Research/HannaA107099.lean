import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A107099: the vanishing part of the mod-3 conjecture

A107099 (Paul D. Hanna, May 13 2005), NAME:
"G.f. satisfies A(A(x)) = x + 4*x^3, where A(x) = Sum_{n>=0} a(n)*x^(2*n+1)."
COMMENT: "Coefficients [x^n] A(x) = 0 (mod 3) except at n = 3^k (conjecture)."

We prove: for every integer power series `A` with `A(0) = 0`, `[x^1] A = 1` (the first
term `a(0) = 1`) and `A(A(x)) = x + 4x^3`, the coefficient `[x^n] A` is divisible by 3
whenever `n` is not a power of 3.

We also prove (`hanna_a107099_counterexample`) that `3 ∣ [x^729] A`, where `729 = 3^6`
(OEIS index 364, since `a(n) = [x^(2n+1)] A`). So the stronger reading of the comment,
non-vanishing at every `n = 3^k`, is false; the statement as written (vanishing off the
powers of 3) is `hanna_a107099`.

Proof: modulo 3, `F∘F = x + x^3`.  Call a series *additive* if its coefficients vanish off
the powers of 3.  Compositions of additive series are additive (Frobenius: `H^(3^j)` is
`H(x^(3^j))`).  Strong induction on `m` (not a power of 3): the truncation `T` of `F` below
degree `m` is additive, so `[x^m] T∘T = 0`, while `[x^m] F∘F - [x^m] T∘T = 2 f_m`
(linearization: `F ≡ T mod x^m`, `[x^1] T = 1`).  As `[x^m](x + x^3) = 0`, `2 f_m = 0`.
-/

noncomputable section
namespace HannaA107099
open PowerSeries

local notation "K" => ZMod 3

/-- Frobenius in `(ZMod 3)[[X]]`: cubing is the substitution `X ↦ X^3`. -/
lemma cube_eq_expand (F : PowerSeries K) : F ^ 3 = expand 3 three_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 3 three_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

/-- A series is additive if its coefficients vanish off the powers of 3. -/
def Additive (G : PowerSeries K) : Prop := ∀ m, (∀ j, m ≠ 3 ^ j) → coeff m G = 0

lemma not_pow_div (m : ℕ) (hm : ∀ j, m ≠ 3 ^ j) (h3 : 3 ∣ m) : ∀ j, m / 3 ≠ 3 ^ j := by
  intro j hj
  apply hm (j + 1)
  obtain ⟨t, rfl⟩ := h3
  rw [Nat.mul_div_cancel_left t (by norm_num)] at hj
  rw [hj, pow_succ]; ring

lemma additive_pow (H : PowerSeries K) (hH : Additive H) : ∀ j, Additive (H ^ (3 ^ j)) := by
  intro j
  induction j with
  | zero => simpa using hH
  | succ j ih =>
    intro m hm
    rw [pow_succ, pow_mul, cube_eq_expand, coeff_expand]
    split_ifs with h3
    · exact ih _ (not_pow_div m hm h3)
    · rfl

/-- Compositions of additive series are additive. -/
lemma additive_subst (G H : PowerSeries K) (hG : Additive G) (hH : Additive H)
    (hH0 : constantCoeff H = 0) : Additive (G.subst H) := by
  intro m hm
  have hs : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  rw [coeff_subst' hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : ∃ j, d = 3 ^ j
  · obtain ⟨j, rfl⟩ := hd
    rw [additive_pow H hH j m hm, smul_zero]
  · push Not at hd
    rw [hG d hd, zero_smul]

/-- Composition respects congruences modulo `X^n` in the inner argument. -/
lemma subst_congr_right (F G1 G2 : PowerSeries K) (hG1 : HasSubst G1) (hG2 : HasSubst G2)
    (n : ℕ) (h : X ^ n ∣ G1 - G2) : X ^ n ∣ F.subst G1 - F.subst G2 := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, sub_eq_zero, coeff_subst' hG1, coeff_subst' hG2]
  refine finsum_congr (fun d => ?_)
  have h' : X ^ n ∣ G1 ^ d - G2 ^ d := h.trans (sub_dvd_pow_sub_pow G1 G2 d)
  rw [X_pow_dvd_iff] at h'
  have := h' m hm
  rw [map_sub, sub_eq_zero] at this
  rw [this]

/-- `coeff m (H^d) = 0` for `d > m` when `H(0) = 0`. -/
lemma coeff_pow_eq_zero {H : PowerSeries K} (hH0 : constantCoeff H = 0) {m d : ℕ} (hd : m < d) :
    coeff m (H ^ d) = 0 := by
  have : X ^ d ∣ H ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hH0) d
  rw [X_pow_dvd_iff] at this
  exact this m hd

/-- For `d ≥ 2`, `X^(m+1) ∣ F1^d - F2^d` when `X^m ∣ F1 - F2` and both have zero constant
term. -/
lemma pow_sub_pow_dvd {F1 F2 : PowerSeries K} (h1 : constantCoeff F1 = 0)
    (h2 : constantCoeff F2 = 0) {m d : ℕ} (hd : 2 ≤ d) (h : X ^ m ∣ F1 - F2) :
    X ^ (m + 1) ∣ F1 ^ d - F2 ^ d := by
  rw [← geom_sum₂_mul, pow_succ, mul_comm (∑ i ∈ Finset.range d, F1 ^ i * F2 ^ (d - 1 - i))]
  refine mul_dvd_mul h (Finset.dvd_sum fun i hi => ?_)
  rw [Finset.mem_range] at hi
  by_cases hi0 : i = 0
  · subst hi0
    rw [pow_zero, one_mul]
    exact dvd_pow (X_dvd_iff.mpr h2) (by omega)
  · exact dvd_mul_of_dvd_left (dvd_pow (X_dvd_iff.mpr h1) hi0) _

/-- Linearization: if `F1 ≡ F2 (mod X^m)` (`m ≥ 1`), then
`[x^m] G(F1) - [x^m] G(F2) = [x^1] G * ([x^m] F1 - [x^m] F2)`. -/
lemma coeff_subst_sub (G F1 F2 : PowerSeries K) (h1 : constantCoeff F1 = 0)
    (h2 : constantCoeff F2 = 0) {m : ℕ} (hm : 1 ≤ m) (h : X ^ m ∣ F1 - F2) :
    coeff m (G.subst F1) - coeff m (G.subst F2) = coeff 1 G * (coeff m F1 - coeff m F2) := by
  have hs1 : HasSubst F1 := HasSubst.of_constantCoeff_zero' h1
  have hs2 : HasSubst F2 := HasSubst.of_constantCoeff_zero' h2
  rw [coeff_subst' hs1, coeff_subst' hs2]
  have sup : ∀ F : PowerSeries K, constantCoeff F = 0 →
      (Function.support fun d => coeff d G • coeff m (F ^ d)) ⊆ (Finset.range (m + 1) : Set ℕ) := by
    intro F hF d hd
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero hF (by omega), smul_zero])
  rw [finsum_eq_sum_of_support_subset _ (sup F1 h1), finsum_eq_sum_of_support_subset _ (sup F2 h2),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 1]
  · simp [smul_eq_mul, mul_sub]
  · intro d _ hd1
    rw [← smul_sub]
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · have : d = 0 := by omega
      subst this
      simp
    · have hdv := pow_sub_pow_dvd h1 h2 hd2 h
      rw [X_pow_dvd_iff] at hdv
      rw [← map_sub, hdv m (by omega), smul_zero]
  · intro h1m
    exfalso; exact h1m (Finset.mem_range.mpr (by omega))

/-- The truncation of `F` below degree `m`, as a power series. -/
def tr (m : ℕ) (F : PowerSeries K) : PowerSeries K := ((trunc m F : Polynomial K) : PowerSeries K)

lemma coeff_tr (m k : ℕ) (F : PowerSeries K) :
    coeff k (tr m F) = if k < m then coeff k F else 0 := by
  rw [tr, Polynomial.coeff_coe, coeff_trunc]

/-- Linearization at degree `m ≥ 2`: `[x^m] F∘F - [x^m] T∘T = 2 f_m` with `T = tr m F`. -/
lemma lin (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1) (m : ℕ)
    (hm1 : 2 ≤ m) :
    coeff m (F.subst F) - coeff m ((tr m F).subst (tr m F)) = 2 * coeff m F := by
  have hsF : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  set T := tr m F with hT
  have hTc : ∀ k, coeff k T = if k < m then coeff k F else 0 := fun k => coeff_tr m k F
  have hT0 : constantCoeff T = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hTc, if_pos (by omega),
      coeff_zero_eq_constantCoeff_apply, h0]
  have hT1 : coeff 1 T = 1 := by rw [hTc, if_pos (by omega), h1]
  have hTm : coeff m T = 0 := by rw [hTc, if_neg (lt_irrefl m)]
  have hdvd : X ^ m ∣ F - T := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hTc, if_pos hk, sub_self]
  have e1 : coeff m (F.subst F) - coeff m (T.subst F) = coeff m F := by
    obtain ⟨Q, hQ⟩ := hdvd
    obtain ⟨U, hU⟩ : (X : PowerSeries K) ∣ F := X_dvd_iff.mpr h0
    have hU0 : constantCoeff U = 1 := by
      have h := congrArg (coeff 1) hU
      rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
        coeff_zero_eq_constantCoeff_apply] at h
      exact h.symm
    have e : F.subst F - T.subst F = X ^ m * (U ^ m * Q.subst F) := by
      have hFm : F ^ m = X ^ m * U ^ m := by rw [hU, mul_pow]
      rw [← subst_sub hsF, hQ, subst_mul hsF, subst_pow hsF, subst_X hsF, hFm]
      ring
    have hQF : constantCoeff (Q.subst F) = constantCoeff Q := by
      have hXF : (X : PowerSeries K) ^ 1 ∣ F - X := by
        rw [pow_one, X_dvd_iff]; simp [h0]
      have := subst_congr_right Q F X hsF HasSubst.X' 1 hXF
      rw [X_subst, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
      exact this
    have hQm : constantCoeff Q = coeff m F := by
      have h := congrArg (coeff m) hQ
      rw [map_sub, hTm, sub_zero, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply] at h
      exact h.symm
    rw [← map_sub, e, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hU0, one_pow, one_mul, hQF, hQm]
  have e2 : coeff m (T.subst F) - coeff m (T.subst T) = coeff m F := by
    rw [coeff_subst_sub T F T h0 hT0 (by omega) hdvd, hT1, hTm, sub_zero, one_mul]
  linear_combination e1 + e2

/-- The statement in `(ZMod 3)[[X]]`. -/
theorem residue (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst F = X + X ^ 3) : Additive F := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hm0 : m = 0
    · subst hm0
      rw [coeff_zero_eq_constantCoeff_apply, h0]
    have hm1 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · have : m = 1 := by omega
        subst this
        exact absurd (by norm_num : (1 : ℕ) = 3 ^ 0) (hm 0)
      · exact h
    have hT0 : constantCoeff (tr m F) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_tr, if_pos (by omega),
        coeff_zero_eq_constantCoeff_apply, h0]
    have hTadd : Additive (tr m F) := by
      intro k hk
      rw [coeff_tr]
      split_ifs with hkm
      · exact ih k hkm hk
      · rfl
    have hTT : coeff m ((tr m F).subst (tr m F)) = 0 :=
      additive_subst (tr m F) (tr m F) hTadd hTadd hT0 m hm
    have hFF : coeff m (F.subst F) = 0 := by
      rw [hF, map_add, coeff_X, coeff_X_pow, if_neg (fun h => hm 0 (by simpa using h)),
        if_neg (fun h => hm 1 (by simpa using h)), add_zero]
    have htwo : (2 : K) * coeff m F = 0 := by
      have hl := lin F h0 h1 m hm1
      rw [hFF, hTT, sub_zero] at hl
      linear_combination -hl
    have h2 : (2 : K) ≠ 0 := by decide
    exact (mul_eq_zero.mp htwo).resolve_left h2

/-! ### The non-vanishing claim fails at `3^6 = 729` -/

lemma coeff_pow3_pow (H : PowerSeries K) :
    ∀ i k, i ≤ k → coeff (3 ^ k) (H ^ (3 ^ i)) = coeff (3 ^ (k - i)) H := by
  intro i
  induction i with
  | zero => intro k _; simp
  | succ i ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ 3 i, pow_mul, cube_eq_expand, coeff_expand, if_pos (dvd_pow_self 3 (by omega)),
      pow_succ, Nat.mul_div_cancel _ (by norm_num), ih j (by omega),
      show j + 1 - (i + 1) = j - i by omega]

/-- The `3^k`-th coefficient of a composition with an additive outer series. -/
lemma coeff_additive_subst (G H : PowerSeries K) (hG : Additive G) (hH0 : constantCoeff H = 0)
    (k : ℕ) : coeff (3 ^ k) (G.subst H) =
      ∑ i ∈ Finset.range (k + 1), coeff (3 ^ i) G * coeff (3 ^ (k - i)) H := by
  have hs : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  rw [coeff_subst' hs]
  have hsupp : (Function.support fun d => coeff d G • coeff (3 ^ k) (H ^ d)) ⊆
      (((Finset.range (k + 1)).image (fun i => 3 ^ i) : Finset ℕ) : Set ℕ) := by
    intro d hd
    simp only [Function.mem_support] at hd
    by_cases hdp : ∃ j, d = 3 ^ j
    · obtain ⟨j, rfl⟩ := hdp
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨j, ?_, rfl⟩
      by_contra hj
      apply hd
      rw [coeff_pow_eq_zero hH0 (Nat.pow_lt_pow_right (by norm_num) (by omega)), smul_zero]
    · exfalso
      push Not at hdp
      exact hd (by rw [hG d hdp, zero_smul])
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun i _ j _ h => Nat.pow_right_injective (by norm_num : 2 ≤ 3) h)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [smul_eq_mul, coeff_pow3_pow H i k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- The recursion for `c k = [x^(3^k)] F`: `2 c_k + Σ_{0<i<k} c_i c_{k-i} = [k = 1]`. -/
lemma rec_c (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst F = X + X ^ 3) (k : ℕ) (hk : 1 ≤ k) :
    2 * coeff (3 ^ k) F + ∑ i ∈ Finset.range (k + 1),
      (if i = 0 ∨ i = k then 0 else coeff (3 ^ i) F * coeff (3 ^ (k - i)) F) =
      if k = 1 then 1 else 0 := by
  have hadd := residue F h0 h1 hF
  have hm2 : 2 ≤ 3 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  have hl := lin F h0 h1 (3 ^ k) hm2
  have hT0 : constantCoeff (tr (3 ^ k) F) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_tr, if_pos (by omega),
      coeff_zero_eq_constantCoeff_apply, h0]
  have hTadd : Additive (tr (3 ^ k) F) := by
    intro j hj
    rw [coeff_tr]
    split_ifs
    · exact hadd j hj
    · rfl
  have hTT := coeff_additive_subst (tr (3 ^ k) F) (tr (3 ^ k) F) hTadd hT0 k
  have hsum : ∑ i ∈ Finset.range (k + 1),
      coeff (3 ^ i) (tr (3 ^ k) F) * coeff (3 ^ (k - i)) (tr (3 ^ k) F) =
      ∑ i ∈ Finset.range (k + 1),
        (if i = 0 ∨ i = k then 0 else coeff (3 ^ i) F * coeff (3 ^ (k - i)) F) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_tr, coeff_tr]
    by_cases h0i : i = 0
    · subst h0i
      simp
    · by_cases hki : i = k
      · subst hki
        simp
      · have a1 : 3 ^ i < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
        have a2 : 3 ^ (k - i) < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
        rw [if_pos a1, if_pos a2, if_neg (by tauto)]
  have hFF : coeff (3 ^ k) (F.subst F) = if k = 1 then 1 else 0 := by
    rw [hF, map_add, coeff_X, coeff_X_pow]
    have n1 : 3 ^ k ≠ 1 := by
      have := Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 3); omega
    rw [if_neg n1]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have n3 : 3 ^ k ≠ 3 := by
        intro h
        have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (pow_one 3).symm)
        exact hk1 this
      rw [if_neg n3, if_neg hk1, add_zero]
  rw [hTT, hsum, hFF] at hl
  linear_combination -hl

lemma c6_zero (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst F = X + X ^ 3) : coeff (3 ^ 6) F = 0 := by
  have r1 := rec_c F h0 h1 hF 1 (by norm_num)
  have r2 := rec_c F h0 h1 hF 2 (by norm_num)
  have r3 := rec_c F h0 h1 hF 3 (by norm_num)
  have r4 := rec_c F h0 h1 hF 4 (by norm_num)
  have r5 := rec_c F h0 h1 hF 5 (by norm_num)
  have r6 := rec_c F h0 h1 hF 6 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at r1 r2 r3 r4 r5 r6
  norm_num at r1 r2 r3 r4 r5 r6 ⊢
  generalize coeff 3 F = a1 at *
  generalize coeff 9 F = a2 at *
  generalize coeff 27 F = a3 at *
  generalize coeff 81 F = a4 at *
  generalize coeff 243 F = a5 at *
  generalize coeff 729 F = a6 at *
  have e1 : a1 = 2 := by clear r2 r3 r4 r5 r6; revert a1; decide
  subst e1
  have e2 : a2 = 1 := by clear r1 r3 r4 r5 r6; revert a2; decide
  subst e2
  have e3 : a3 = 1 := by clear r1 r2 r4 r5 r6; revert a3; decide
  subst e3
  have e4 : a4 = 2 := by clear r1 r2 r3 r5 r6; revert a4; decide
  subst e4
  have e5 : a5 = 1 := by clear r1 r2 r3 r4 r6; revert a5; decide
  subst e5
  clear r1 r2 r3 r4 r5
  revert a6
  decide

/-- **A107099, vanishing part.**  For every integer power series `A` with `A(0) = 0`,
`[x^1] A = 1` and `A(A(x)) = x + 4 x^3`, the coefficient `[x^n] A` is divisible by 3 whenever
`n` is not a power of 3. -/
theorem hanna_a107099 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst A = X + 4 * X ^ 3) (n : ℕ) (hn : ∀ k, n ≠ 3 ^ k) : (3 : ℤ) ∣ coeff n A := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst A := HasSubst.of_constantCoeff_zero' h0
  have h4 : (4 : PowerSeries K) = 1 := by
    simpa only [map_ofNat, map_one] using
      congrArg (C : K →+* PowerSeries K) (show (4 : K) = 1 by decide)
  have hm : (A.map f).subst (A.map f) = X + X ^ 3 := by
    have e := map_subst hs (h := f) A
    have h := congrArg (PowerSeries.map f) hA
    rw [map_add, map_mul, map_pow, map_X, map_ofNat, h4, one_mul] at h
    exact e.symm.trans h
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hr := residue (A.map f) hc0 hc1 hm n hn
  rw [coeff_map] at hr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hr

/-- **A107099, the non-vanishing reading fails.**  For every integer power series `A` as above,
`3` divides `[x^729] A` although `729 = 3^6` is a power of 3. -/
theorem hanna_a107099_counterexample (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (h1 : coeff 1 A = 1) (hA : A.subst A = X + 4 * X ^ 3) : (3 : ℤ) ∣ coeff (3 ^ 6) A := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst A := HasSubst.of_constantCoeff_zero' h0
  have h4 : (4 : PowerSeries K) = 1 := by
    simpa only [map_ofNat, map_one] using
      congrArg (C : K →+* PowerSeries K) (show (4 : K) = 1 by decide)
  have hm : (A.map f).subst (A.map f) = X + X ^ 3 := by
    have e := map_subst hs (h := f) A
    have h := congrArg (PowerSeries.map f) hA
    rw [map_add, map_mul, map_pow, map_X, map_ofNat, h4, one_mul] at h
    exact e.symm.trans h
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hr := c6_zero (A.map f) hc0 hc1 hm
  rw [coeff_map] at hr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hr

end HannaA107099

#print axioms HannaA107099.hanna_a107099
#print axioms HannaA107099.hanna_a107099_counterexample
