import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

set_option autoImplicit false

/-!
# OEIS A376230: the odd terms

A376230 (Paul D. Hanna, Sep 23 2024), offset 1, NAME:
"G.f. A(x) satisfies A(x)^2 = A(x*A(x) + x*A(x)^2 + x*A(x)^3)."
COMMENT: "It appears that, for n >= 1, a(n) is odd iff n = 4*A000695(k) + {0,1,2,3} for
some k >= 0."  Here A000695 (Moser–de Bruijn) lists the sums of distinct powers of 4, i.e. the
numbers whose base-4 digits are all 0 or 1.

We prove, for every integer power series `A` with `A(0) = 0`, `a(1) = 1` and
`A^2 = A(X*A + X*A^2 + X*A^3)`:

* `hanna_a376230`: for `n ≥ 1`, `a(n)` is odd iff `n % 8 < 4` and `⌊n/8⌋ ∈ A000695`;
* `hanna_a376230_literal_false`: the comment as stated is false (it fails at `n = 4`,
  since `4 = 4*1 + 0` with `1 ∈ A000695`, but `a(4)` is even).

Proof, modulo 2.  Let `F` be the reduction of `A` and `G = X*F + X*F^2 + X*F^3`.
1. Frobenius: `F^2 = F(X^2)`, so the equation reads `F(X^2) = F(G)`.
2. Cancellation: `F` has a compositional inverse (`F(0) = 0`, `[X]F = 1`), so `G = X^2`,
   i.e. `F + F^2 + F^3 = X`.
3. `U = 1 + F` satisfies `U^3 = 1 + X`, hence `U(X^4) = U^4 = (1 + X) U`, i.e.
   `u(0) = 1` and `u(n) = u(n-1) + [4 ∣ n] u(n/4)` for `n ≥ 1`.
4. The indicator of `{n | n % 8 < 4 ∧ ⌊n/8⌋ ∈ A000695}` satisfies the same recursion
   (case analysis on `n % 8`, using `q ∈ A000695 ↔ q % 4 ≤ 1 ∧ ⌊q/4⌋ ∈ A000695`).
-/

noncomputable section
namespace HannaA376230
open PowerSeries

local notation "K" => ZMod 2

/-! ### Moser–de Bruijn numbers (A000695) -/

/-- Membership in A000695 (Moser–de Bruijn numbers): all base-4 digits are `0` or `1`. -/
def InMoser (m : ℕ) : Prop := ∀ d ∈ Nat.digits 4 m, d ≤ 1

instance (m : ℕ) : Decidable (InMoser m) :=
  inferInstanceAs (Decidable (∀ d ∈ Nat.digits 4 m, d ≤ 1))

lemma inMoser_zero : InMoser 0 := by
  simp [InMoser]

/-- Peeling off the last base-4 digit. -/
lemma inMoser_iff (q : ℕ) : InMoser q ↔ q % 4 ≤ 1 ∧ InMoser (q / 4) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [inMoser_zero]
  · unfold InMoser
    rw [Nat.digits_def' (by norm_num) hq, List.forall_mem_cons]

lemma inMoser_one : InMoser 1 :=
  (inMoser_iff 1).mpr ⟨by norm_num, by rw [show (1 : ℕ) / 4 = 0 by norm_num]; exact inMoser_zero⟩

/-! ### The corrected parity pattern and its recursion -/

/-- The corrected pattern: `n % 8 < 4` and `⌊n/8⌋ ∈ A000695`. -/
def Pat (n : ℕ) : Prop := n % 8 < 4 ∧ InMoser (n / 8)

instance (n : ℕ) : Decidable (Pat n) :=
  inferInstanceAs (Decidable (n % 8 < 4 ∧ InMoser (n / 8)))

/-- The indicator of the pattern, in `ZMod 2`. -/
def g (n : ℕ) : K := if Pat n then 1 else 0

lemma g_zero : g 0 = 1 := by
  have h : Pat 0 := by
    unfold Pat
    exact ⟨by norm_num, by rw [Nat.zero_div]; exact inMoser_zero⟩
  unfold g
  rw [if_pos h]

/-- The indicator satisfies `g(n) = g(n-1) + [4 ∣ n] g(n/4)` for `n ≥ 1`. -/
lemma g_rec (n : ℕ) : g (n + 1) = g n + (if 4 ∣ n + 1 then g ((n + 1) / 4) else 0) := by
  by_cases hA : (n + 1) % 8 = 4
  · -- `n + 1 ≡ 4 (mod 8)`: `g (n+1) = 0`, and `g n = g ((n+1)/4) = [q ∈ A000695]`.
    have h4 : 4 ∣ n + 1 := by omega
    have hP1 : ¬ Pat (n + 1) := by
      unfold Pat
      rintro ⟨h, -⟩
      omega
    have hPn : Pat n ↔ InMoser ((n + 1) / 8) := by
      unfold Pat
      rw [show n / 8 = (n + 1) / 8 by omega]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have hPq : Pat ((n + 1) / 4) ↔ InMoser ((n + 1) / 8) := by
      unfold Pat
      rw [inMoser_iff ((n + 1) / 8), show (n + 1) / 4 / 8 = (n + 1) / 8 / 4 by omega]
      exact ⟨fun h => ⟨by have := h.1; omega, h.2⟩, fun h => ⟨by have := h.1; omega, h.2⟩⟩
    rw [if_pos h4]
    unfold g
    rw [if_neg hP1, if_congr hPn rfl rfl, if_congr hPq rfl rfl]
    split_ifs <;> decide
  · by_cases hB : (n + 1) % 8 = 0
    · -- `n + 1 ≡ 0 (mod 8)`: `g n = 0`, and `g (n+1) = g ((n+1)/4) = [q ∈ A000695]`.
      have h4 : 4 ∣ n + 1 := by omega
      have hPn : ¬ Pat n := by
        unfold Pat
        rintro ⟨h, -⟩
        omega
      have hP1 : Pat (n + 1) ↔ InMoser ((n + 1) / 8) := by
        unfold Pat
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      have hPq : Pat ((n + 1) / 4) ↔ InMoser ((n + 1) / 8) := by
        unfold Pat
        rw [inMoser_iff ((n + 1) / 8), show (n + 1) / 4 / 8 = (n + 1) / 8 / 4 by omega]
        exact ⟨fun h => ⟨by have := h.1; omega, h.2⟩, fun h => ⟨by have := h.1; omega, h.2⟩⟩
      rw [if_pos h4]
      unfold g
      rw [if_neg hPn, zero_add, if_congr hP1 rfl rfl, if_congr hPq rfl rfl]
    · -- otherwise `4 ∤ n + 1`, and `n`, `n + 1` lie in the same half of the same block of 8.
      have h4 : ¬ 4 ∣ n + 1 := by omega
      have hP : Pat (n + 1) ↔ Pat n := by
        unfold Pat
        rw [show (n + 1) / 8 = n / 8 by omega]
        exact ⟨fun h => ⟨by have := h.1; omega, h.2⟩, fun h => ⟨by have := h.1; omega, h.2⟩⟩
      rw [if_neg h4, add_zero]
      unfold g
      exact if_congr hP rfl rfl

/-! ### Power series over `ZMod 2` -/

lemma two_eq_zero_K : (2 : K) = 0 := by decide

lemma two_eq_zero_PS : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) two_eq_zero_K

/-- Frobenius in `(ZMod 2)[[X]]`: squaring is the substitution `X ↦ X^2`. -/
lemma sq_eq_expand (F : PowerSeries K) : F ^ 2 = expand 2 two_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 2 two_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

/-- Cancellation: a series with zero constant term and linear coefficient `1` has a
compositional inverse, so substitution into it is injective. -/
lemma subst_cancel (F u v : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) (h : F.subst u = F.subst v) :
    u = v := by
  have hF : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  have hsu : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  have hsv : HasSubst v := HasSubst.of_constantCoeff_zero' hv
  have hunit : IsUnit (coeff 1 F) := by rw [h1]; exact isUnit_one
  set Q := F.substInvOfIsUnit hunit with hQdef
  have hQ : Q.subst F = X := subst_substInvOfIsUnit_left F h0 hunit
  have eu : Q.subst (F.subst u) = u := by
    rw [← subst_comp_subst_apply hF hsu Q, hQ, subst_X hsu]
  have ev : Q.subst (F.subst v) = v := by
    rw [← subst_comp_subst_apply hF hsv Q, hQ, subst_X hsv]
  rw [← eu, ← ev, h]

/-- The statement in `(ZMod 2)[[X]]`: the coefficients of `1 + F` are given by `g`. -/
theorem residue (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F ^ 2 = F.subst (X * F + X * F ^ 2 + X * F ^ 3)) (n : ℕ) :
    coeff n (1 + F) = g n := by
  -- Step 1: Frobenius turns the equation into `F(X^2) = F(G)`.
  have hG0 : constantCoeff (X * F + X * F ^ 2 + X * F ^ 3 : PowerSeries K) = 0 := by simp
  have hX20 : constantCoeff (X ^ 2 : PowerSeries K) = 0 := by simp
  have hFX2 : F.subst (X ^ 2 : PowerSeries K) = F.subst (X * F + X * F ^ 2 + X * F ^ 3) := by
    rw [← expand_apply 2 two_ne_zero, ← sq_eq_expand]
    exact hF
  -- Step 2: cancellation gives `G = X^2`, i.e. `F + F^2 + F^3 = X`.
  have hG : (X ^ 2 : PowerSeries K) = X * F + X * F ^ 2 + X * F ^ 3 :=
    subst_cancel F _ _ h0 h1 hX20 hG0 hFX2
  have hFX : F + F ^ 2 + F ^ 3 = X := by
    have h' : X * (F + F ^ 2 + F ^ 3) = X * X := by linear_combination -hG
    ext k
    have hk := congrArg (coeff (k + 1)) h'
    rwa [coeff_succ_X_mul, coeff_succ_X_mul] at hk
  -- Step 3: `U = 1 + F` is a cube root of `1 + X`.
  set U : PowerSeries K := 1 + F with hUdef
  have hU3 : U ^ 3 = 1 + X := by
    rw [hUdef]
    linear_combination hFX + (F + F ^ 2) * two_eq_zero_PS
  -- Step 4: `U(X^4) = U^4 = (1 + X) U`, read off coefficientwise.
  have hU4 : ∀ m, coeff m (U ^ 4) = if 4 ∣ m then coeff (m / 4) U else 0 := by
    intro m
    have e : U ^ 4 = expand 2 two_ne_zero (expand 2 two_ne_zero U) := by
      rw [← sq_eq_expand, ← sq_eq_expand]
      ring
    rw [e, coeff_expand, coeff_expand]
    by_cases h4 : 4 ∣ m
    · rw [if_pos (show 2 ∣ m by omega), if_pos (show 2 ∣ m / 2 by omega), if_pos h4,
        show m / 2 / 2 = m / 4 by omega]
    · rw [if_neg h4]
      split_ifs <;> first | rfl | (exfalso; omega)
  have hrec : ∀ m, coeff (m + 1) U =
      coeff m U + (if 4 ∣ m + 1 then coeff ((m + 1) / 4) U else 0) := by
    intro m
    have e : U ^ 4 = U + X * U := by
      rw [show U ^ 4 = U * U ^ 3 by ring, hU3]
      ring
    have h := hU4 (m + 1)
    rw [e, map_add, coeff_succ_X_mul] at h
    linear_combination h - coeff m U * two_eq_zero_K
  have hU0 : coeff 0 U = 1 := by
    rw [hUdef, map_add, coeff_one, if_pos rfl, coeff_zero_eq_constantCoeff_apply, h0, add_zero]
  -- Step 5: strong induction against the recursion of `g`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [hU0, g_zero]
    | succ m =>
      rw [hrec m, ih m (by omega), g_rec m]
      by_cases h4 : 4 ∣ m + 1
      · rw [if_pos h4, if_pos h4, ih ((m + 1) / 4) (by omega)]
      · rw [if_neg h4, if_neg h4]

/-! ### The theorems over `ℤ` -/

/-- **A376230, corrected parity statement.**  For every integer power series `A` with
`A(0) = 0`, `a(1) = 1` and `A(x)^2 = A(x A(x) + x A(x)^2 + x A(x)^3)`, and every `n ≥ 1`,
`a(n)` is odd iff `n % 8 < 4` and `⌊n/8⌋` is a Moser–de Bruijn number (A000695). -/
theorem hanna_a376230 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1)
    (hA : A ^ 2 = A.subst (X * A + X * A ^ 2 + X * A ^ 3)) (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n A) ↔ (n % 8 < 4 ∧ InMoser (n / 8)) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hG0 : constantCoeff (X * A + X * A ^ 2 + X * A ^ 3 : PowerSeries ℤ) = 0 := by simp
  have hs : HasSubst (X * A + X * A ^ 2 + X * A ^ 3 : PowerSeries ℤ) :=
    HasSubst.of_constantCoeff_zero' hG0
  have hmapG : PowerSeries.map f (X * A + X * A ^ 2 + X * A ^ 3 : PowerSeries ℤ) =
      X * A.map f + X * (A.map f) ^ 2 + X * (A.map f) ^ 3 := by
    simp only [map_add, map_mul, map_pow, map_X]
  have hm : (A.map f) ^ 2 =
      (A.map f).subst (X * A.map f + X * (A.map f) ^ 2 + X * (A.map f) ^ 3) := by
    have h4 := congrArg (PowerSeries.map f) hA
    rw [map_pow] at h4
    rw [← hmapG]
    exact h4.trans (map_subst hs (h := f) A)
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hr := residue (A.map f) hc0 hc1 hm n
  rw [map_add, coeff_one, if_neg (show n ≠ 0 by omega), zero_add, coeff_map] at hr
  have hr' : ((coeff n A : ℤ) : K) = g n := hr
  rw [← ZMod.intCast_eq_one_iff_odd, hr']
  show g n = 1 ↔ Pat n
  unfold g
  split_ifs with hP <;> simp [hP]

/-- **The comment as stated is false.**  The literal reading
"`a(n)` odd iff `n = 4k + r` with `k ∈ A000695` and `r ≤ 3`" fails at `n = 4`
(`4 = 4*1 + 0`, `1 ∈ A000695`, but `a(4)` is even). -/
theorem hanna_a376230_literal_false (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (h1 : coeff 1 A = 1) (hA : A ^ 2 = A.subst (X * A + X * A ^ 2 + X * A ^ 3)) :
    ¬ (∀ n, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k r, InMoser k ∧ r ≤ 3 ∧ n = 4 * k + r)) := by
  intro h
  have hodd : Odd (coeff 4 A) :=
    (h 4 (by norm_num)).mpr ⟨1, 0, inMoser_one, by norm_num, by norm_num⟩
  have h8 := (hanna_a376230 A h0 h1 hA 4 (by norm_num)).mp hodd
  exact absurd h8.1 (by norm_num)

end HannaA376230

#print axioms HannaA376230.hanna_a376230
#print axioms HannaA376230.hanna_a376230_literal_false
