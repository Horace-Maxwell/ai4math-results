import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# OEIS A120566: all terms are odd

A120566, offset 1, NAME: "G.f. satisfies: A(x) = A(A(x)) - x*A(A(A(x))), with A(0) = 0."
COMMENT: "It appears that all terms are odd. - _Paul D. Hanna_, Jun 04 2026"
Data: `1, 1, 1, 3, 7, 33, 109, ...` (so `a(1) = 1`).

We prove: every integer power series `A` with `A(0) = 0`, `a(1) = 1` and
`A = A(A(x)) - x*A(A(A(x)))` has all coefficients `a(n)`, `n ≥ 1`, odd.
(The normalization `a(1) = 1` is needed: `A = 0` also solves the equation.)

Proof: modulo 2 the equation reads `F = F∘F - x F∘F∘F`, and `E = x/(1-x)` is a solution,
because `E∘E = x/(1-2x) = x` and `x - x E = E` modulo 2.  Uniqueness: let `D = F - E` with
`x^n ∣ D` (`n ≥ 2`).  Then
`D = D∘F + (E∘F - E∘E) - x (F∘F∘F - E∘E∘E)`.  Modulo `x^(n+1)`:
`D∘F ≡ D` (since `F = x·(1 + ...)`), `E∘F - E∘E = D / ((1-F)(1-E)) ≡ D`, and the last term
vanishes because composition respects congruences modulo `x^n`.  Hence `D ≡ 2D`, i.e.
`x^(n+1) ∣ D`.
-/

noncomputable section
namespace HannaA120566
open PowerSeries

local notation "K" => ZMod 2

lemma two_eq_zero : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (2 : K) = 0 by decide)

/-! ### Composition respects congruences modulo `X^n` -/

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

lemma subst_congr_left (F1 F2 G : PowerSeries K) (hG : constantCoeff G = 0) (n : ℕ)
    (h : X ^ n ∣ F1 - F2) : X ^ n ∣ F1.subst G - F2.subst G := by
  have hs : HasSubst G := HasSubst.of_constantCoeff_zero' hG
  obtain ⟨Q, hQ⟩ := h
  rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG) n) _

lemma subst_congr (F1 F2 G1 G2 : PowerSeries K) (hG1 : constantCoeff G1 = 0)
    (hG2 : constantCoeff G2 = 0) (n : ℕ) (hF : X ^ n ∣ F1 - F2) (hG : X ^ n ∣ G1 - G2) :
    X ^ n ∣ F1.subst G1 - F2.subst G2 := by
  have e : F1.subst G1 - F2.subst G2 =
      (F1.subst G1 - F2.subst G1) + (F2.subst G1 - F2.subst G2) := by ring
  rw [e]
  exact dvd_add (subst_congr_left F1 F2 G1 hG1 n hF)
    (subst_congr_right F2 G1 G2 (HasSubst.of_constantCoeff_zero' hG1)
      (HasSubst.of_constantCoeff_zero' hG2) n hG)

lemma const_subst {F G : PowerSeries K} (hF : constantCoeff F = 0) (hG : constantCoeff G = 0) :
    constantCoeff (F.subst G) = 0 :=
  constantCoeff_subst_eq_zero hG F hF

/-! ### The explicit solution `E = x/(1-x)` -/

def E : PowerSeries K := PowerSeries.mk fun n => if n = 0 then 0 else 1

lemma E_mul : E * (1 - X) = X := by
  ext n
  rcases n with _ | _ | n <;> simp [E, mul_sub, coeff_X, coeff_succ_mul_X]

lemma E_const : constantCoeff E = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [E]

lemma E_one : coeff 1 E = 1 := by simp [E]

lemma subst_one' {a : PowerSeries K} (ha : HasSubst a) : (1 : PowerSeries K).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

lemma E_subst_mul {a : PowerSeries K} (ha : HasSubst a) : E.subst a * (1 - a) = a := by
  have h := congrArg (fun f => f.subst a) E_mul
  simp only [subst_mul ha, subst_sub ha, subst_X ha, subst_one' ha] at h
  exact h

lemma hsE : HasSubst E := HasSubst.of_constantCoeff_zero' E_const

/-- `E` is an involution modulo 2. -/
lemma E_E : E.subst E = X := by
  have he := E_subst_mul hsE
  linear_combination (1 - X) * he + (E.subst E + 1) * E_mul + (E.subst E * X) * two_eq_zero

lemma E_eq : E = E.subst E - X * E.subst (E.subst E) := by
  rw [E_E, X_subst]
  linear_combination E_mul + (X * E) * two_eq_zero

/-- The statement in `(ZMod 2)[[X]]`. -/
theorem residue (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F = F.subst F - X * F.subst (F.subst F)) : F = E := by
  have hsF : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  have hE := E_eq
  have hFF : constantCoeff (F.subst F) = 0 := const_subst h0 h0
  have hEE : constantCoeff (E.subst E) = 0 := const_subst E_const E_const
  -- `F = X * U` with `U(0) = 1`
  obtain ⟨U, hU⟩ : (X : PowerSeries K) ∣ F := X_dvd_iff.mpr h0
  have hU0 : constantCoeff U = 1 := by
    have h := congrArg (coeff 1) hU
    rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have key : ∀ n, 2 ≤ n → X ^ n ∣ F - E := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [map_sub, coeff_zero_eq_constantCoeff_apply, h0, E_const]
      · simp [map_sub, h1, E_one]
    | succ n hn ih =>
      -- (i) the triple compositions agree modulo `X^n`
      have hS2 : X ^ n ∣ F.subst F - E.subst E := subst_congr F E F E h0 E_const n ih ih
      have hS3 : X ^ n ∣ F.subst (F.subst F) - E.subst (E.subst E) :=
        subst_congr F E (F.subst F) (E.subst E) hFF hEE n ih hS2
      -- (ii) `R = E∘F - E∘E` satisfies `R * W = F - E` with `W = (1-F)(1-E)` a unit
      set R := E.subst F - E.subst E with hRdef
      have hRW : R * ((1 - F) * (1 - E)) = F - E := by
        have h1' := E_subst_mul hsF
        have h2' := E_subst_mul hsE
        rw [hRdef]
        linear_combination (1 - E) * h1' - (1 - F) * h2'
      have hWu : IsUnit ((1 - F) * (1 - E)) := by
        rw [isUnit_iff_constantCoeff]
        simp [h0, E_const]
      have hXW : (X : PowerSeries K) ∣ 1 - (1 - F) * (1 - E) := by
        rw [X_dvd_iff]
        simp [h0, E_const]
      have hRn : X ^ n ∣ R := by
        have : X ^ n ∣ R * ((1 - F) * (1 - E)) := by rw [hRW]; exact ih
        exact (hWu.dvd_mul_right).mp this
      have hRD : X ^ (n + 1) ∣ R - (F - E) := by
        have e : R - (F - E) = R * (1 - (1 - F) * (1 - E)) := by rw [← hRW]; ring
        rw [e, pow_succ]
        exact mul_dvd_mul hRn hXW
      -- (iii) `D∘F ≡ D` modulo `X^(n+1)`
      obtain ⟨Q, hQ⟩ := ih
      have hDF : X ^ (n + 1) ∣ (F - E).subst F - (F - E) := by
        have e1 : (F - E).subst F = F ^ n * Q.subst F := by
          rw [hQ, subst_mul hsF, subst_pow hsF, subst_X hsF]
        have e2 : (F - E).subst F - (F - E) =
            X ^ n * ((U ^ n - 1) * Q.subst F + (Q.subst F - Q)) := by
          rw [e1, hQ, hU]; ring
        rw [e2, pow_succ]
        refine mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left ?_ _) ?_)
        · rw [X_dvd_iff]; simp [hU0]
        · have hXF : (X : PowerSeries K) ^ 1 ∣ F - X := by
            rw [pow_one, X_dvd_iff]; simp [h0]
          have := subst_congr_right Q F X hsF HasSubst.X' 1 hXF
          rw [X_subst, pow_one] at this
          exact this
      -- (iv) combine
      have hsum : -(F - E) = ((F - E).subst F - (F - E)) + (R - (F - E)) -
          X * (F.subst (F.subst F) - E.subst (E.subst E)) := by
        have e3 : F.subst F - E.subst E = (F - E).subst F + R := by
          rw [hRdef, subst_sub hsF]; ring
        linear_combination hF - hE + e3
      have hfin : X ^ (n + 1) ∣ -(F - E) := by
        rw [hsum]
        refine dvd_sub (dvd_add hDF hRD) ?_
        rw [pow_succ']
        exact mul_dvd_mul_left X hS3
      exact (dvd_neg).mp hfin
  have hz : F - E = 0 := by
    ext m
    have h := key (m + 2) (by omega)
    rw [X_pow_dvd_iff] at h
    simpa using h m (by omega)
  exact sub_eq_zero.mp hz

/-- **A120566: all terms are odd.**  For every integer power series `A` with `A(0) = 0`,
`a(1) = 1` and `A = A(A(x)) - x*A(A(A(x)))`, every coefficient `a(n)` with `n ≥ 1` is odd. -/
theorem hanna_a120566 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1)
    (hA : A = A.subst A - X * A.subst (A.subst A)) (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n A) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst A := HasSubst.of_constantCoeff_zero' h0
  have hAA0 : constantCoeff (A.subst A) = 0 := constantCoeff_subst_eq_zero h0 A h0
  have hsAA : HasSubst (A.subst A) := HasSubst.of_constantCoeff_zero' hAA0
  have m1 : PowerSeries.map f (A.subst A) = (A.map f).subst (A.map f) := map_subst hs (h := f) A
  have m2 : PowerSeries.map f (A.subst (A.subst A)) =
      (A.map f).subst ((A.map f).subst (A.map f)) := by
    have e := map_subst hsAA (h := f) A
    refine e.trans ?_
    exact congrArg (fun g => (A.map f).subst g) m1
  have hm : A.map f = (A.map f).subst (A.map f) - X * (A.map f).subst ((A.map f).subst (A.map f)) := by
    have h := congrArg (PowerSeries.map f) hA
    rw [map_sub, map_mul, map_X, m1, m2] at h
    exact h
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hF := residue (A.map f) hc0 hc1 hm
  have hcoef := congrArg (coeff n) hF
  rw [coeff_map] at hcoef
  have hE : coeff n E = 1 := by simp [E, show n ≠ 0 by omega]
  rw [hE] at hcoef
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hcoef

end HannaA120566

#print axioms HannaA120566.hanna_a120566
