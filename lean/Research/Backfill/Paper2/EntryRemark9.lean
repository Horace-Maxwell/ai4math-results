import Research.Backfill.Paper2.Challenge
import Research.Backfill.Paper2.EntryA120566

/-! Full integer inverse equation, uniqueness and mod-two consequences of Remark 9.
The coefficient linearization below is the ring-valid argument from AdditiveCore,
specialized to integers; no modular cancellation is used in its uniqueness theorem. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.EntryRemark9
open PowerSeries BackfillPaper2.Challenge

private theorem subst_neg {H : PowerSeries ℤ} (hH : HasSubst H) (F : PowerSeries ℤ) :
    (-F).subst H = -(F.subst H) := by
  rw [← coe_substAlgHom hH, map_neg]

/-- Composition respects congruences modulo `X^n` in the inner argument. -/
private lemma subst_congr_right (F G1 G2 : PowerSeries ℤ) (hG1 : HasSubst G1) (hG2 : HasSubst G2)
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
private lemma coeff_pow_eq_zero {H : PowerSeries ℤ} (hH0 : constantCoeff H = 0) {m d : ℕ} (hd : m < d) :
    coeff m (H ^ d) = 0 := by
  have : X ^ d ∣ H ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hH0) d
  rw [X_pow_dvd_iff] at this
  exact this m hd

/-- For `d ≥ 2`, `X^(m+1) ∣ F1^d - F2^d` when `X^m ∣ F1 - F2` and both have zero constant
term. -/
private lemma pow_sub_pow_dvd {F1 F2 : PowerSeries ℤ} (h1 : constantCoeff F1 = 0)
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
private lemma coeff_subst_sub (G F1 F2 : PowerSeries ℤ) (h1 : constantCoeff F1 = 0)
    (h2 : constantCoeff F2 = 0) {m : ℕ} (hm : 1 ≤ m) (h : X ^ m ∣ F1 - F2) :
    coeff m (G.subst F1) - coeff m (G.subst F2) = coeff 1 G * (coeff m F1 - coeff m F2) := by
  have hs1 : HasSubst F1 := HasSubst.of_constantCoeff_zero' h1
  have hs2 : HasSubst F2 := HasSubst.of_constantCoeff_zero' h2
  rw [coeff_subst' hs1, coeff_subst' hs2]
  have sup : ∀ F : PowerSeries ℤ, constantCoeff F = 0 →
      (Function.support fun d => coeff d G • coeff m (F ^ d)) ⊆ (Finset.range (m + 1) : Set ℕ) := by
    intro F hF d hd
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero hF (by omega), smul_zero])
  rw [finsum_eq_sum_of_support_subset _ (sup F1 h1), finsum_eq_sum_of_support_subset _ (sup F2 h2),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 1]
  · simp [mul_sub]
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
private def tr (m : ℕ) (F : PowerSeries ℤ) : PowerSeries ℤ := ((trunc m F : Polynomial ℤ) : PowerSeries ℤ)

private lemma coeff_tr (m k : ℕ) (F : PowerSeries ℤ) :
    coeff k (tr m F) = if k < m then coeff k F else 0 := by
  rw [tr, Polynomial.coeff_coe, coeff_trunc]

/-- Linearization at degree `m ≥ 2`: `[x^m] F∘F - [x^m] T∘T = 2 f_m` with `T = tr m F`. -/
private lemma lin (F : PowerSeries ℤ) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1) (m : ℕ)
    (hm1 : 2 ≤ m) :
    coeff m (F.subst F) - coeff m ((tr m F).subst (tr m F)) = 2 * coeff m F := by
  have hsF : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  set T := tr m F with hT
  have hTc : ∀ k, coeff k T = if k < m then coeff k F else 0 := fun k => coeff_tr m k F
  have hT0 : constantCoeff T = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hTc, ite_eq_left (by omega),
      coeff_zero_eq_constantCoeff_apply, h0]
  have hT1 : coeff 1 T = 1 := by rw [hTc, ite_eq_left (by omega), h1]
  have hTm : coeff m T = 0 := by rw [hTc, ite_eq_right (lt_irrefl m)]
  have hdvd : X ^ m ∣ F - T := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hTc, ite_eq_left hk, sub_self]
  have e1 : coeff m (F.subst F) - coeff m (T.subst F) = coeff m F := by
    obtain ⟨Q, hQ⟩ := hdvd
    obtain ⟨U, hU⟩ : (X : PowerSeries ℤ) ∣ F := X_dvd_iff.mpr h0
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
      have hXF : (X : PowerSeries ℤ) ^ 1 ∣ F - X := by
        rw [pow_one, X_dvd_iff]; simp [h0]
      have := subst_congr_right Q F X hsF HasSubst.X' 1 hXF
      rw [X_subst, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
      exact this
    have hQm : constantCoeff Q = coeff m F := by
      have h := congrArg (coeff m) hQ
      rw [map_sub, hTm, sub_zero, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply] at h
      exact h.symm
    rw [← map_sub, e, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hU0, one_pow, one_mul, hQF, hQm]
  have e2 : coeff m (T.subst F) - coeff m (T.subst T) = coeff m F := by
    rw [coeff_subst_sub T F T h0 hT0 (by omega) hdvd, hT1, hTm, sub_zero, one_mul]
  linear_combination e1 + e2


private theorem subst_congr_left (F G H : PowerSeries ℤ) (hH : constantCoeff H = 0)
    (n : ℕ) (h : X ^ n ∣ F - G) : X ^ n ∣ F.subst H - G.subst H := by
  have hs := HasSubst.of_constantCoeff_zero' hH
  obtain ⟨Q, hQ⟩ := h
  rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hH) n) _

private theorem subst_congr (F G H I : PowerSeries ℤ) (hH : constantCoeff H = 0)
    (hI : constantCoeff I = 0) (n : ℕ) (hFG : X ^ n ∣ F - G) (hHI : X ^ n ∣ H - I) :
    X ^ n ∣ F.subst H - G.subst I := by
  have he : F.subst H - G.subst I = (F.subst H - G.subst H) + (G.subst H - G.subst I) := by ring
  rw [he]
  exact dvd_add (subst_congr_left F G H hH n hFG)
    (subst_congr_right G H I (HasSubst.of_constantCoeff_zero' hH)
      (HasSubst.of_constantCoeff_zero' hI) n hHI)

private theorem inverse_unique (B C : PowerSeries ℤ)
    (hB0 : constantCoeff B = 0) (hB1 : coeff 1 B = 1) (hB : EqInv120566 B)
    (hC0 : constantCoeff C = 0) (hC1 : coeff 1 C = 1) (hC : EqInv120566 C) : B = C := by
  apply PowerSeries.ext
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm0 : m = 0
    · subst m; simp only [coeff_zero_eq_constantCoeff_apply, hB0, hC0]
    by_cases hm1 : m = 1
    · subst m; rw [hB1, hC1]
    have hm : 2 ≤ m := by omega
    have hd : X ^ m ∣ B - C := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, ih j hj, sub_self]
    have hT : tr m B = tr m C := by
      ext j
      rw [coeff_tr, coeff_tr]
      by_cases hj : j < m
      · rw [ite_eq_left hj, ite_eq_left hj, ih j hj]
      · rw [ite_eq_right hj, ite_eq_right hj]
    have hlB := lin B hB0 hB1 m hm
    have hlC := lin C hC0 hC1 m hm
    rw [hT] at hlB
    have hd2 : X ^ m ∣ B.subst B - C.subst C := subst_congr B C B C hB0 hC0 m hd hd
    have hBB0 : constantCoeff (B.subst B) = 0 := constantCoeff_subst_eq_zero hB0 B hB0
    have hCC0 : constantCoeff (C.subst C) = 0 := constantCoeff_subst_eq_zero hC0 C hC0
    have hd3 : X ^ m ∣ B.subst (B.subst B) - C.subst (C.subst C) :=
      subst_congr B C (B.subst B) (C.subst C) hBB0 hCC0 m hd hd2
    have hx : X ^ (m + 1) ∣ X * B.subst (B.subst B) - X * C.subst (C.subst C) := by
      rw [← mul_sub, pow_succ']
      exact mul_dvd_mul_left X hd3
    rw [X_pow_dvd_iff] at hx
    have he : coeff m (X * B.subst (B.subst B)) - coeff m (X * C.subst (C.subst C)) = 0 := by
      simpa only [map_sub] using hx m (by omega)
    have hb := congrArg (coeff m) hB
    have hc := congrArg (coeff m) hC
    simp only [map_add] at hb hc
    linear_combination -hb + hc - hlB + hlC - he

private theorem conjugate_equation (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : Eq120566 A) : EqInv120566 (-(A.subst (-(X : PowerSeries ℤ)))) := by
  let N : PowerSeries ℤ := -X
  let T : PowerSeries ℤ := -(A.subst N)
  have hn0 : constantCoeff N = 0 := by simp [N]
  have hsN := HasSubst.of_constantCoeff_zero' hn0
  have ht0 : constantCoeff T = 0 := by
    have hz : constantCoeff (A.subst N) = 0 := constantCoeff_subst_eq_zero hn0 A h0
    simpa [T] using congrArg Neg.neg hz
  have hsT := HasSubst.of_constantCoeff_zero' ht0
  have hT2 : T.subst T = -(PowerSeries.subst N (A.subst A)) := by
    dsimp only [T]
    rw [subst_neg hsT, subst_comp_subst_apply hsN hsT A]
    have hn : PowerSeries.subst T N = A.subst N := by
      dsimp only [N]
      rw [subst_neg hsT, subst_X hsT]
      dsimp only [T]
      rw [neg_neg]
    rw [hn, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' h0) hsN A]
  have htt0 : constantCoeff (T.subst T) = 0 := constantCoeff_subst_eq_zero ht0 T ht0
  have hsTT := HasSubst.of_constantCoeff_zero' htt0
  have hT3 : T.subst (T.subst T) = -(PowerSeries.subst N (A.subst (A.subst A))) := by
    dsimp only [T]
    rw [subst_neg hsTT, subst_comp_subst_apply hsN hsTT A]
    have hn : PowerSeries.subst (T.subst T) N = PowerSeries.subst N (A.subst A) := by
      dsimp only [N]
      rw [subst_neg hsTT, subst_X hsTT, hT2, neg_neg]
    rw [hn, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by
      exact constantCoeff_subst_eq_zero h0 A h0)) hsN A]
  have he := congrArg (fun F : PowerSeries ℤ => F.subst N) hA
  simp only [subst_sub hsN, subst_mul hsN, subst_X hsN] at he
  change T = T.subst T + X * T.subst (T.subst T)
  rw [hT3, hT2]
  dsimp only [T, N] at he ⊢
  linear_combination -he

private theorem inverse_equation (A B : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : Eq120566 A) (hB0 : constantCoeff B = 0) (hAB : A.subst B = X) : EqInv120566 B := by
  have hsA := HasSubst.of_constantCoeff_zero' h0
  have hsB := HasSubst.of_constantCoeff_zero' hB0
  have hb2 : constantCoeff (B.subst B) = 0 := constantCoeff_subst_eq_zero hB0 B hB0
  have hsB2 := HasSubst.of_constantCoeff_zero' hb2
  have hb3 : constantCoeff (B.subst (B.subst B)) = 0 := constantCoeff_subst_eq_zero hb2 B hB0
  have hsB3 := HasSubst.of_constantCoeff_zero' hb3
  have hAB2 : A.subst (B.subst B) = B := by
    rw [← subst_comp_subst_apply hsB hsB A, hAB, subst_X hsB]
  have hAB3 : A.subst (B.subst (B.subst B)) = B.subst B := by
    rw [← subst_comp_subst_apply hsB hsB2 A, hAB, subst_X hsB2]
  have hA2 : PowerSeries.subst (B.subst (B.subst B)) (A.subst A) = B := by
    rw [subst_comp_subst_apply hsA hsB3 A, hAB3, hAB2]
  have hAA0 : constantCoeff (A.subst A) = 0 := constantCoeff_subst_eq_zero h0 A h0
  have hA3 : PowerSeries.subst (B.subst (B.subst B)) (A.subst (A.subst A)) = X := by
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hAA0) hsB3 A, hA2, hAB]
  have he := congrArg (fun F : PowerSeries ℤ => F.subst (B.subst (B.subst B))) hA
  simp only [subst_sub hsB3, subst_mul hsB3, subst_X hsB3, hAB3, hA2, hA3] at he
  change B = B.subst B + X * B.subst (B.subst B)
  linear_combination -he


private theorem conjugate_zero (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) :
    constantCoeff (-(A.subst (-(X : PowerSeries ℤ)))) = 0 := by
  have hz : constantCoeff (PowerSeries.subst (-(X : PowerSeries ℤ)) A) = 0 := constantCoeff_subst_eq_zero (show constantCoeff (-(X : PowerSeries ℤ)) = 0 by simp) A h0
  rw [map_neg, hz, neg_zero]

private theorem conjugate_one (A : PowerSeries ℤ) (h1 : coeff 1 A = 1) :
    coeff 1 (-(A.subst (-(X : PowerSeries ℤ)))) = 1 := by
  have hr : A.subst (-(X : PowerSeries ℤ)) = rescale (-1 : ℤ) A := by
    simpa only [Algebra.smul_def, map_neg, map_one, neg_one_mul] using (rescale_eq_subst (-1 : ℤ) A).symm
  rw [map_neg, hr, coeff_rescale, h1]
  norm_num

private theorem conjugate_inverse (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (h1 : coeff 1 A = 1) (hA : Eq120566 A) :
    A.subst (-(A.subst (-(X : PowerSeries ℤ)))) = X := by
  have hu : IsUnit (coeff 1 A) := by rw [h1]; exact isUnit_one
  let B := substInvOfIsUnit A hu
  have hb0 : constantCoeff B = 0 := constantCoeff_substInvOfIsUnit A hu
  have hb1 : coeff 1 B = 1 := by
    have hunit : hu.unit = 1 := Units.ext (hu.unit_spec.trans h1)
    dsimp only [B]
    rw [coeff_one_substInvOfIsUnit, hunit]
    simp
  have hAB : A.subst B = X := subst_substInvOfIsUnit_right A h0 hu
  have he : -(A.subst (-X)) = B :=
    inverse_unique _ _ (conjugate_zero A h0) (conjugate_one A h1)
      (conjugate_equation A h0 hA) hb0 hb1 (inverse_equation A B h0 hA hb0 hAB)
  rw [he, hAB]

private theorem reduced_conjugate (A : PowerSeries ℤ) :
    red 2 (-(A.subst (-(X : PowerSeries ℤ)))) = red 2 A := by
  have hs : HasSubst (-(X : PowerSeries ℤ)) := HasSubst.of_constantCoeff_zero' (by simp)
  have hm : red 2 (A.subst (-(X : PowerSeries ℤ))) =
      (red 2 A).subst (-(X : PowerSeries (ZMod 2))) := by
    have he : red 2 (A.subst (-(X : PowerSeries ℤ))) =
        (red 2 A).subst (red 2 (-(X : PowerSeries ℤ))) := by
      simpa only [red, PowerSeries.map] using
        (map_subst (h := Int.castRingHom (ZMod 2)) hs A)
    have hx : red 2 (-(X : PowerSeries ℤ)) = -(X : PowerSeries (ZMod 2)) := by
      simp only [red, map_neg, map_X]
    rw [he, hx]
  have hn : ∀ F : PowerSeries (ZMod 2), -F = F := by
    intro F
    linear_combination (-F) * EntryA120566.two_eq_zero
  have he : red 2 (-(A.subst (-(X : PowerSeries ℤ)))) =
      -(red 2 (A.subst (-(X : PowerSeries ℤ)))) := by simp only [red, map_neg]
  rw [he, hm, hn X, X_subst, hn]

theorem check_Rem9 : Rem9 := by
  refine ⟨conjugate_inverse, ?_, inverse_unique, ?_⟩
  · intro A h0 h1 hA
    exact ⟨conjugate_equation A h0 hA,
      fun B hB0 hAB _ => inverse_equation A B h0 hA hB0 hAB⟩
  · intro A h0 h1 hA
    have hc := reduced_conjugate A
    refine ⟨hc, ?_, ?_⟩
    · have ht0 := conjugate_zero A h0
      have hm : red 2 (A.subst (-(A.subst (-X)))) =
          (red 2 A).subst (red 2 (-(A.subst (-X)))) := by
        simpa only [red, PowerSeries.map] using
          (map_subst (h := Int.castRingHom (ZMod 2))
            (HasSubst.of_constantCoeff_zero' ht0) A)
      rw [conjugate_inverse A h0 h1 hA] at hm
      have hx : red 2 (X : PowerSeries ℤ) = X := by simp [red]
      rw [hx, hc] at hm
      exact hm.symm
    · have hs := HasSubst.of_constantCoeff_zero' h0
      have haa0 : constantCoeff (A.subst A) = 0 := constantCoeff_subst_eq_zero h0 A h0
      have hm1 : red 2 (A.subst A) = (red 2 A).subst (red 2 A) := by
        simpa only [red, PowerSeries.map] using (map_subst (h := Int.castRingHom (ZMod 2)) hs A)
      have hm2 : red 2 (A.subst (A.subst A)) = (red 2 A).subst ((red 2 A).subst (red 2 A)) := by
        have ht : red 2 (A.subst (A.subst A)) = (red 2 A).subst (red 2 (A.subst A)) := by
          simpa only [red, PowerSeries.map] using (map_subst (h := Int.castRingHom (ZMod 2))
            (HasSubst.of_constantCoeff_zero' haa0) A)
        rw [ht, hm1]
      have hr : red 2 A = red 2 (A.subst A) - X * red 2 (A.subst (A.subst A)) := by
        simpa only [red, map_sub, map_mul, map_X] using
          congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hA
      rw [hm1, hm2] at hr
      have hc0 : constantCoeff (red 2 A) = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0, map_zero]
      have hc1 : coeff 1 (red 2 A) = 1 := by rw [coeff_map, h1, map_one]
      have hf := EntryA120566.residue (red 2 A) hc0 hc1 hr
      rw [hf]
      have he := EntryA120566.E_mul
      have hu : IsUnit (1 + X : PowerSeries (ZMod 2)) := isUnit_iff_constantCoeff.mpr (by simp)
      apply hu.mul_left_injective
      change EntryA120566.E * (1 + X) = (X * invOfUnit (1 + X) 1) * (1 + X)
      have hpm : (1 + X : PowerSeries (ZMod 2)) = 1 - X := by
        linear_combination X * EntryA120566.two_eq_zero
      rw [hpm, he, mul_assoc, invOfUnit_mul]
      · simp
      · simp

end BackfillPaper2.EntryRemark9
#print axioms BackfillPaper2.EntryRemark9.check_Rem9
