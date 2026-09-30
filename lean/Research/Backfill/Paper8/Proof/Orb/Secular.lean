import Research.Backfill.Paper8.Proof.Orb.Poly

/-!
# Paper 8, orbits: facts about the secular polynomial `R`

Proved directly from the definition of `secular`: `R(b) ≠ 0` for `b ∈ B`; the identity
`R(t) = ∏_{b∈B}(t - b) · (1 - F(t))` for `t ∉ B` (so `F(t) = 1` at every root of `R`); `R(0) ≠ 0`;
`R(x²)` evaluated through `R`; roots of orbit factors are secular; and a rational root of `R(x²)`
is an integer when `R` is monic (Gauss).
-/

set_option autoImplicit false

open Polynomial BackfillPaper8 BackfillPaper8.Challenge

namespace P8Orb

noncomputable section

/-- `R` over `ℚ`. -/
abbrev Rq (m : Multiset ℕ) : ℚ[X] := (secular m).map (Int.castRingHom ℚ)

theorem R2_eq (m : Multiset ℕ) : R2 m = expand ℚ 2 (Rq m) := rfl

/-- `R(b) = -k_b ∏_{b' ≠ b} (b - b') ≠ 0` for `b ∈ B`. -/
theorem secular_eval_mem_ne_zero (m : Multiset ℕ) {b : ℕ} (hb : b ∈ Bset m) :
    (secular m).eval (b : ℤ) ≠ 0 := by
  unfold secular
  rw [eval_sub, eval_prod, eval_finsetSum, Finset.prod_eq_zero hb (by simp), zero_sub,
    neg_ne_zero, Finset.sum_eq_single b]
  · rw [eval_mul, eval_C, eval_prod]
    refine mul_ne_zero ?_ ?_
    · have h := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hb)
      unfold kb
      exact_mod_cast h.ne'
    · rw [Finset.prod_ne_zero_iff]
      intro b' hb'
      rw [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact_mod_cast (Finset.ne_of_mem_erase hb').symm
  · intro b' hb' hne
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hne, hb⟩) (by simp),
      mul_zero]
  · intro h
    exact absurd hb h

theorem aeval_intCast_secular {K : Type*} [Field K] (m : Multiset ℕ) (z : ℤ) :
    aeval (z : K) (secular m) = (((secular m).eval z : ℤ) : K) := by
  simpa using aeval_algebraMap_apply_eq_algebraMap_eval (A := K) z (secular m)

/-- `R(t) = ∏_{b∈B}(t - b) · (1 - ∑_{b∈B} k_b/(t - b))` for `t ∉ B`. -/
theorem aeval_secular {K : Type*} [Field K] (m : Multiset ℕ) (t : K)
    (ht : ∀ b ∈ Bset m, t ≠ (b : K)) :
    aeval t (secular m) =
      (∏ b ∈ Bset m, (t - b)) * (1 - ∑ b ∈ Bset m, (kb m b : K) / (t - b)) := by
  unfold secular
  simp only [map_sub, map_prod, map_sum, map_mul, aeval_X, map_natCast]
  rw [mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [← Finset.mul_prod_erase _ _ hb]
  have h : t - (b : K) ≠ 0 := sub_ne_zero.2 (ht b hb)
  field_simp

/-- No root of `R` lies in `B`. -/
theorem ne_of_aeval_secular_eq_zero {K : Type*} [Field K] [CharZero K] (m : Multiset ℕ) {t : K}
    (ht : aeval t (secular m) = 0) : ∀ b ∈ Bset m, t ≠ (b : K) := by
  intro b hb h
  rw [h, show (b : K) = ((b : ℤ) : K) by simp, aeval_intCast_secular] at ht
  exact secular_eval_mem_ne_zero m hb (by exact_mod_cast ht)

/-- `F(t) = ∑_{b∈B} k_b/(t - b) = 1` at every root `t` of `R`. -/
theorem sum_kb_div_eq_one {K : Type*} [Field K] [CharZero K] (m : Multiset ℕ) {t : K}
    (ht : aeval t (secular m) = 0) : ∑ b ∈ Bset m, (kb m b : K) / (t - b) = 1 := by
  have hne := ne_of_aeval_secular_eq_zero m ht
  rw [aeval_secular m t hne] at ht
  rcases mul_eq_zero.1 ht with h | h
  · obtain ⟨b, hb, h0⟩ := Finset.prod_eq_zero_iff.1 h
    exact absurd (sub_eq_zero.1 h0) (hne b hb)
  · exact (sub_eq_zero.1 h).symm

/-- `R(0) ≠ 0`. -/
theorem secular_eval_zero_ne (m : Multiset ℕ) : (secular m).eval 0 ≠ 0 := by
  by_cases h0 : 0 ∈ Bset m
  · simpa using secular_eval_mem_ne_zero m h0
  · have ht : ∀ b ∈ Bset m, (0 : ℚ) ≠ (b : ℚ) := by
      intro b hb h
      have hb0 : b = 0 := by exact_mod_cast h.symm
      exact h0 (hb0 ▸ hb)
    intro hR
    have h1 : aeval (0 : ℚ) (secular m) = 0 := by
      simpa [hR] using aeval_intCast_secular (K := ℚ) m 0
    rw [aeval_secular m 0 ht] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.1 h2
      exact ht b hb (by linarith)
    · have h3 : ∑ b ∈ Bset m, (kb m b : ℚ) / (0 - b) ≤ 0 :=
        Finset.sum_nonpos (fun b _ => by rw [zero_sub, div_neg, neg_nonpos]; positivity)
      linarith

theorem Rq_eval_intCast (m : Multiset ℕ) (z : ℤ) :
    (Rq m).eval (z : ℚ) = (((secular m).eval z : ℤ) : ℚ) := by
  simp

theorem Rq_eval_zero_ne (m : Multiset ℕ) : (Rq m).eval 0 ≠ 0 := by
  have h := Rq_eval_intCast m 0
  rw [Int.cast_zero] at h
  rw [h]
  exact_mod_cast secular_eval_zero_ne m

theorem aeval_Rq {A : Type*} [CommRing A] [Algebra ℚ A] (m : Multiset ℕ) (x : A) :
    aeval x (Rq m) = aeval x (secular m) := by
  rw [Rq, ← algebraMap_int_eq, aeval_map_algebraMap]

/-- `R(x²)` at `x` is `R` at `x²`. -/
theorem aeval_R2 {A : Type*} [CommRing A] [Algebra ℚ A] (m : Multiset ℕ) (x : A) :
    aeval x (R2 m) = aeval (x ^ 2) (secular m) := by
  rw [R2_eq, expand_aeval, aeval_Rq]

theorem R2_even (m : Multiset ℕ) : (R2 m).comp (-X) = R2 m :=
  expand_comp_neg_X (Rq m)

theorem orbitFactor_eval_zero_ne {m : Multiset ℕ} {f : ℚ[X]} (hf : IsOrbitFactor m f) :
    f.eval 0 ≠ 0 :=
  eval_zero_ne_of_dvd (Rq_eval_zero_ne m) hf.2.2

/-- A root of an orbit factor is a secular value. -/
theorem isSecular_of_root {m : Multiset ℕ} {f : ℚ[X]} (hf : IsOrbitFactor m f) {θ : ℝ}
    (hθ : aeval θ f = 0) : IsSecular m θ := by
  obtain ⟨g, hg⟩ := hf.2.2
  have h : aeval θ (R2 m) = 0 := by rw [hg, map_mul, hθ, zero_mul]
  rwa [aeval_R2] at h

/-- Gauss: a rational root `c` of `R(x²)` is an integer `z`, and `R(z²) = 0`. -/
theorem int_of_rat_root {m : Multiset ℕ} (hmon : (secular m).Monic) {c : ℚ}
    (hc : (R2 m).eval c = 0) : ∃ z : ℤ, c = z ∧ (secular m).eval (z ^ 2) = 0 := by
  have h1 : aeval c (expand ℤ 2 (secular m)) = 0 := by
    rw [expand_aeval, ← aeval_R2, coe_aeval_eq_eval]
    exact hc
  obtain ⟨z, hz, -⟩ :=
    exists_integer_of_is_root_of_monic ((monic_expand_iff two_pos).2 hmon) h1
  refine ⟨z, by simpa using hz, ?_⟩
  rw [hz, aeval_algebraMap_apply_eq_algebraMap_eval, expand_eval, algebraMap_int_eq,
    eq_intCast] at h1
  exact_mod_cast h1

end

end P8Orb
