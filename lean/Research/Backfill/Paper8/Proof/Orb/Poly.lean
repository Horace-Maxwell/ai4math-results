import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, orbits: even and odd parts of rational polynomials

General facts over `ℚ[X]` used for Lemma 3.3: the decomposition `p = ev p (x²) + x · od p (x²)`,
evenness (`p(-x) = p(x)` iff `od p = 0`), the monic polynomial `±f(-x)` (`Challenge.mirror`),
descent of divisibility along `expand 2`, and the polynomial `normH f` with
`normH f (x²) = f(x) · (±f(-x))`, which is a monic irreducible factor of `P` whenever `f` is a
monic irreducible, non-even factor of `P(x²)` and `P(0) ≠ 0`.
-/

set_option autoImplicit false

open Polynomial BackfillPaper8

namespace P8Orb

noncomputable section

/-- Even part: `ev p = ∑ p_{2n} Xⁿ`. -/
def ev (p : ℚ[X]) : ℚ[X] := contract 2 p

/-- Odd part: `od p = ∑ p_{2n+1} Xⁿ`. -/
def od (p : ℚ[X]) : ℚ[X] := contract 2 p.divX

/-- `p(x) = ev p (x²) + x · od p (x²)`. -/
theorem ev_add_od (p : ℚ[X]) : expand ℚ 2 (ev p) + X * expand ℚ 2 (od p) = p := by
  ext n
  rcases n with _ | n
  · simp [ev, coeff_expand two_pos, coeff_contract two_ne_zero]
  · rw [coeff_add, coeff_X_mul, coeff_expand two_pos, coeff_expand two_pos]
    simp only [ev, od, coeff_contract two_ne_zero, coeff_divX]
    split_ifs with h1 h2 h2
    · omega
    · rw [add_zero]; congr 1; omega
    · rw [zero_add]; congr 1; omega
    · omega

/-- `expand 2 q` is even. -/
theorem expand_comp_neg_X (q : ℚ[X]) : (expand ℚ 2 q).comp (-X) = expand ℚ 2 q := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp

theorem comp_neg_X_eq (p : ℚ[X]) :
    p.comp (-X) = expand ℚ 2 (ev p) - X * expand ℚ 2 (od p) := by
  conv_lhs => rw [← ev_add_od p]
  rw [add_comp, mul_comp, X_comp, expand_comp_neg_X, expand_comp_neg_X]
  ring

theorem aeval_eq_ev_od {A : Type*} [CommRing A] [Algebra ℚ A] (p : ℚ[X]) (x : A) :
    aeval x p = aeval (x ^ 2) (ev p) + x * aeval (x ^ 2) (od p) := by
  conv_lhs => rw [← ev_add_od p]
  rw [map_add, map_mul, aeval_X, expand_aeval, expand_aeval]

theorem aeval_neg_eq_ev_od {A : Type*} [CommRing A] [Algebra ℚ A] (p : ℚ[X]) (x : A) :
    aeval (-x) p = aeval (x ^ 2) (ev p) - x * aeval (x ^ 2) (od p) := by
  rw [aeval_eq_ev_od, neg_sq]
  ring

/-- `p` is even iff its odd part vanishes. -/
theorem even_iff_od_eq_zero (p : ℚ[X]) : Challenge.IsEvenPoly p ↔ od p = 0 := by
  unfold Challenge.IsEvenPoly
  constructor
  · intro h
    have h2 := comp_neg_X_eq p
    rw [h] at h2
    conv_lhs at h2 => rw [← ev_add_od p]
    have h3 : (2 : ℚ[X]) * X * expand ℚ 2 (od p) = 0 := by linear_combination h2
    have h4 : expand ℚ 2 (od p) = 0 := by
      rcases mul_eq_zero.1 h3 with h5 | h5
      · rcases mul_eq_zero.1 h5 with h6 | h6
        · exact absurd h6 two_ne_zero
        · exact absurd h6 X_ne_zero
      · exact h5
    exact (expand_eq_zero two_pos).1 h4
  · intro h
    rw [comp_neg_X_eq, h]
    conv_rhs => rw [← ev_add_od p, h]
    simp

theorem eq_expand_ev_of_even {p : ℚ[X]} (h : Challenge.IsEvenPoly p) : p = expand ℚ 2 (ev p) := by
  conv_lhs => rw [← ev_add_od p, (even_iff_od_eq_zero p).1 h]
  simp

/-! ### The monic polynomial `±f(-x)` -/

theorem mirror_def' (f : ℚ[X]) : Challenge.mirror f = C ((-1) ^ f.natDegree) * f.comp (-X) := rfl

theorem natDegree_comp_neg_X (f : ℚ[X]) : (f.comp (-X)).natDegree = f.natDegree := by
  rw [natDegree_comp]
  simp

theorem natDegree_mirror (f : ℚ[X]) : (Challenge.mirror f).natDegree = f.natDegree := by
  rw [mirror_def', natDegree_C_mul (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)),
    natDegree_comp_neg_X]

theorem mirror_ne_zero {f : ℚ[X]} (hf : f ≠ 0) : Challenge.mirror f ≠ 0 := by
  rw [mirror_def']
  refine mul_ne_zero ?_ ?_
  · rw [Ne, C_eq_zero]
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  · rwa [Ne, comp_neg_X_eq_zero_iff]

theorem mirror_mirror (f : ℚ[X]) : Challenge.mirror (Challenge.mirror f) = f := by
  rw [mirror_def' (Challenge.mirror f), natDegree_mirror, mirror_def', mul_comp, C_comp,
    comp_neg_X_comp_neg_X, ← mul_assoc, ← C_mul, ← mul_pow]
  simp

theorem monic_mirror {f : ℚ[X]} (hf : f.Monic) : (Challenge.mirror f).Monic := by
  have h := hf.neg_one_pow_natDegree_mul_comp_neg_X
  rw [mirror_def']
  convert h using 2
  simp

theorem aeval_mirror {A : Type*} [CommRing A] [Algebra ℚ A] (f : ℚ[X]) (x : A) :
    aeval x (Challenge.mirror f) = (-1) ^ f.natDegree * aeval (-x) f := by
  rw [mirror_def', map_mul, aeval_C, aeval_comp]
  simp

theorem irreducible_mirror {f : ℚ[X]} (hf : Irreducible f) :
    Irreducible (Challenge.mirror f) := by
  have hu : IsUnit (C ((-1 : ℚ) ^ f.natDegree)) :=
    isUnit_C.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)))
  rw [mirror_def', irreducible_isUnit_mul hu]
  have h : f.comp (-X) = algEquivAevalNegX f := by
    simp [comp_eq_aeval]
  rw [h, MulEquiv.irreducible_iff]
  exact hf

/-- If `f ∣ E` and `E` is even, then `±f(-x) ∣ E`. -/
theorem mirror_dvd_of_dvd {f E : ℚ[X]} (hE : E.comp (-X) = E) (h : f ∣ E) :
    Challenge.mirror f ∣ E := by
  have hu : IsUnit (C ((-1 : ℚ) ^ f.natDegree)) :=
    isUnit_C.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)))
  rw [mirror_def', hu.mul_left_dvd]
  obtain ⟨g, rfl⟩ := h
  rw [← hE, mul_comp]
  exact dvd_mul_right _ _

theorem comp_neg_ne_neg {f : ℚ[X]} (h0 : f.eval 0 ≠ 0) : f.comp (-X) ≠ -f := by
  intro h
  have h1 : f.eval 0 = -f.eval 0 := by simpa [eval_comp] using congrArg (eval 0) h
  exact h0 (by linarith)

theorem mirror_ne_self {f : ℚ[X]} (h0 : f.eval 0 ≠ 0) (hne : ¬ Challenge.IsEvenPoly f) :
    Challenge.mirror f ≠ f := by
  intro h
  rw [mirror_def'] at h
  rcases neg_one_pow_eq_or ℚ f.natDegree with h1 | h1
  · rw [h1, C_1, one_mul] at h
    exact hne h
  · rw [h1, C_neg, C_1, neg_one_mul] at h
    exact comp_neg_ne_neg h0 (by linear_combination -h)

theorem rootSet_mirror {f : ℚ[X]} (hf : f ≠ 0) :
    (Challenge.mirror f).rootSet ℝ = (fun x => -x) '' f.rootSet ℝ := by
  ext x
  simp only [Set.mem_image, mem_rootSet_of_ne (mirror_ne_zero hf), mem_rootSet_of_ne hf,
    aeval_mirror]
  constructor
  · intro h
    refine ⟨-x, ?_, neg_neg x⟩
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    · exact h1
  · rintro ⟨y, hy, rfl⟩
    simp [hy]

/-! ### Divisibility along `expand 2` and the polynomial `normH f` -/

theorem dvd_of_expand_dvd {A B : ℚ[X]} (hA : A ≠ 0) (h : expand ℚ 2 A ∣ expand ℚ 2 B) :
    A ∣ B := by
  obtain ⟨Q, hQ⟩ := h
  have hQe : Challenge.IsEvenPoly Q := by
    have h1 := congrArg (fun p => p.comp (-X)) hQ
    simp only [mul_comp, expand_comp_neg_X] at h1
    have hA2 : expand ℚ 2 A ≠ 0 := (expand_ne_zero two_pos).2 hA
    exact mul_left_cancel₀ hA2 (h1.symm.trans hQ)
  refine ⟨ev Q, ?_⟩
  apply expand_injective two_pos
  rw [hQ, map_mul, ← eq_expand_ev_of_even hQe]

theorem coprime_of_ne {f g : ℚ[X]} (hf : f.Monic) (hg : g.Monic) (hfi : Irreducible f)
    (hgi : Irreducible g) (hne : f ≠ g) : IsCoprime f g := by
  rw [hfi.coprime_iff_not_dvd]
  intro hdvd
  exact hne (eq_of_monic_of_associated hf hg (hfi.associated_of_dvd hgi hdvd))

theorem eval_zero_ne_of_dvd {P f : ℚ[X]} (hP0 : P.eval 0 ≠ 0) (h : f ∣ expand ℚ 2 P) :
    f.eval 0 ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := h
  have h1 := congrArg (eval 0) hg
  rw [expand_eval, eval_mul, h0, zero_mul] at h1
  exact hP0 (by simpa using h1)

/-- `normH f = ev (f · (±f(-x)))`, so that `normH f (x²) = f(x) · (±f(-x))`. -/
def normH (f : ℚ[X]) : ℚ[X] := ev (f * Challenge.mirror f)

theorem mul_mirror_even (f : ℚ[X]) : Challenge.IsEvenPoly (f * Challenge.mirror f) := by
  unfold Challenge.IsEvenPoly
  rw [mul_comp, mirror_def', mul_comp, C_comp, comp_neg_X_comp_neg_X]
  ring

theorem expand_normH (f : ℚ[X]) : expand ℚ 2 (normH f) = f * Challenge.mirror f :=
  (eq_expand_ev_of_even (mul_mirror_even f)).symm

theorem natDegree_normH (f : ℚ[X]) : (normH f).natDegree = f.natDegree := by
  by_cases hf : f = 0
  · have h0 : normH f = 0 := by
      ext n
      simp [hf, normH, ev, coeff_contract two_ne_zero]
    rw [h0, hf, natDegree_zero]
  · have h := congrArg natDegree (expand_normH f)
    rw [natDegree_expand, natDegree_mul hf (mirror_ne_zero hf), natDegree_mirror] at h
    omega

theorem monic_normH {f : ℚ[X]} (hf : f.Monic) : (normH f).Monic := by
  rw [← monic_expand_iff two_pos, expand_normH]
  exact hf.mul (monic_mirror hf)

/-- Setting of an orbit factor: `f` monic, irreducible, not even, `f(0) ≠ 0`. Then
`f · (±f(-x))` divides every even polynomial divisible by `f`. -/
theorem mul_mirror_dvd {f E : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h0 : f.eval 0 ≠ 0)
    (hne : ¬ Challenge.IsEvenPoly f) (hE : E.comp (-X) = E) (h : f ∣ E) :
    f * Challenge.mirror f ∣ E :=
  (coprime_of_ne hf (monic_mirror hf) hfi (irreducible_mirror hfi)
    (mirror_ne_self h0 hne).symm).mul_dvd h (mirror_dvd_of_dvd hE h)

theorem normH_dvd_of_dvd {f W : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h0 : f.eval 0 ≠ 0)
    (hne : ¬ Challenge.IsEvenPoly f) (h : f ∣ expand ℚ 2 W) : normH f ∣ W := by
  apply dvd_of_expand_dvd (monic_normH hf).ne_zero
  rw [expand_normH]
  exact mul_mirror_dvd hf hfi h0 hne (expand_comp_neg_X W) h

theorem irreducible_normH {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h0 : f.eval 0 ≠ 0)
    (hne : ¬ Challenge.IsEvenPoly f) : Irreducible (normH f) := by
  have hH := monic_normH hf
  have hpos : 0 < f.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hfi)
  refine irreducible_iff.2 ⟨?_, ?_⟩
  · intro hu
    have h1 := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_normH] at h1
    omega
  · intro U V hUV
    have hf_dvd : f ∣ expand ℚ 2 U * expand ℚ 2 V := by
      rw [← map_mul, ← hUV, expand_normH]
      exact dvd_mul_right _ _
    rcases hfi.prime.dvd_or_dvd hf_dvd with h | h
    · obtain ⟨W, hW⟩ := normH_dvd_of_dvd hf hfi h0 hne h
      right
      have h1 : normH f * (W * V) = normH f * 1 := by
        rw [mul_one, ← mul_assoc, ← hW, hUV]
      exact IsUnit.of_mul_eq_one_right _ (mul_left_cancel₀ hH.ne_zero h1)
    · obtain ⟨W, hW⟩ := normH_dvd_of_dvd hf hfi h0 hne h
      left
      have h1 : normH f * (W * U) = normH f * 1 := by
        rw [mul_one, ← mul_assoc, ← hW, hUV, mul_comm]
      exact IsUnit.of_mul_eq_one_right _ (mul_left_cancel₀ hH.ne_zero h1)

theorem normH_dvd {P f : ℚ[X]} (hP0 : P.eval 0 ≠ 0) (hf : f.Monic) (hfi : Irreducible f)
    (hdvd : f ∣ expand ℚ 2 P) (hne : ¬ Challenge.IsEvenPoly f) : normH f ∣ P :=
  normH_dvd_of_dvd hf hfi (eval_zero_ne_of_dvd hP0 hdvd) hne hdvd

/-- The monic irreducible factors of `normH f (x²)` are `f` and `±f(-x)`. -/
theorem eq_or_eq_mirror_of_dvd_normH {f g : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f)
    (hg : g.Monic) (hgi : Irreducible g) (hdvd : g ∣ expand ℚ 2 (normH f)) :
    g = f ∨ g = Challenge.mirror f := by
  rw [expand_normH] at hdvd
  rcases hgi.prime.dvd_or_dvd hdvd with h | h
  · exact Or.inl (eq_of_monic_of_associated hg hf (hgi.associated_of_dvd hfi h))
  · exact Or.inr (eq_of_monic_of_associated hg (monic_mirror hf)
      (hgi.associated_of_dvd (irreducible_mirror hfi) h))

/-- `normH f (0) = ±f(0)²`. -/
theorem eval_zero_normH (f : ℚ[X]) :
    (normH f).eval 0 = (-1) ^ f.natDegree * (f.eval 0) ^ 2 := by
  have h := congrArg (eval 0) (expand_normH f)
  rw [expand_eval, eval_mul, mirror_def', eval_mul, eval_C, eval_comp] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, eval_neg, eval_X,
    neg_zero] at h
  rw [h]
  ring

/-! ### Finitely many monic irreducible factors, and their degrees -/

theorem finite_monic_irreducible_dvd {Q : ℚ[X]} (hQ : Q ≠ 0) :
    {f : ℚ[X] | f.Monic ∧ Irreducible f ∧ f ∣ Q}.Finite := by
  classical
  apply (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.finite_toSet.subset
  rintro f ⟨hf, hfi, hdvd⟩
  obtain ⟨q, hq, hfq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hQ hfi hdvd
  have hq0 : q ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq
  have hqn : normalize q = q := UniqueFactorizationMonoid.normalize_normalized_factor q hq
  have hqm : q.Monic := hqn ▸ monic_normalize hq0
  rw [eq_of_monic_of_associated hf hqm hfq]
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 hq)

/-- Distinct monic irreducible factors of `P ≠ 0` have total degree at most `deg P`. -/
theorem sum_natDegree_le {P : ℚ[X]} (hP : P ≠ 0) (T : Finset ℚ[X])
    (hT : ∀ h ∈ T, h.Monic ∧ Irreducible h ∧ h ∣ P) :
    ∑ h ∈ T, h.natDegree ≤ P.natDegree := by
  have hdvd : (∏ h ∈ T, h) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro h1 hh1 h2 hh2 hne
      exact coprime_of_ne (hT h1 hh1).1 (hT h2 hh2).1 (hT h1 hh1).2.1 (hT h2 hh2).2.1 hne
    · intro h hh
      exact (hT h hh).2.2
  rw [← natDegree_prod_of_monic T (fun h => h) (fun h hh => (hT h hh).1)]
  exact natDegree_le_of_dvd hdvd hP

end

end P8Orb
