import Research.Backfill.Paper8.Proof.Orb.Secular

/-!
# Paper 8, orbits: Lemma 3.3 (a)–(c) for a multiset

For a monic irreducible factor `f` of `R(x²)` over `ℚ` and a real root `θ` of `f`:
(a) `f(-x) ≠ -f(x)` (as `R(0) ≠ 0`), and if `f` is even then `θ ∉ ℚ(θ²)` (else `f ∣ x`);
(b) if `f` is not even, then `f(θ) = E(θ²) + θ O(θ²)` with `O(θ²) ≠ 0`, so `θ ∈ ℚ(θ²)`; degree 1
gives an integer `θ` with `R(θ²) = 0` (Gauss), and otherwise `θ² ∉ ℚ`;
(c) `x² - z` is an even orbit factor when `z` is an integer root of `R` that is not a square.
-/

set_option autoImplicit false

open Polynomial BackfillPaper8 BackfillPaper8.Challenge

namespace P8Orb

noncomputable section

theorem X_not_even : ¬ IsEvenPoly (X : ℚ[X]) := by
  unfold IsEvenPoly
  intro h
  have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) h
  norm_num at h1

theorem natDegree_pos_of_irreducible {f : ℚ[X]} (hfi : Irreducible f) : 0 < f.natDegree :=
  natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hfi)

theorem eq_X_of_dvd_X {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h : f ∣ X) : f = X :=
  (eq_of_monic_of_dvd_of_natDegree_le hf monic_X h
    (by rw [natDegree_X]; exact natDegree_pos_of_irreducible hfi)).symm

/-- (a): an even monic irreducible `f` with root `θ` has `θ ∉ ℚ(θ²)`. -/
theorem not_mem_QAdj_of_even {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f)
    (he : IsEvenPoly f) {θ : ℝ} (hθ : aeval θ f = 0) : θ ∉ QAdj (θ ^ 2) := by
  intro hmem
  have hint : IsIntegral ℚ θ := ⟨f, hf, by rwa [aeval_def] at hθ⟩
  have halg : IsAlgebraic ℚ (θ ^ 2) := (hint.pow 2).isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg,
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 hmem
  have hfmin : f = minpoly ℚ θ := minpoly.eq_of_irreducible_of_monic hfi hθ hf
  have hq : aeval θ (X - expand ℚ 2 p) = 0 := by
    rw [map_sub, aeval_X, expand_aeval, hp, sub_self]
  have h1 : f ∣ X - expand ℚ 2 p := hfmin ▸ minpoly.dvd ℚ θ hq
  have h2 : f ∣ (X - expand ℚ 2 p).comp (-X) := by
    obtain ⟨g, hg⟩ := h1
    refine ⟨g.comp (-X), ?_⟩
    unfold IsEvenPoly at he
    rw [hg, mul_comp, he]
  have hC : (C (2 : ℚ) : ℚ[X]) = 2 := C_ofNat 2
  have h3 : (X - expand ℚ 2 p) - (X - expand ℚ 2 p).comp (-X) = C 2 * X := by
    rw [sub_comp, X_comp, expand_comp_neg_X, hC]
    ring
  have h4 : f ∣ C 2 * X := h3 ▸ dvd_sub h1 h2
  have h5 : f ∣ X := (IsUnit.dvd_mul_left (isUnit_C.2 (by norm_num))).1 h4
  exact X_not_even (eq_X_of_dvd_X hf hfi h5 ▸ he)

/-- (b), key step: for a non-even factor, `f(θ) = E(θ²) + θ O(θ²)` with `O(θ²) ≠ 0`. -/
theorem od_ne_and_eq {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h0 : f.eval 0 ≠ 0)
    (hne : ¬ IsEvenPoly f) {θ : ℝ} (hθ : aeval θ f = 0) :
    aeval (θ ^ 2) (od f) ≠ 0 ∧ θ = -aeval (θ ^ 2) (ev f) / aeval (θ ^ 2) (od f) := by
  have hdec := aeval_eq_ev_od f θ
  rw [hθ] at hdec
  have hO : aeval (θ ^ 2) (od f) ≠ 0 := by
    intro hO
    rw [hO, mul_zero, add_zero] at hdec
    have hneg : aeval (-θ) f = 0 := by
      rw [aeval_neg_eq_ev_od, ← hdec, hO, mul_zero, sub_zero]
    have hmθ : aeval θ (Challenge.mirror f) = 0 := by rw [aeval_mirror, hneg, mul_zero]
    have e1 : f = minpoly ℚ θ := minpoly.eq_of_irreducible_of_monic hfi hθ hf
    have e2 : Challenge.mirror f = minpoly ℚ θ :=
      minpoly.eq_of_irreducible_of_monic (irreducible_mirror hfi) hmθ (monic_mirror hf)
    exact mirror_ne_self h0 hne (e2.trans e1.symm)
  refine ⟨hO, ?_⟩
  field_simp
  linarith

/-- (b): a root of a non-even factor lies in `ℚ(θ²)`. -/
theorem mem_QAdj_of_not_even {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) (h0 : f.eval 0 ≠ 0)
    (hne : ¬ IsEvenPoly f) {θ : ℝ} (hθ : aeval θ f = 0) : θ ∈ QAdj (θ ^ 2) := by
  obtain ⟨-, h⟩ := od_ne_and_eq hf hfi h0 hne hθ
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨-ev f, od f, by rw [map_neg]; exact h⟩

/-- (b), degree 1: the root is an integer `q` with `R(q²) = 0`. -/
theorem int_of_natDegree_eq_one {m : Multiset ℕ} {f : ℚ[X]} (hmon : (secular m).Monic)
    (hf : IsOrbitFactor m f) (hdeg : f.natDegree = 1) {θ : ℝ} (hθ : aeval θ f = 0) :
    ∃ q : ℤ, θ = q ∧ (secular m).eval (q ^ 2) = 0 := by
  have hX := hf.1.eq_X_add_C hdeg
  have hθc : θ = -((f.coeff 0 : ℚ) : ℝ) := by
    rw [hX] at hθ
    simp only [map_add, aeval_X, aeval_C, eq_ratCast] at hθ
    linarith
  have hroot : (R2 m).eval (-f.coeff 0) = 0 := by
    obtain ⟨g, hg⟩ := hf.2.2
    rw [hg, eval_mul]
    conv_lhs => rw [hX]
    simp
  obtain ⟨z, hz, hR⟩ := int_of_rat_root hmon hroot
  refine ⟨z, ?_, hR⟩
  rw [hθc]
  exact_mod_cast hz

/-- (b), degree `≠ 1`: `θ² ∉ ℚ`. -/
theorem not_rat_of_natDegree_ne_one {m : Multiset ℕ} {f : ℚ[X]} (hf : IsOrbitFactor m f)
    (hne : ¬ IsEvenPoly f) (hdeg : f.natDegree ≠ 1) {θ : ℝ} (hθ : aeval θ f = 0) :
    θ ^ 2 ∉ Set.range (algebraMap ℚ ℝ) := by
  rintro ⟨c, hc⟩
  obtain ⟨-, h⟩ := od_ne_and_eq hf.1 hf.2.1 (orbitFactor_eval_zero_ne hf) hne hθ
  rw [← hc, aeval_algebraMap_apply_eq_algebraMap_eval,
    aeval_algebraMap_apply_eq_algebraMap_eval] at h
  have hθd : θ = algebraMap ℚ ℝ (-(ev f).eval c / (od f).eval c) := by
    rw [h]
    simp
  have hfd : f.IsRoot (-(ev f).eval c / (od f).eval c) := by
    rw [hθd, aeval_algebraMap_apply_eq_algebraMap_eval] at hθ
    rw [IsRoot.def]
    exact (map_eq_zero_iff _ (algebraMap ℚ ℝ).injective).1 hθ
  exact hdeg (natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hf.2.1 hfd))

/-- (b): `±f(-x)` is again an orbit factor. -/
theorem isOrbitFactor_mirror {m : Multiset ℕ} {f : ℚ[X]} (hf : IsOrbitFactor m f) :
    IsOrbitFactor m (Challenge.mirror f) :=
  ⟨monic_mirror hf.1, irreducible_mirror hf.2.1, mirror_dvd_of_dvd (R2_even m) hf.2.2⟩

/-- (c): `x² - z` is an even orbit factor for an integer root `z` of `R` that is not a square. -/
theorem even_orbit_of_not_isSquare {m : Multiset ℕ} {z : ℤ} (hz : (secular m).eval z = 0)
    (hsq : ¬ IsSquare z) :
    IsOrbitFactor m (X ^ 2 - C (z : ℚ)) ∧ IsEvenPoly (X ^ 2 - C (z : ℚ)) := by
  refine ⟨⟨monic_X_pow_sub_C _ two_ne_zero, ?_, ?_⟩, ?_⟩
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    apply hsq
    rw [← Rat.isSquare_intCast_iff]
    exact ⟨b, by rw [← hb, sq]⟩
  · have h1 : X - C (z : ℚ) ∣ Rq m := by
      rw [dvd_iff_isRoot, IsRoot.def, Rq_eval_intCast, hz, Int.cast_zero]
    have h2 := map_dvd (expand ℚ 2) h1
    rw [map_sub, expand_X, expand_C] at h2
    exact h2
  · unfold IsEvenPoly
    simp [sub_comp]

end

end P8Orb
