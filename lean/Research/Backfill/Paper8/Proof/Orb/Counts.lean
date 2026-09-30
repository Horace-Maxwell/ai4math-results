import Research.Backfill.Paper8.Proof.Orb.Orbits

/-!
# Paper 8, orbits: counting pairs (Lemma 3.3(d) and facts used by Proposition 5.5)

For a multiset `m ≠ 0` with `R = secular m` monic of degree `r` (from `Secular_monic`): every
non-even orbit factor `f` gives the monic irreducible factor `normH f` of `R` of degree `deg f`,
and the pair `{f, ±f(-x)}` is the set of monic irreducible factors of `normH f (x²)`; distinct
monic irreducible factors of `R` have total degree `≤ r`. Consequences, all for a multiset `m`:
`orbit_count` (Lemma 3.3(d) with finiteness), `NI_eq` (`N_I = #{q ≥ 1 : R(q²) = 0}`),
`two_NII_add_Nrat_le` (`2 N_II + #{integer roots of R} ≤ r`) and `two_NII_lt_of_not_isSquare`
(`2 N_II < r` when `|R(0)|` is not a square; the pair factors would then multiply to `R`, and
`normH f (0) = ±f(0)²`).
-/

set_option autoImplicit false

open Polynomial BackfillPaper8 BackfillPaper8.Challenge

namespace P8Orb

noncomputable section

/-! ### General counting over `ℚ[X]` -/

theorem card_add_two_mul_card_le {P : ℚ[X]} (hP : P ≠ 0) (A B : Finset ℚ[X]) (hAB : Disjoint A B)
    (hA : ∀ h ∈ A, h.Monic ∧ Irreducible h ∧ h ∣ P ∧ 1 ≤ h.natDegree)
    (hB : ∀ h ∈ B, h.Monic ∧ Irreducible h ∧ h ∣ P ∧ 2 ≤ h.natDegree) :
    A.card + 2 * B.card ≤ P.natDegree := by
  have h1 := sum_natDegree_le hP (A ∪ B) (by
    intro h hh
    rcases Finset.mem_union.1 hh with h' | h'
    · exact ⟨(hA h h').1, (hA h h').2.1, (hA h h').2.2.1⟩
    · exact ⟨(hB h h').1, (hB h h').2.1, (hB h h').2.2.1⟩)
  rw [Finset.sum_union hAB] at h1
  have h2 : A.card ≤ ∑ h ∈ A, h.natDegree := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun h hh => (hA h hh).2.2.2)
  have h3 : B.card • 2 ≤ ∑ h ∈ B, h.natDegree :=
    Finset.card_nsmul_le_sum B _ 2 (fun h hh => (hB h hh).2.2.2)
  rw [smul_eq_mul] at h3
  omega

theorem ncard_add_two_mul_ncard_le {P : ℚ[X]} (hP : P ≠ 0) {A B : Set ℚ[X]} (hAf : A.Finite)
    (hBf : B.Finite) (hAB : Disjoint A B)
    (hA : ∀ h ∈ A, h.Monic ∧ Irreducible h ∧ h ∣ P ∧ 1 ≤ h.natDegree)
    (hB : ∀ h ∈ B, h.Monic ∧ Irreducible h ∧ h ∣ P ∧ 2 ≤ h.natDegree) :
    A.ncard + 2 * B.ncard ≤ P.natDegree := by
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  exact card_add_two_mul_card_le hP _ _ (Set.Finite.disjoint_toFinset.2 hAB)
    (fun h hh => hA h (hAf.mem_toFinset.1 hh)) (fun h hh => hB h (hBf.mem_toFinset.1 hh))

theorem mirror_X_add_C (c : ℚ) : Challenge.mirror (X + C c) = X - C c := by
  rw [mirror_def', natDegree_X_add_C, add_comp, X_comp, C_comp]
  simp only [pow_one, map_neg, map_one]
  ring

theorem mirror_X_sub_C (c : ℚ) : Challenge.mirror (X - C c) = X + C c := by
  rw [mirror_def', natDegree_X_sub_C, sub_comp, X_comp, C_comp]
  simp only [pow_one, map_neg, map_one]
  ring

theorem normH_X_add_C (c : ℚ) : normH (X + C c) = X - C (c ^ 2) := by
  apply expand_injective two_pos
  rw [expand_normH, mirror_X_add_C, map_sub, expand_X, expand_C, C_pow]
  ring

theorem not_even_X_sub_C (c : ℚ) : ¬ IsEvenPoly (X - C c) := by
  unfold IsEvenPoly
  intro h
  have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) h
  norm_num [sub_comp, coeff_X, coeff_C] at h1

theorem X_sub_C_injective : Function.Injective (fun c : ℚ => X - C c) := by
  intro c c' h
  have h1 := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simpa using h1

/-! ### Orbit factors, pairs and factors of `R` for a multiset -/

section Multiset

variable (m : Multiset ℕ)

theorem Rq_ne_zero : Rq m ≠ 0 := fun h => Rq_eval_zero_ne m (by rw [h, eval_zero])

theorem secular_ne_zero : secular m ≠ 0 := fun h => secular_eval_zero_ne m (by rw [h, eval_zero])

theorem Rq_natDegree (hmon : Secular_monic) (hm : m ≠ 0) : (Rq m).natDegree = (Bset m).card := by
  rw [Rq, (hmon m hm).1.natDegree_map, (hmon m hm).2]

theorem orbitFactors_finite : {f : ℚ[X] | IsOrbitFactor m f}.Finite :=
  finite_monic_irreducible_dvd ((expand_ne_zero two_pos).2 (Rq_ne_zero m))

/-- The integer roots of `R` form a finite set. -/
theorem intRoots_finite : {z : ℤ | (secular m).eval z = 0}.Finite := by
  classical
  apply ((secular m).roots.toFinset.finite_toSet).subset
  intro z hz
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((mem_roots (secular_ne_zero m)).2 hz))

/-- The set of monic irreducible factors of `h (x²)`. -/
def pairOf (h : ℚ[X]) : Set ℚ[X] := {g | g.Monic ∧ Irreducible g ∧ g ∣ expand ℚ 2 h}

theorem pairOf_normH {f : ℚ[X]} (hf : f.Monic) (hfi : Irreducible f) :
    pairOf (normH f) = {f, Challenge.mirror f} := by
  ext g
  simp only [pairOf, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hg, hgi, hdvd⟩
    exact eq_or_eq_mirror_of_dvd_normH hf hfi hg hgi hdvd
  · rintro (rfl | rfl)
    · exact ⟨hf, hfi, by rw [expand_normH]; exact dvd_mul_right _ _⟩
    · exact ⟨monic_mirror hf, irreducible_mirror hfi, by rw [expand_normH]; exact dvd_mul_left _ _⟩

/-- For a non-even orbit factor `f`, `normH f` is a monic irreducible factor of `R` of degree
`deg f`. -/
theorem normH_mem {f : ℚ[X]} (hf : IsOrbitFactor m f) (hne : ¬ IsEvenPoly f) :
    (normH f).Monic ∧ Irreducible (normH f) ∧ normH f ∣ Rq m ∧
      (normH f).natDegree = f.natDegree :=
  ⟨monic_normH hf.1, irreducible_normH hf.1 hf.2.1 (orbitFactor_eval_zero_ne hf) hne,
    normH_dvd (Rq_eval_zero_ne m) hf.1 hf.2.1 hf.2.2 hne, natDegree_normH f⟩

/-- Factors of `R` coming from integer pairs. -/
def TI : Set ℚ[X] :=
  normH '' {f | IsOrbitFactor m f ∧ ¬ IsEvenPoly f ∧ f.natDegree = 1}

/-- Factors of `R` coming from irrational pairs. -/
def TII : Set ℚ[X] :=
  normH '' {f | IsOrbitFactor m f ∧ ¬ IsEvenPoly f ∧ f.natDegree ≠ 1}

theorem TI_finite : (TI m).Finite :=
  ((orbitFactors_finite m).subset (fun _ hf => hf.1)).image _

theorem TII_finite : (TII m).Finite :=
  ((orbitFactors_finite m).subset (fun _ hf => hf.1)).image _

theorem NI_le : NI m ≤ (TI m).ncard := by
  have hsub : {P ∈ nonEvenPairs m | ∀ f ∈ P, f.natDegree = 1} ⊆ pairOf '' TI m := by
    rintro P ⟨⟨f, hf, hne, rfl⟩, hdeg⟩
    exact ⟨normH f, ⟨f, ⟨hf, hne, hdeg f (Set.mem_insert _ _)⟩, rfl⟩, pairOf_normH hf.1 hf.2.1⟩
  exact (Set.ncard_le_ncard hsub ((TI_finite m).image _)).trans (Set.ncard_image_le (TI_finite m))

theorem NII_le : NII m ≤ (TII m).ncard := by
  have hsub : {P ∈ nonEvenPairs m | ∀ f ∈ P, f.natDegree ≠ 1} ⊆ pairOf '' TII m := by
    rintro P ⟨⟨f, hf, hne, rfl⟩, hdeg⟩
    exact ⟨normH f, ⟨f, ⟨hf, hne, hdeg f (Set.mem_insert _ _)⟩, rfl⟩, pairOf_normH hf.1 hf.2.1⟩
  exact (Set.ncard_le_ncard hsub ((TII_finite m).image _)).trans
    (Set.ncard_image_le (TII_finite m))

theorem TI_prop : ∀ h ∈ TI m, h.Monic ∧ Irreducible h ∧ h ∣ Rq m ∧ h.natDegree = 1 := by
  rintro h ⟨f, ⟨hf, hne, hdeg⟩, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := normH_mem m hf hne
  exact ⟨h1, h2, h3, h4.trans hdeg⟩

theorem TII_prop : ∀ h ∈ TII m, h.Monic ∧ Irreducible h ∧ h ∣ Rq m ∧ 2 ≤ h.natDegree := by
  rintro h ⟨f, ⟨hf, hne, hdeg⟩, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := normH_mem m hf hne
  have hpos := natDegree_pos_of_irreducible hf.2.1
  exact ⟨h1, h2, h3, by omega⟩

/-- The factors `x - z` of `R` for a set `Z` of integer roots. -/
def linOf (Z : Set ℤ) : Set ℚ[X] := (fun z : ℤ => X - C (z : ℚ)) '' Z

theorem linOf_ncard (Z : Set ℤ) : (linOf Z).ncard = Z.ncard := by
  apply Set.ncard_image_of_injective
  intro z z' h
  exact_mod_cast X_sub_C_injective h

theorem linOf_prop {Z : Set ℤ} (hZ : ∀ z ∈ Z, (secular m).eval z = 0) :
    ∀ h ∈ linOf Z, h.Monic ∧ Irreducible h ∧ h ∣ Rq m ∧ h.natDegree = 1 := by
  rintro h ⟨z, hz, rfl⟩
  refine ⟨monic_X_sub_C _, irreducible_of_degree_eq_one (degree_X_sub_C _), ?_,
    natDegree_X_sub_C _⟩
  rw [dvd_iff_isRoot, IsRoot.def, Rq_eval_intCast, hZ z hz, Int.cast_zero]

theorem intRoots_ncard_add_two_NII_le (hmon : Secular_monic) (hm : m ≠ 0) :
    {z : ℤ | (secular m).eval z = 0}.ncard + 2 * NII m ≤ (Bset m).card := by
  have hdisj : Disjoint (linOf {z : ℤ | (secular m).eval z = 0}) (TII m) := by
    rw [Set.disjoint_left]
    intro h h1 h2
    have e1 := (linOf_prop m (fun z hz => hz) h h1).2.2.2
    have e2 := (TII_prop m h h2).2.2.2
    omega
  have key := ncard_add_two_mul_ncard_le (A := linOf {z : ℤ | (secular m).eval z = 0})
    (Rq_ne_zero m) ((intRoots_finite m).image _) (TII_finite m) hdisj
    (fun h hh => by
      obtain ⟨a, b, c, d⟩ := linOf_prop m (fun z hz => hz) h hh
      exact ⟨a, b, c, d.ge⟩)
    (TII_prop m)
  rw [linOf_ncard, Rq_natDegree m hmon hm] at key
  have := NII_le m
  omega

/-- `x - q` (for an integer `q` with `R(q²) = 0`) is an orbit factor. -/
theorem isOrbitFactor_X_sub_C {z : ℤ} (hz : (secular m).eval (z ^ 2) = 0) :
    IsOrbitFactor m (X - C (z : ℚ)) := by
  refine ⟨monic_X_sub_C _, irreducible_of_degree_eq_one (degree_X_sub_C _), ?_⟩
  rw [dvd_iff_isRoot, IsRoot.def, R2_eq, expand_eval]
  have h : ((z : ℚ)) ^ 2 = ((z ^ 2 : ℤ) : ℚ) := by push_cast; ring
  rw [h, Rq_eval_intCast, hz, Int.cast_zero]

/-- The integer pair `{x - q, x + q}`. -/
def intPair (q : ℕ) : Set ℚ[X] := {X - C (q : ℚ), X + C (q : ℚ)}

/-- (b′) `N_I = #{q ≥ 1 : R(q²) = 0}` (and this set is finite). -/
theorem NI_eq_aux (hmon : Secular_monic) (hm : m ≠ 0) :
    {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0}.Finite ∧
    NI m = {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0}.ncard := by
  set Q := {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0} with hQ
  have hQf : Q.Finite := by
    have hinj : Set.InjOn (fun q : ℕ => (q : ℤ) ^ 2)
        ((fun q : ℕ => (q : ℤ) ^ 2) ⁻¹' {z : ℤ | (secular m).eval z = 0}) := by
      intro q _ q' _ h
      simp only at h
      have h1 : q ^ 2 = q' ^ 2 := by exact_mod_cast h
      exact Nat.pow_left_injective (by norm_num) h1
    exact ((intRoots_finite m).preimage hinj).subset (fun q hq => hq.2)
  refine ⟨hQf, ?_⟩
  have hinjP : Set.InjOn intPair Q := by
    intro q hq q' _ h
    have hmem : X - C (q : ℚ) ∈ intPair q' := by
      rw [← h]
      exact Set.mem_insert _ _
    simp only [intPair, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1
    · exact_mod_cast X_sub_C_injective h1
    · have h2 := congrArg (fun p : ℚ[X] => p.coeff 0) h1
      simp only [coeff_sub, coeff_add, coeff_X_zero, coeff_C_zero, zero_sub, zero_add] at h2
      have h3 : ((q + q' : ℕ) : ℚ) = 0 := by push_cast; linarith
      have h4 : q + q' = 0 := by exact_mod_cast h3
      have h5 := hq.1
      omega
  have hset : {P ∈ nonEvenPairs m | ∀ f ∈ P, f.natDegree = 1} = intPair '' Q := by
    ext P
    constructor
    · rintro ⟨⟨f, hf, hne, rfl⟩, hdeg⟩
      have hdeg1 : f.natDegree = 1 := hdeg f (Set.mem_insert _ _)
      have hX := hf.1.eq_X_add_C hdeg1
      have hroot : (R2 m).eval (-f.coeff 0) = 0 := by
        obtain ⟨g, hg⟩ := hf.2.2
        rw [hg, eval_mul]
        conv_lhs => rw [hX]
        simp
      obtain ⟨z, hz, hR⟩ := int_of_rat_root (hmon m hm).1 hroot
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact secular_eval_zero_ne m (by simpa using hR)
      refine ⟨z.natAbs, ⟨Int.natAbs_pos.2 hz0, by rw [Int.natAbs_sq]; exact hR⟩, ?_⟩
      have hf' : f = X - C (z : ℚ) := by
        rw [hX, ← hz, map_neg, sub_neg_eq_add]
      rw [hf', mirror_X_sub_C]
      rcases Int.natAbs_eq z with h | h
      · have hq : (z : ℚ) = (z.natAbs : ℚ) :=
          (congrArg (Int.cast : ℤ → ℚ) h).trans (Int.cast_natCast _)
        rw [intPair, hq]
      · have hq : (z : ℚ) = -(z.natAbs : ℚ) := by
          rw [congrArg (Int.cast : ℤ → ℚ) h, Int.cast_neg, Int.cast_natCast]
        rw [intPair, hq, map_neg, sub_neg_eq_add, ← sub_eq_add_neg, Set.pair_comm]
    · rintro ⟨q, ⟨_, hq2⟩, rfl⟩
      have hof : IsOrbitFactor m (X - C (q : ℚ)) := by
        simpa using isOrbitFactor_X_sub_C m (z := q) hq2
      refine ⟨⟨X - C (q : ℚ), hof, not_even_X_sub_C _, ?_⟩, ?_⟩
      · rw [intPair, mirror_X_sub_C]
      · intro f hf
        simp only [intPair, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl
        · exact natDegree_X_sub_C _
        · exact natDegree_X_add_C _
  unfold NI
  rw [hset, hinjP.ncard_image]

/-- Constant-term certificate: if `|R(0)|` is not a perfect square, then `2 N_II < r`. (Otherwise
the factors `normH f` of the irrational pairs would multiply to `R`, and each has constant term
`±f(0)²`.) -/
theorem two_NII_lt_aux (hmon : Secular_monic) (hm : m ≠ 0)
    (hsq : ¬ IsSquare |(secular m).eval 0|) : 2 * NII m < (Bset m).card := by
  classical
  by_contra hcon
  have hcon' : (Bset m).card ≤ 2 * NII m := by omega
  set F := (TII_finite m).toFinset with hF
  have hFprop : ∀ h ∈ F, h.Monic ∧ Irreducible h ∧ h ∣ Rq m ∧ 2 ≤ h.natDegree :=
    fun h hh => TII_prop m h ((TII_finite m).mem_toFinset.1 hh)
  have hcard : NII m ≤ F.card := by
    rw [hF, ← Set.ncard_eq_toFinset_card _ (TII_finite m)]
    exact NII_le m
  have hsum : F.card • 2 ≤ ∑ h ∈ F, h.natDegree :=
    Finset.card_nsmul_le_sum F (fun h => h.natDegree) 2 (fun h hh => (hFprop h hh).2.2.2)
  rw [smul_eq_mul] at hsum
  have hdvd : (∏ h ∈ F, h) ∣ Rq m := by
    apply Finset.prod_dvd_of_coprime
    · intro h1 hh1 h2 hh2 hne
      exact coprime_of_ne (hFprop h1 hh1).1 (hFprop h2 hh2).1 (hFprop h1 hh1).2.1
        (hFprop h2 hh2).2.1 hne
    · intro h hh
      exact (hFprop h hh).2.2.1
  have hmonF : (∏ h ∈ F, h).Monic := monic_prod_of_monic _ _ (fun h hh => (hFprop h hh).1)
  have hdegF : (∏ h ∈ F, h).natDegree = ∑ h ∈ F, h.natDegree :=
    natDegree_prod_of_monic F (fun h => h) (fun h hh => (hFprop h hh).1)
  have hr := Rq_natDegree m hmon hm
  have heq : Rq m = ∏ h ∈ F, h :=
    eq_of_monic_of_dvd_of_natDegree_le hmonF ((hmon m hm).1.map _) hdvd (by omega)
  have hsqF : IsSquare |(∏ h ∈ F, h).eval 0| := by
    rw [eval_prod, Finset.abs_prod]
    apply Finset.prod_induction _ IsSquare (fun a b ha hb => ha.mul hb) (IsSquare.one)
    intro h hh
    obtain ⟨f, _, rfl⟩ := (TII_finite m).mem_toFinset.1 hh
    rw [eval_zero_normH]
    exact ⟨|f.eval 0|, by simp [abs_mul, sq]⟩
  rw [← heq] at hsqF
  have h0 := Rq_eval_intCast m 0
  rw [Int.cast_zero] at h0
  rw [h0, ← Int.cast_abs, Rat.isSquare_intCast_iff] at hsqF
  exact hsq hsqF

end Multiset

/-! ### Summary (statements used for Proposition 5.5 and Lemma 3.3(d)) -/

/-- `2 N_II + N_rat ≤ r`, where `N_rat` is the number of integer roots of `R`. -/
theorem two_NII_add_Nrat_le (hmon : Secular_monic) (m : Multiset ℕ) (hm : m ≠ 0) :
    2 * NII m + {z : ℤ | (secular m).eval z = 0}.ncard ≤ (Bset m).card := by
  have := intRoots_ncard_add_two_NII_le m hmon hm
  omega

/-- Lemma 3.3(d) for a multiset: finiteness, and `N_I + 2 N_II + N_ei ≤ r`. -/
theorem orbit_count (hmon : Secular_monic) (m : Multiset ℕ) (hm : m ≠ 0) :
    (nonEvenPairs m).Finite ∧
    {z : ℤ | (secular m).eval z = 0 ∧ Even z ∧ ¬ IsSquare z}.Finite ∧
    NI m + 2 * NII m + Nei m ≤ (Bset m).card := by
  set Z := {z : ℤ | (secular m).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} with hZdef
  have hZf : Z.Finite := (intRoots_finite m).subset (fun z hz => hz.1)
  refine ⟨?_, hZf, ?_⟩
  · apply ((orbitFactors_finite m).image (fun f => ({f, Challenge.mirror f} : Set ℚ[X]))).subset
    rintro P ⟨f, hf, -, rfl⟩
    exact ⟨f, hf, rfl⟩
  · have hdisj1 : Disjoint (TI m) (linOf Z) := by
      rw [Set.disjoint_left]
      rintro h ⟨f, ⟨hf, hne, hdeg⟩, rfl⟩ ⟨z, hz, hzh⟩
      have hX := hf.1.eq_X_add_C hdeg
      rw [hX, normH_X_add_C] at hzh
      have h1 : ((z : ℚ)) = f.coeff 0 ^ 2 := X_sub_C_injective hzh
      apply hz.2.2
      rw [← Rat.isSquare_intCast_iff, h1]
      exact ⟨f.coeff 0, sq _⟩
    have hdisj2 : Disjoint (TI m ∪ linOf Z) (TII m) := by
      rw [Set.disjoint_left]
      intro h h1 h2
      have e2 := (TII_prop m h h2).2.2.2
      rcases h1 with h1 | h1
      · have := (TI_prop m h h1).2.2.2
        omega
      · have := (linOf_prop m (fun z hz => hz.1) h h1).2.2.2
        omega
    have hAf : (TI m ∪ linOf Z).Finite := (TI_finite m).union (hZf.image _)
    have key := ncard_add_two_mul_ncard_le (Rq_ne_zero m) hAf (TII_finite m) hdisj2
      (by
        rintro h (hh | hh)
        · obtain ⟨a, b, c, d⟩ := TI_prop m h hh
          exact ⟨a, b, c, d.ge⟩
        · obtain ⟨a, b, c, d⟩ := linOf_prop m (fun z hz => hz.1) h hh
          exact ⟨a, b, c, d.ge⟩)
      (TII_prop m)
    rw [Set.ncard_union_eq hdisj1 (TI_finite m) (hZf.image _), linOf_ncard,
      Rq_natDegree m hmon hm] at key
    have h1 := NI_le m
    have h2 := NII_le m
    have h3 : Nei m = Z.ncard := rfl
    omega

/-- (b′) `N_I = #{q ≥ 1 : R(q²) = 0}` (and this set is finite). -/
theorem NI_eq (hmon : Secular_monic) (m : Multiset ℕ) (hm : m ≠ 0) :
    {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0}.Finite ∧
    NI m = {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0}.ncard :=
  NI_eq_aux m hmon hm

/-- Constant-term certificate: if `|R(0)|` is not a perfect square, then `2 N_II < r`. -/
theorem two_NII_lt_of_not_isSquare (hmon : Secular_monic) (m : Multiset ℕ) (hm : m ≠ 0)
    (hsq : ¬ IsSquare |(secular m).eval 0|) : 2 * NII m < (Bset m).card :=
  two_NII_lt_aux m hmon hm hsq

end

end P8Orb
