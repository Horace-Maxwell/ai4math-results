import Research.Backfill.Paper8.Proof.Rows.Lemmas

/-!
# Paper 8, rows: Corollary 4.4

If no member of a row were good, every member would fail (S) by Lemma 3.2 ((L) and (Z) hold), so
every member would fail at an orbit (every secular `θ` is a root of an orbit factor). The failing
members are counted pair by pair (at most 4 per integer pair, 2 per irrational pair) and, for the
bare row, even orbit by even orbit (at most one member each, injectively labelled by an even
non-square root `2m` of `R`); this is less than the size of the row under (a′) or (b′).
The set of pairs is finite because the monic irreducible factors of `R(x²)` are among its
normalized factors.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

variable {k : ℕ} (a : Fin k → ℕ)

/-! ### Finiteness -/

theorem orbitFactors_finite (hk : 0 < k) :
    {f : ℚ[X] | IsOrbitFactor (branchMS a) f}.Finite := by
  classical
  have hR := R2_ne_zero (branchMS a) (Bset_nonempty a hk)
  refine (UniqueFactorizationMonoid.normalizedFactors (R2 (branchMS a))).toFinset.finite_toSet.subset
    ?_
  rintro f ⟨hmon, hirr, hdvd⟩
  obtain ⟨q, hq, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hR hirr hdvd
  have hq0 : q ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq
  have hqmon : q.Monic := by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
    exact Polynomial.monic_normalize hq0
  have : f = q := Polynomial.eq_of_monic_of_associated hmon hqmon hassoc
  subst this
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 hq)

theorem nonEvenPairs_finite (hk : 0 < k) : (nonEvenPairs (branchMS a)).Finite := by
  refine ((orbitFactors_finite a hk).image (fun f => ({f, mirror f} : Set ℚ[X]))).subset ?_
  rintro P ⟨f, hf, -, rfl⟩
  exact ⟨f, hf, rfl⟩

theorem neiSet_finite (hk : 0 < k) :
    {z : ℤ | (secular (branchMS a)).eval z = 0 ∧ Even z ∧ ¬ IsSquare z}.Finite :=
  (Polynomial.finite_setOfPred_isRoot (secular_ne_zero _ (Bset_nonempty a hk))).subset
    (fun _ hz => hz.1)

/-! ### Failing at a pair depends only on the pair -/

/-- `s` fails at the pair `P` (a set of polynomials). -/
def FailsP (s : TV a → ℝ) (P : Set ℚ[X]) : Prop :=
  ∃ h ∈ P, ∃ θ ∈ h.rootSet ℝ, Gs a s θ = 0

theorem failsAtPair_iff_failsP (s : TV a → ℝ) (f : ℚ[X]) :
    FailsAtPair a s f ↔ FailsP a s {f, mirror f} := by
  constructor
  · rintro ⟨θ, hθ | hθ, hG⟩
    · exact ⟨f, Set.mem_insert _ _, θ, hθ, hG⟩
    · exact ⟨mirror f, Set.mem_insert_of_mem _ rfl, θ, hθ, hG⟩
  · rintro ⟨h, hh, θ, hθ, hG⟩
    rcases hh with rfl | hh
    · exact ⟨θ, Or.inl hθ, hG⟩
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ⟨θ, Or.inr hθ, hG⟩

/-- Every switching failing (S) fails at an even orbit or at a non-even pair. -/
theorem fails_of_not_condS (hk : 0 < k) (s : TV a → ℝ) (hS : ¬ condS a s) :
    (∃ f, IsOrbitFactor (branchMS a) f ∧ IsEvenPoly f ∧ FailsAtOrbit a s f) ∨
      ∃ P ∈ nonEvenPairs (branchMS a), FailsP a s P := by
  unfold condS at hS
  push Not at hS
  obtain ⟨θ, hθ, hG⟩ := hS
  obtain ⟨f, hf, hθf⟩ := exists_orbitFactor _ (Bset_nonempty a hk) hθ
  by_cases hev : IsEvenPoly f
  · exact Or.inl ⟨f, hf, hev, θ, hθf, hG⟩
  · exact Or.inr ⟨{f, mirror f}, ⟨f, hf, hev, rfl⟩,
      (failsAtPair_iff_failsP a s f).1 ⟨θ, Or.inl hθf, hG⟩⟩

/-! ### Counting over the pairs -/

theorem natDegree_of_mem_pair {f g : ℚ[X]} (hg : g ∈ ({f, mirror f} : Set ℚ[X])) :
    g.natDegree = f.natDegree := by
  rcases hg with rfl | hg
  · rfl
  · rw [Set.mem_singleton_iff] at hg
    rw [hg, natDegree_mirror]

theorem encard_biUnion_pairs_le (hk : 0 < k) {π : Type*} (X : Set ℚ[X] → Set π)
    (hX : ∀ f, IsOrbitFactor (branchMS a) f → ¬ IsEvenPoly f →
      (X {f, mirror f}).encard ≤ if f.natDegree = 1 then 4 else 2) :
    (⋃ P ∈ nonEvenPairs (branchMS a), X P).encard ≤
      ((4 * NI (branchMS a) + 2 * NII (branchMS a) : ℕ) : ℕ∞) := by
  classical
  have hfin := nonEvenPairs_finite a hk
  set T := hfin.toFinset with hT
  have hU : (⋃ P ∈ nonEvenPairs (branchMS a), X P) = ⋃ P ∈ T, X P := by
    ext p
    simp [T]
  rw [hU]
  refine le_trans (Finset.set_encard_biUnion_le T X) ?_
  let Q : Set ℚ[X] → Prop := fun P => ∀ f ∈ P, f.natDegree = 1
  have hc : ∀ P ∈ T, (X P).encard ≤ if Q P then 4 else 2 := by
    intro P hP
    obtain ⟨f, hf, hne, rfl⟩ := (hfin.mem_toFinset).1 hP
    refine le_trans (hX f hf hne) ?_
    by_cases hd : f.natDegree = 1
    · have hQ : Q {f, mirror f} := by
        intro g hg
        rcases hg with rfl | hg
        · exact hd
        · rw [Set.mem_singleton_iff] at hg
          rw [hg, natDegree_mirror]
          exact hd
      simp [hd, hQ]
    · have hQ : ¬ Q {f, mirror f} := fun h => hd (h f (Set.mem_insert _ _))
      simp [hd, hQ]
  refine le_trans (Finset.sum_le_sum hc) ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hNI : (T.filter Q).card = NI (branchMS a) := by
    unfold NI
    rw [← Set.ncard_coe_finset]
    congr 1
    ext P
    simp [T, Q]
  have hNII : (T.filter (fun P => ¬ Q P)).card = NII (branchMS a) := by
    unfold NII
    rw [← Set.ncard_coe_finset]
    congr 1
    ext P
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, T]
    constructor
    · rintro ⟨hP, h⟩
      refine ⟨hP, ?_⟩
      obtain ⟨f, -, -, rfl⟩ := hP
      intro g hg hd
      apply h
      intro g' hg'
      rw [natDegree_of_mem_pair hg']
      rw [natDegree_of_mem_pair hg] at hd
      exact hd
    · rintro ⟨hP, h⟩
      refine ⟨hP, fun hall => ?_⟩
      obtain ⟨f, -, -, rfl⟩ := hP
      exact h f (Set.mem_insert _ _) (hall f (Set.mem_insert _ _))
  rw [hNI, hNII]
  push_cast
  simp only [nsmul_eq_mul]
  rw [mul_comm (NI (branchMS a) : ℕ∞), mul_comm (NII (branchMS a) : ℕ∞)]

/-- The rows have `2|S|` members. -/
theorem encard_pm_prod {α : Type*} (S : Set α) :
    {p : ℤ × α | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ S}.encard = S.encard + S.encard := by
  have hset : {p : ℤ × α | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ S} =
      (fun x => ((1 : ℤ), x)) '' S ∪ (fun x => ((-1 : ℤ), x)) '' S := by
    ext ⟨ε, x⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Prod.mk.injEq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact Or.inl ⟨x, hx, h.symm, rfl⟩
      · exact Or.inr ⟨x, hx, h.symm, rfl⟩
    · rintro (⟨y, hy, h1, rfl⟩ | ⟨y, hy, h1, rfl⟩)
      · exact ⟨Or.inl h1.symm, hy⟩
      · exact ⟨Or.inr h1.symm, hy⟩
  rw [hset, Set.encard_union_eq]
  · rw [(Prod.mk_right_injective (1 : ℤ)).injOn.encard_image,
      (Prod.mk_right_injective (-1 : ℤ)).injOn.encard_image]
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, h⟩
    simp only [Prod.mk.injEq] at h
    omega

end P8Rows
