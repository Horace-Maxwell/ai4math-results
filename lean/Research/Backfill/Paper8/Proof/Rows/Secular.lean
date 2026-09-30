import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, rows: facts about `B`, `I_b`, the secular polynomial and orbit factors

Elementary facts used by the two rows of switchings (Lemmas 4.2, 4.3) and Corollary 4.4:
`|I_b| = k_b`, `b* ∈ B`, the first element of `I_b` has `posIn = 0`; the value of `R` at a point
of `B` is nonzero, so a secular `θ` has `θ² ∉ B` and `F(θ²) = 1`; every secular `θ` is a root
of an orbit factor (its minimal polynomial); the roots of `mirror f` are the negatives of those
of `f`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

section Branches

variable {k : ℕ} (a : Fin k → ℕ)

theorem mem_Bset_iff (b : ℕ) : b ∈ Bset (branchMS a) ↔ ∃ i, a i = b := by
  simp [Bset, branchMS]

theorem mem_Ib (b : ℕ) (i : Fin k) : i ∈ Ib a b ↔ a i = b := by
  simp [Ib]

theorem card_Ib (b : ℕ) : (Ib a b).card = kb (branchMS a) b := by
  classical
  simp only [Ib, kb, branchMS, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun i _ => eq_comm)

theorem a_mem_Bset (i : Fin k) : a i ∈ Bset (branchMS a) :=
  (mem_Bset_iff a (a i)).2 ⟨i, rfl⟩

theorem Bset_nonempty (hk : 0 < k) : (Bset (branchMS a)).Nonempty :=
  ⟨a ⟨0, hk⟩, a_mem_Bset a _⟩

theorem bstar_mem (hk : 0 < k) : bstar (branchMS a) ∈ Bset (branchMS a) := by
  obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup _ (Bset_nonempty a hk) id
  unfold bstar
  rw [hsup]
  exact hb

/-- The smallest element of `I_b` has position `0` in `I_b`. -/
theorem exists_posIn_zero (b : ℕ) (hb : b ∈ Bset (branchMS a)) :
    ∃ i, a i = b ∧ posIn a i = 0 := by
  classical
  have hne : (Ib a b).Nonempty := by
    obtain ⟨i, hi⟩ := (mem_Bset_iff a b).1 hb
    exact ⟨i, (mem_Ib a b i).2 hi⟩
  set i := (Ib a b).min' hne with hi
  have hib : a i = b := (mem_Ib a b i).1 (Finset.min'_mem _ hne)
  refine ⟨i, hib, ?_⟩
  unfold posIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro j - ⟨hj, hja⟩
  have hjI : j ∈ Ib a b := (mem_Ib a b j).2 (hja.trans hib)
  exact absurd (Finset.min'_le _ _ hjI) (not_le.2 hj)

theorem kb_pos (b : ℕ) (hb : b ∈ Bset (branchMS a)) : 0 < kb (branchMS a) b := by
  rw [← card_Ib]
  obtain ⟨i, hi⟩ := (mem_Bset_iff a b).1 hb
  exact Finset.card_pos.2 ⟨i, (mem_Ib a b i).2 hi⟩

end Branches

section Secular

variable (m : Multiset ℕ)

theorem aeval_secular (t : ℝ) :
    aeval t (secular m) = ∏ b ∈ Bset m, (t - b) -
      ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, (t - b') := by
  simp [secular, map_prod, map_sum]

theorem kb_pos_of_mem (b : ℕ) (hb : b ∈ Bset m) : 0 < kb m b := by
  unfold kb
  exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 hb)

/-- `R(b) = -k_b ∏_{b' ≠ b} (b - b') ≠ 0` for `b ∈ B`. -/
theorem aeval_secular_mem_ne_zero (b0 : ℕ) (hb0 : b0 ∈ Bset m) :
    aeval (b0 : ℝ) (secular m) ≠ 0 := by
  classical
  rw [aeval_secular]
  have h1 : ∏ b ∈ Bset m, ((b0 : ℝ) - b) = 0 := Finset.prod_eq_zero hb0 (sub_self _)
  have h2 : ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, ((b0 : ℝ) - b') =
      (kb m b0 : ℝ) * ∏ b' ∈ (Bset m).erase b0, ((b0 : ℝ) - b') := by
    refine Finset.sum_eq_single b0 (fun b hb hne => ?_) (fun h => absurd hb0 h)
    have : b0 ∈ (Bset m).erase b := Finset.mem_erase.2 ⟨fun h => hne h.symm, hb0⟩
    rw [Finset.prod_eq_zero this (sub_self _), mul_zero]
  rw [h1, h2, zero_sub, neg_ne_zero]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (kb_pos_of_mem m b0 hb0).ne'
  · rw [Finset.prod_ne_zero_iff]
    intro b hb
    have hne : b ≠ b0 := (Finset.mem_erase.1 hb).1
    rw [sub_ne_zero]
    exact_mod_cast hne.symm

theorem secular_ne_zero (hB : (Bset m).Nonempty) : secular m ≠ 0 := by
  obtain ⟨b0, hb0⟩ := hB
  intro h
  apply aeval_secular_mem_ne_zero m b0 hb0
  rw [h, map_zero]

/-- A secular `θ` has `θ² ∉ B`. -/
theorem sq_ne_of_isSecular {θ : ℝ} (hθ : IsSecular m θ) (b : ℕ) (hb : b ∈ Bset m) :
    θ ^ 2 ≠ (b : ℝ) := by
  intro h
  apply aeval_secular_mem_ne_zero m b hb
  rw [← h]
  exact hθ

/-- `F(t) = ∑_b k_b/(t - b) = 1` at `t = θ²` for a secular `θ`. -/
theorem F_eq_one_of_isSecular {θ : ℝ} (hθ : IsSecular m θ) :
    ∑ b ∈ Bset m, (kb m b : ℝ) / (θ ^ 2 - b) = 1 := by
  classical
  have hsec : aeval (θ ^ 2) (secular m) = 0 := hθ
  rw [aeval_secular] at hsec
  set t := θ ^ 2 with ht
  have hne : ∀ b ∈ Bset m, t - (b : ℝ) ≠ 0 := fun b hb =>
    sub_ne_zero.2 (sq_ne_of_isSecular m hθ b hb)
  have hP : ∏ b ∈ Bset m, (t - b) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  have key : ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, (t - b') =
      (∑ b ∈ Bset m, (kb m b : ℝ) / (t - b)) * ∏ b ∈ Bset m, (t - b) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← Finset.mul_prod_erase (Bset m) (fun b' => t - (b' : ℝ)) hb]
    field_simp [hne b hb]
  rw [key] at hsec
  have : (1 - ∑ b ∈ Bset m, (kb m b : ℝ) / (t - b)) * ∏ b ∈ Bset m, (t - b) = 0 := by
    linear_combination hsec
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hP

theorem ne_zero_of_isSecular {θ : ℝ} (hθ : IsSecular m θ) (h0 : 0 ∈ Bset m) :
    θ ≠ 0 := by
  intro h
  apply sq_ne_of_isSecular m hθ 0 h0
  simp [h]

end Secular

section Orbits

variable (m : Multiset ℕ)

theorem aeval_R2 (θ : ℝ) : aeval θ (R2 m) = aeval (θ ^ 2) (secular m) := by
  unfold R2
  rw [expand_aeval, ← algebraMap_int_eq, aeval_map_algebraMap]

theorem R2_ne_zero (hB : (Bset m).Nonempty) : R2 m ≠ 0 := by
  unfold R2
  rw [Ne, expand_eq_zero two_pos, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]
  exact secular_ne_zero m hB

/-- A root of an orbit factor is secular. -/
theorem isSecular_of_mem_rootSet {f : ℚ[X]} (hf : IsOrbitFactor m f) {θ : ℝ}
    (hθ : θ ∈ f.rootSet ℝ) : IsSecular m θ := by
  obtain ⟨g, hg⟩ := hf.2.2
  have h0 : aeval θ f = 0 := aeval_eq_zero_of_mem_rootSet hθ
  have : aeval θ (R2 m) = 0 := by rw [hg, map_mul, h0, zero_mul]
  rw [aeval_R2] at this
  exact this

/-- Every secular `θ` is a root of an orbit factor, namely of its minimal polynomial. -/
theorem exists_orbitFactor (hB : (Bset m).Nonempty) {θ : ℝ} (hθ : IsSecular m θ) :
    ∃ f : ℚ[X], IsOrbitFactor m f ∧ θ ∈ f.rootSet ℝ := by
  have hR : aeval θ (R2 m) = 0 := by rw [aeval_R2]; exact hθ
  have hint : IsIntegral ℚ θ := isAlgebraic_iff_isIntegral.1 ⟨R2 m, R2_ne_zero m hB, hR⟩
  refine ⟨minpoly ℚ θ, ⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.dvd ℚ θ hR⟩, ?_⟩
  rw [mem_rootSet]
  exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ θ⟩

theorem comp_neg_X_comp_neg_X (f : ℚ[X]) : (f.comp (-X)).comp (-X) = f := by
  rw [comp_assoc]
  simp

theorem aeval_mirror (f : ℚ[X]) (θ : ℝ) :
    aeval θ (mirror f) = (-1) ^ f.natDegree * aeval (-θ) f := by
  unfold mirror
  rw [map_mul, aeval_C, aeval_comp]
  simp

theorem mirror_ne_zero {f : ℚ[X]} (hf : f ≠ 0) : mirror f ≠ 0 := by
  unfold mirror
  refine mul_ne_zero (by simp) ?_
  intro h
  apply hf
  rw [← comp_neg_X_comp_neg_X f, h, zero_comp]

/-- The roots of `mirror f` are the negatives of the roots of `f`. -/
theorem mem_rootSet_mirror {f : ℚ[X]} (θ : ℝ) :
    θ ∈ (mirror f).rootSet ℝ ↔ -θ ∈ f.rootSet ℝ := by
  by_cases hf : f = 0
  · subst hf
    simp [mirror]
  rw [mem_rootSet, mem_rootSet, aeval_mirror]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hf, ?_⟩
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  · rintro ⟨-, h⟩
    exact ⟨mirror_ne_zero hf, by rw [h, mul_zero]⟩

theorem natDegree_mirror (f : ℚ[X]) : (mirror f).natDegree = f.natDegree := by
  unfold mirror
  rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_comp]
  simp

end Orbits

end P8Rows
