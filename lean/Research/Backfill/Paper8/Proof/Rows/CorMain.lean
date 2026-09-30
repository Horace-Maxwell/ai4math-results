import Research.Backfill.Paper8.Proof.Rows.Cor

/-!
# Paper 8, rows: Corollary 4.4 (assembly)

Leaf row under (a′): if no member were good, all `2|ℒ_β|` members would fail at a non-even pair
(no member fails at an even orbit), but at most `4 N_I + 2 N_II < 2|ℒ_β|` do. Bare row under
(b′): the members failing at an even orbit are labelled injectively by `2m`, an even root of `R`
that is not a square, so there are at most `N_ei` of them; with the pairs at most
`4 N_I + 2 N_II + N_ei < 2(k_0 + 1)`. Hypotheses: `StdLeafSums`, Lemma 3.2, Lemma 3.3(a),(b),(e).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

variable {k : ℕ} (a : Fin k → ℕ)

/-- Corollary 4.4 for the leaf row. -/
theorem cor_leaf (hStd : StdLeafSums) (h32 : Lemma_3_2) (h3a : Lemma_3_3_a)
    (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k) (hbs : 2 ≤ bstar (branchMS a))
    (β : ℕ) (hβ : β ∈ Bset (branchMS a)) (hβ1 : 1 ≤ β) (hcrit : CritAat (branchMS a) β)
    (mem : ℤ → ℤ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
      IsLeafRowMember a β ε Λ (mem ε Λ)) :
    ∃ ε ∈ ({1, -1} : Set ℤ), ∃ Λ ∈ Lset β (kb (branchMS a) β), IsGood (adjT a) (mem ε Λ) := by
  classical
  unfold CritAat at hcrit
  set L := Lset β (kb (branchMS a) β) with hL
  by_contra hcon
  push Not at hcon
  let X : Set ℚ[X] → Set (ℤ × ℤ) := fun P =>
    {p | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ L ∧ FailsP a (mem p.1 p.2) P}
  have hsub : {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ L} ⊆
      ⋃ P ∈ nonEvenPairs (branchMS a), X P := by
    rintro ⟨ε, Λ⟩ ⟨hε, hΛ⟩
    have hs := hmem ε hε Λ hΛ
    have hnot := hcon ε hε Λ hΛ
    rw [h32 k a hk _ hs.1] at hnot
    obtain ⟨hLc, hZc⟩ := leafRow_condL_condZ a hStd hk hbs β hβ1 ε Λ _ hs
    have hnS : ¬ condS a (mem ε Λ) := fun hS => hnot ⟨hS, hLc, hZc⟩
    rcases fails_of_not_condS a hk _ hnS with ⟨f, hf, hev, hfail⟩ | ⟨P, hP, hfail⟩
    · exact absurd hfail (leaf_not_failsAtOrbit a β hβ hβ1 h3a hk ε Λ _ hs f hf hev)
    · rw [Set.mem_iUnion₂]
      exact ⟨P, hP, hε, hΛ, hfail⟩
  have hX : ∀ f, IsOrbitFactor (branchMS a) f → ¬ IsEvenPoly f →
      (X {f, mirror f}).encard ≤ if f.natDegree = 1 then 4 else 2 := by
    intro f hf hne
    have hXeq : X {f, mirror f} = {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ L ∧
        FailsAtPair a (mem p.1 p.2) f} := by
      ext p
      simp only [X, Set.mem_ofPred_eq, failsAtPair_iff_failsP]
    rw [hXeq]
    by_cases hd : f.natDegree = 1
    · rw [ite_eq_left hd]
      exact leaf_count_total a β hβ hβ1 h3b h3e hk mem hmem f hf hne
    · rw [ite_eq_right hd]
      exact leaf_count_irr a β hβ hβ1 h3b h3e hk mem hmem f hf hne hd
  have h1 := le_trans (Set.encard_le_encard hsub) (encard_biUnion_pairs_le a hk X hX)
  rw [encard_pm_prod] at h1
  have hLpos : 0 < L.ncard := by omega
  have hLfin : L.Finite := Set.finite_of_ncard_pos hLpos
  rw [← hLfin.cast_ncard_eq] at h1
  have h2 : L.ncard + L.ncard ≤ 4 * NI (branchMS a) + 2 * NII (branchMS a) := by
    exact_mod_cast h1
  omega

/-- An even orbit at which a member of the bare row fails yields an even root `2m` of `R` that
is not a square. -/
theorem bare_even_root (h3a : Lemma_3_3_a) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (h0 : 1 ≤ kb (branchMS a) 0) (ε : ℤ) (mm : ℕ) (s : TV a → ℝ)
    (hs : IsBareRowMember a ε mm s) (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f)
    (hev : IsEvenPoly f) (hfail : FailsAtOrbit a s f) :
    (2 * (mm : ℤ)) ∈ {z : ℤ | (secular (branchMS a)).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} ∧
      (ε : ℝ) + Ufun a (2 * mm) = 0 := by
  obtain ⟨hall, hU⟩ := bare_fails_even a h0 h3a h3e hk ε mm s hs f hf hev hfail
  obtain ⟨θ1, hθ1, -⟩ := hfail
  have hsec := isSecular_of_mem_rootSet _ hf hθ1
  have hsq : θ1 ^ 2 = ((2 * (mm : ℤ) : ℤ) : ℝ) := by rw [hall θ1 hθ1]; push_cast; ring
  refine ⟨⟨?_, even_two_mul _, ?_⟩, hU⟩
  · have h1 : aeval (θ1 ^ 2) (secular (branchMS a)) = 0 := hsec
    rw [hsq, aeval_def, eval₂_at_intCast, Int.cast_id] at h1
    exact (algebraMap ℤ ℝ).injective_int (by rw [h1, map_zero])
  · rintro ⟨r, hr⟩
    apply (h3a k a hk f hf).2 θ1 (aeval_of_mem_rootSet hθ1) hev
    have h2 : θ1 ^ 2 = (r : ℝ) ^ 2 := by rw [hsq, hr]; push_cast; ring
    have h3 : (θ1 - r) * (θ1 + r) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · rw [show θ1 = (r : ℝ) by linarith]
      exact intCast_mem_QAdj _ r
    · rw [show θ1 = -(r : ℝ) by linarith]
      exact neg_mem (intCast_mem_QAdj _ r)

/-- Corollary 4.4 for the bare row. -/
theorem cor_bare (hStd : StdLeafSums) (h32 : Lemma_3_2) (h3a : Lemma_3_3_a)
    (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k) (hbs : 2 ≤ bstar (branchMS a))
    (hB : CritB (branchMS a)) (mem : ℤ → ℕ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0,
      IsBareRowMember a ε mm (mem ε mm)) :
    ∃ ε ∈ ({1, -1} : Set ℤ), ∃ mm ≤ kb (branchMS a) 0, IsGood (adjT a) (mem ε mm) := by
  classical
  obtain ⟨h0, hlt⟩ := hB
  by_contra hcon
  push Not at hcon
  set k0 := kb (branchMS a) 0 with hk0
  let S : Set ℕ := {m | m ≤ k0}
  let NeiS : Set ℤ := {z : ℤ | (secular (branchMS a)).eval z = 0 ∧ Even z ∧ ¬ IsSquare z}
  let E : Set (ℤ × ℕ) := {p | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ S ∧
    ∃ f, IsOrbitFactor (branchMS a) f ∧ IsEvenPoly f ∧ FailsAtOrbit a (mem p.1 p.2) f}
  let Y : Set ℚ[X] → Set (ℤ × ℕ) := fun P =>
    {p | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ S ∧ FailsP a (mem p.1 p.2) P}
  have hsub : {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ S} ⊆
      E ∪ ⋃ P ∈ nonEvenPairs (branchMS a), Y P := by
    rintro ⟨ε, m⟩ ⟨hε, hm⟩
    have hs := hmem ε hε m hm
    have hnot := hcon ε hε m hm
    rw [h32 k a hk _ hs.1] at hnot
    obtain ⟨hLc, hZc⟩ := bareRow_condL_condZ a hStd hk hbs ε m _ hs
    have hnS : ¬ condS a (mem ε m) := fun hS => hnot ⟨hS, hLc, hZc⟩
    rcases fails_of_not_condS a hk _ hnS with ⟨f, hf, hev, hfail⟩ | ⟨P, hP, hfail⟩
    · exact Or.inl ⟨hε, hm, f, hf, hev, hfail⟩
    · right
      rw [Set.mem_iUnion₂]
      exact ⟨P, hP, hε, hm, hfail⟩
  have hE : E.encard ≤ NeiS.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun p : ℤ × ℕ => 2 * (p.2 : ℤ)) ?_ ?_
    · rintro ⟨ε, m⟩ ⟨hε, hm, f, hf, hev, hfail⟩
      exact (bare_even_root a h3a h3e hk h0 ε m _ (hmem ε hε m hm) f hf hev hfail).1
    · rintro ⟨ε, m⟩ ⟨hε, hm, f, hf, hev, hfail⟩ ⟨ε', m'⟩ ⟨hε', hm', f', hf', hev', hfail'⟩ h
      simp only at h
      have hmm : m = m' := by omega
      subst hmm
      have h1 := (bare_even_root a h3a h3e hk h0 ε m _ (hmem ε hε m hm) f hf hev hfail).2
      have h2 :=
        (bare_even_root a h3a h3e hk h0 ε' m _ (hmem ε' hε' m hm') f' hf' hev' hfail').2
      have h3 : (ε : ℝ) = ε' := by linarith
      have h4 : ε = ε' := by exact_mod_cast h3
      rw [h4]
  have hY : ∀ f, IsOrbitFactor (branchMS a) f → ¬ IsEvenPoly f →
      (Y {f, mirror f}).encard ≤ if f.natDegree = 1 then 4 else 2 := by
    intro f hf hne
    have hYeq : Y {f, mirror f} = {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ k0 ∧
        FailsAtPair a (mem p.1 p.2) f} := by
      ext p
      simp only [Y, S, Set.mem_ofPred_eq, failsAtPair_iff_failsP]
    rw [hYeq]
    by_cases hd : f.natDegree = 1
    · rw [ite_eq_left hd]
      exact bare_count_int a h0 h3b h3e hk mem hmem f hf hne
    · rw [ite_eq_right hd]
      exact bare_count_irr a h0 h3b h3e hk mem hmem f hf hne hd
  have h1 := le_trans (Set.encard_le_encard hsub) (le_trans (Set.encard_union_le _ _)
    (add_le_add hE (encard_biUnion_pairs_le a hk Y hY)))
  rw [encard_pm_prod] at h1
  have hS : S.encard = ((k0 + 1 : ℕ) : ℕ∞) := by
    have : S = ↑(Finset.range (k0 + 1)) := by
      ext m
      simp [S]
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  have hNei : NeiS.encard = (Nei (branchMS a) : ℕ∞) := (neiSet_finite a hk).cast_ncard_eq.symm
  rw [hS, hNei] at h1
  have h2 : (k0 + 1) + (k0 + 1) ≤
      Nei (branchMS a) + (4 * NI (branchMS a) + 2 * NII (branchMS a)) := by
    exact_mod_cast h1
  omega

/-- **Corollary 4.4.** -/
theorem cor_4_4 (hStd : StdLeafSums) (h32 : Lemma_3_2) (h3a : Lemma_3_3_a)
    (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) : Cor_4_4 := by
  intro k a hk hbs
  refine ⟨fun β hβ hβ1 hcrit mem hmem =>
      cor_leaf a hStd h32 h3a h3b h3e hk hbs β hβ hβ1 hcrit mem hmem,
    fun hB mem hmem => cor_bare a hStd h32 h3a h3b h3e hk hbs hB mem hmem, ?_⟩
  rintro (⟨β, hβ, hβ1, hcrit⟩ | hB)
  · have hex : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
        ∃ s, IsLeafRowMember a β ε Λ s :=
      fun ε hε Λ hΛ => exists_leafRowMember a hStd β ε hε Λ hΛ
    choose! mem hmem using hex
    obtain ⟨ε, hε, Λ, hΛ, hgood⟩ :=
      cor_leaf a hStd h32 h3a h3b h3e hk hbs β hβ hβ1 hcrit mem hmem
    exact ⟨mem ε Λ, (hmem ε hε Λ hΛ).1, hgood⟩
  · have hex : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0,
        ∃ s, IsBareRowMember a ε mm s :=
      fun ε hε mm hmm => exists_bareRowMember a hStd ε hε mm hmm
    choose! mem hmem using hex
    obtain ⟨ε, hε, mm, hmm, hgood⟩ := cor_bare a hStd h32 h3a h3b h3e hk hbs hB mem hmem
    exact ⟨mem ε mm, (hmem ε hε mm hmm).1, hgood⟩

end P8Rows
