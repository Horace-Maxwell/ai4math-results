import Research.Backfill.Paper8.Proof.Rows.Count

/-!
# Paper 8, rows: counting the members of the bare row that fail at an orbit

With (4.2), `G(θ) = (ε + U(t)) + θ (1 - 2m/t)`. On an even orbit, `θ ∉ ℚ(t)` (Lemma 3.3(a))
forces `ε + U(t) = 0` and `t = 2m` for every root, so at most one member fails. On a non-even
pair with root `θ₀`, the member fails iff `θ₀ - 2m/θ₀ = ±(ε + U(t₀))`: at most two `m` for each
`ε`, and at most one `(ε, m)` per sign when `t₀ ∉ ℚ` (then `2/θ₀ ∉ ℚ`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

variable {k : ℕ} (a : Fin k → ℕ)

theorem zero_mem_Bset (h0 : 1 ≤ kb (branchMS a) 0) : 0 ∈ Bset (branchMS a) := by
  unfold Bset
  rw [Multiset.mem_toFinset]
  exact Multiset.count_pos.1 h0

section Bare

variable (h0 : 1 ≤ kb (branchMS a) 0)
include h0

/-- A member of the bare row that fails at an even orbit has `θ² = 2m` on the whole orbit and
`ε + U(2m) = 0`. -/
theorem bare_fails_even (h3a : Lemma_3_3_a) (h3e : Lemma_3_3_e) (hk : 0 < k) (ε : ℤ) (mm : ℕ)
    (s : TV a → ℝ) (hs : IsBareRowMember a ε mm s) (f : ℚ[X])
    (hf : IsOrbitFactor (branchMS a) f) (hev : IsEvenPoly f) (hfail : FailsAtOrbit a s f) :
    (∀ θ ∈ f.rootSet ℝ, θ ^ 2 = 2 * (mm : ℝ)) ∧ (ε : ℝ) + Ufun a (2 * mm) = 0 := by
  obtain ⟨θ1, hθ1, hG1⟩ := hfail
  have key : ∀ θ ∈ f.rootSet ℝ, θ ^ 2 = 2 * (mm : ℝ) ∧ (ε : ℝ) + Ufun a (θ ^ 2) = 0 := by
    intro θ hθ
    have hG := h3e k a hk s hs.1 f hf θ1 hθ1 θ hθ hG1
    have hsec := isSecular_of_mem_rootSet _ hf hθ
    have hθ0 : θ ≠ 0 := ne_zero_of_isSecular _ hsec (zero_mem_Bset a h0)
    rw [Gs_bare a h0 ε mm s hs θ hsec] at hG
    have hlin : ((ε : ℝ) + Ufun a (θ ^ 2)) * θ = 2 * mm - θ ^ 2 := by
      have h2 : 2 * (mm : ℝ) / θ * θ = 2 * mm := div_mul_cancel₀ _ hθ0
      have h3 : ((ε : ℝ) + Ufun a (θ ^ 2) + θ - 2 * mm / θ) * θ = 0 := by rw [hG, zero_mul]
      linear_combination h3 + h2
    by_cases hc : (ε : ℝ) + Ufun a (θ ^ 2) = 0
    · refine ⟨?_, hc⟩
      rw [hc, zero_mul] at hlin
      linarith
    · exfalso
      apply (h3a k a hk f hf).2 θ (aeval_of_mem_rootSet hθ) hev
      have hθeq : θ = (2 * mm - θ ^ 2) / ((ε : ℝ) + Ufun a (θ ^ 2)) := by
        rw [eq_div_iff hc]
        linarith
      have h2m : 2 * (mm : ℝ) ∈ QAdj (θ ^ 2) := by
        simpa using natCast_mem_QAdj (θ ^ 2) (2 * mm)
      have hmem : (2 * mm - θ ^ 2) / ((ε : ℝ) + Ufun a (θ ^ 2)) ∈ QAdj (θ ^ 2) :=
        div_mem (sub_mem h2m (self_mem_QAdj _)) (add_mem (intCast_mem_QAdj _ ε) (Ufun_mem a _))
      rw [← hθeq] at hmem
      exact hmem
  obtain ⟨h1, h2⟩ := key θ1 hθ1
  exact ⟨fun θ hθ => (key θ hθ).1, by rw [← h1]; exact h2⟩

theorem bare_count_even (h3a : Lemma_3_3_a) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℕ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0, IsBareRowMember a ε mm (mem ε mm))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hev : IsEvenPoly f) :
    {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
        FailsAtOrbit a (mem p.1 p.2) f}.encard ≤ 1 ∧
      ((∃ p : ℤ × ℕ, p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
          FailsAtOrbit a (mem p.1 p.2) f) →
        ∃ z : ℤ, Even z ∧ ∀ θ ∈ f.rootSet ℝ, θ ^ 2 = (z : ℝ)) := by
  constructor
  · rw [Set.encard_le_one_iff]
    rintro ⟨ε, m⟩ ⟨ε', m'⟩ ⟨hε, hm, hfail⟩ ⟨hε', hm', hfail'⟩
    obtain ⟨hall, hU⟩ :=
      bare_fails_even a h0 h3a h3e hk ε m _ (hmem ε hε m hm) f hf hev hfail
    obtain ⟨hall', hU'⟩ := bare_fails_even a h0 h3a h3e hk ε' m' _ (hmem ε' hε' m' hm') f hf
      hev hfail'
    obtain ⟨θ1, hθ1, -⟩ := hfail
    have hmm : (m : ℝ) = m' := by
      have := (hall θ1 hθ1).symm.trans (hall' θ1 hθ1)
      linarith
    have hmm' : m = m' := by exact_mod_cast hmm
    subst hmm'
    have : (ε : ℝ) = ε' := by linarith
    have : ε = ε' := by exact_mod_cast this
    rw [this]
  · rintro ⟨⟨ε, m⟩, hε, hm, hfail⟩
    obtain ⟨hall, -⟩ := bare_fails_even a h0 h3a h3e hk ε m _ (hmem ε hε m hm) f hf hev hfail
    refine ⟨2 * (m : ℤ), even_two_mul _, fun θ hθ => ?_⟩
    rw [hall θ hθ]
    push_cast
    ring

/-- For a member of the bare row, failing at a non-even pair is an affine condition on `m`. -/
theorem bare_fails_iff (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k) (ε : ℤ) (mm : ℕ)
    (s : TV a → ℝ) (hs : IsBareRowMember a ε mm s) (f : ℚ[X])
    (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f) (θ0 : ℝ)
    (hθ0 : θ0 ∈ f.rootSet ℝ) :
    FailsAtPair a s f ↔
      θ0 + ((mm : ℤ) : ℝ) * (-2 / θ0) = (ε : ℝ) + Ufun a (θ0 ^ 2) ∨
      θ0 + ((mm : ℤ) : ℝ) * (-2 / θ0) = -((ε : ℝ) + Ufun a (θ0 ^ 2)) := by
  have hsec := isSecular_of_mem_rootSet _ hf hθ0
  have hsec' : IsSecular (branchMS a) (-θ0) := by
    unfold IsSecular at hsec ⊢
    rwa [neg_sq]
  have hθ0z : θ0 ≠ 0 := ne_zero_of_isSecular _ hsec (zero_mem_Bset a h0)
  rw [failsAtPair_iff a h3b h3e hk s hs.1 f hf hne θ0 hθ0, Gs_bare a h0 ε mm s hs θ0 hsec,
    Gs_bare a h0 ε mm s hs (-θ0) hsec', neg_sq]
  have e1 : ((mm : ℤ) : ℝ) * (-2 / θ0) = -(2 * (mm : ℝ) / θ0) := by push_cast; ring
  have e2 : 2 * (mm : ℝ) / -θ0 = -(2 * (mm : ℝ) / θ0) := by rw [div_neg]
  rw [e1, e2]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

theorem bare_count_int (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℕ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0, IsBareRowMember a ε mm (mem ε mm))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f) :
    {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
      FailsAtPair a (mem p.1 p.2) f}.encard ≤ 4 := by
  by_cases hroot : ∃ θ0, θ0 ∈ f.rootSet ℝ
  · obtain ⟨θ0, hθ0⟩ := hroot
    have hsec := isSecular_of_mem_rootSet _ hf hθ0
    have hθ0z : θ0 ≠ 0 := ne_zero_of_isSecular _ hsec (zero_mem_Bset a h0)
    have hw : -2 / θ0 ≠ 0 := div_ne_zero (by norm_num) hθ0z
    have heps : ∀ ε ∈ ({1, -1} : Set ℤ),
        {m : ℕ | m ≤ kb (branchMS a) 0 ∧ FailsAtPair a (mem ε m) f}.encard ≤ 2 := by
      intro ε hε
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun m : ℕ => (m : ℤ)) ?_
        (fun x _ y _ h => Nat.cast_injective h))
        (encard_affine_le_two θ0 (-2 / θ0) ((ε : ℝ) + Ufun a (θ0 ^ 2)) hw)
      rintro m ⟨hm, hfail⟩
      exact (bare_fails_iff a h0 h3b h3e hk ε m _ (hmem ε hε m hm) f hf hne θ0 hθ0).1 hfail
    refine le_trans (encard_pm_image_le _ _ _ ?_)
      (le_trans (add_le_add (heps 1 (by simp)) (heps (-1) (by simp))) (by norm_num))
    rintro ⟨ε, m⟩ ⟨hε, hm, hfail⟩
    rcases (mem_pm_iff.1 hε) with h | h
    · subst h
      exact Or.inl ⟨rfl, hm, hfail⟩
    · subst h
      exact Or.inr ⟨rfl, hm, hfail⟩
  · push Not at hroot
    have : {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
        FailsAtPair a (mem p.1 p.2) f} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ _ => not_failsAtPair_of_empty a f hroot _
    rw [this, Set.encard_empty]
    exact zero_le

theorem bare_count_irr (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℕ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0, IsBareRowMember a ε mm (mem ε mm))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f)
    (hdeg : f.natDegree ≠ 1) :
    {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
      FailsAtPair a (mem p.1 p.2) f}.encard ≤ 2 := by
  by_cases hroot : ∃ θ0, θ0 ∈ f.rootSet ℝ
  · obtain ⟨θ0, hθ0⟩ := hroot
    have hsec := isSecular_of_mem_rootSet _ hf hθ0
    have hθ0z : θ0 ≠ 0 := ne_zero_of_isSecular _ hsec (zero_mem_Bset a h0)
    have ht := sq_irrational a h3b hk f hf hne hdeg θ0 hθ0
    have hwq : ∀ c : ℝ, c ≠ 0 → (∃ c' : ℚ, (c' : ℝ) = c) → ∀ q : ℚ, (q : ℝ) ≠ c / θ0 := by
      rintro c hc ⟨c', rfl⟩ q hq
      have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; exact div_ne_zero hc hθ0z
      apply ht ((c' / q) ^ 2)
      push_cast
      rw [hq]
      field_simp
    have hw1 := hwq (-2) (by norm_num) ⟨-2, by push_cast; ring⟩
    have hw2 := hwq 2 (by norm_num) ⟨2, by push_cast; ring⟩
    set U := Ufun a (θ0 ^ 2)
    let g : ℤ × ℕ → ℤ × ℤ := fun p => (p.1, (p.2 : ℤ))
    have hg : Set.InjOn g Set.univ := by
      rintro ⟨x1, x2⟩ - ⟨y1, y2⟩ - h
      simp only [g, Prod.mk.injEq, Nat.cast_inj] at h
      rw [h.1, h.2]
    calc _ ≤ ({p : ℤ × ℕ | ((g p).1 : ℝ) + (g p).2 * (-2 / θ0) = -θ0 - U} ∪
          {p : ℤ × ℕ | ((g p).1 : ℝ) + (g p).2 * (2 / θ0) = θ0 - U}).encard := by
          refine Set.encard_le_encard ?_
          rintro ⟨ε, m⟩ ⟨hε, hm, hfail⟩
          rcases (bare_fails_iff a h0 h3b h3e hk ε m _ (hmem ε hε m hm) f hf hne θ0 hθ0).1
            hfail with h | h
          · right
            show (ε : ℝ) + ((m : ℤ) : ℝ) * (2 / θ0) = θ0 - U
            have : ((m : ℤ) : ℝ) * (2 / θ0) = -(((m : ℤ) : ℝ) * (-2 / θ0)) := by ring
            rw [this]
            linarith
          · left
            show (ε : ℝ) + ((m : ℤ) : ℝ) * (-2 / θ0) = -θ0 - U
            linarith
      _ ≤ _ + _ := Set.encard_union_le _ _
      _ ≤ 1 + 1 := by
          refine add_le_add ?_ ?_
          · exact le_trans (Set.encard_le_encard_of_injOn (f := g) (t := {q : ℤ × ℤ |
              (q.1 : ℝ) + q.2 * (-2 / θ0) = -θ0 - U}) (fun p hp => hp)
              (hg.mono (Set.subset_univ _))) (encard_sol_le_one _ _ hw1)
          · exact le_trans (Set.encard_le_encard_of_injOn (f := g) (t := {q : ℤ × ℤ |
              (q.1 : ℝ) + q.2 * (2 / θ0) = θ0 - U}) (fun p hp => hp)
              (hg.mono (Set.subset_univ _))) (encard_sol_le_one _ _ hw2)
      _ = 2 := by norm_num
  · push Not at hroot
    have : {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ kb (branchMS a) 0 ∧
        FailsAtPair a (mem p.1 p.2) f} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ _ => not_failsAtPair_of_empty a f hroot _
    rw [this, Set.encard_empty]
    exact zero_le

end Bare

end P8Rows
