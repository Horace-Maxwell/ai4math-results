import Research.Backfill.Paper8.Proof.Rows.GFormula
import Research.SwitchingThmH
import Research.SwitchingRowCount

/-!
# Paper 8, rows: counting the members that fail at an orbit

Fix a root `θ₀` of a non-even orbit factor `f`. By Lemma 3.3(b),(e) a switching fails at the pair
of `f` iff `G(θ₀) = 0` or `G(-θ₀) = 0`; by (4.1) and (4.2) this is an affine condition on the
integer parameter, so at most two parameters fail for each `ε` (injectivity), and at most one per
equation when `t₀ = θ₀²` is irrational (`SwitchingThmH.sol_subsingleton`). On an even orbit,
`θ ∉ ℚ(t)` (Lemma 3.3(a)) forces `G ≠ 0` on the leaf row, and `t = 2m`, `ε = -U(t)` on the bare
row.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

/-! ### Abstract counting -/

theorem encard_affine_le_two (u w θ : ℝ) (hw : w ≠ 0) :
    {Λ : ℤ | u + Λ * w = θ ∨ u + Λ * w = -θ}.encard ≤ 2 := by
  have hinj : Set.InjOn (fun Λ : ℤ => u + (Λ : ℝ) * w)
      {Λ : ℤ | u + Λ * w = θ ∨ u + Λ * w = -θ} :=
    (SwitchingRow.affine_injective u w hw).injOn
  rw [← hinj.encard_image]
  calc _ ≤ ({θ, -θ} : Set ℝ).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨Λ, hΛ, rfl⟩
        rcases hΛ with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.2 h)
    _ ≤ ({-θ} : Set ℝ).encard + 1 := Set.encard_insert_le _ _
    _ = 2 := by rw [Set.encard_singleton]; rfl

theorem encard_sol_le_one (w u : ℝ) (hw : ∀ q : ℚ, (q : ℝ) ≠ w) :
    {p : ℤ × ℤ | (p.1 : ℝ) + p.2 * w = u}.encard ≤ 1 :=
  Set.encard_le_one_iff_subsingleton.2
    (SwitchingThmH.sol_subsingleton w u (SwitchingThmH.indep_of_irrational w hw))

theorem encard_pm_image_le {α : Type*} (S1 S2 : Set α) (P : Set (ℤ × α))
    (hP : ∀ p ∈ P, (p.1 = 1 ∧ p.2 ∈ S1) ∨ (p.1 = -1 ∧ p.2 ∈ S2)) :
    P.encard ≤ S1.encard + S2.encard := by
  calc P.encard ≤ ((fun x => ((1 : ℤ), x)) '' S1 ∪ (fun x => ((-1 : ℤ), x)) '' S2).encard := by
        refine Set.encard_le_encard (fun p hp => ?_)
        rcases hP p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨p.2, h2, by rw [← h1]⟩
        · exact Or.inr ⟨p.2, h2, by rw [← h1]⟩
    _ ≤ ((fun x => ((1 : ℤ), x)) '' S1).encard + ((fun x => ((-1 : ℤ), x)) '' S2).encard :=
        Set.encard_union_le _ _
    _ ≤ S1.encard + S2.encard := add_le_add (Set.encard_image_le _ _) (Set.encard_image_le _ _)

theorem mem_pm_iff {ε : ℤ} : ε ∈ ({1, -1} : Set ℤ) ↔ ε = 1 ∨ ε = -1 := by
  simp

variable {k : ℕ} (a : Fin k → ℕ)

/-! ### Failing at a pair -/

/-- A switching fails at the non-even pair of `f` iff `G(θ₀) = 0` or `G(-θ₀) = 0`, for any
root `θ₀` of `f` (Lemma 3.3(b), (e)). -/
theorem failsAtPair_iff (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k) (s : TV a → ℝ)
    (hsw : IsSwitching s) (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f)
    (θ0 : ℝ) (hθ0 : θ0 ∈ f.rootSet ℝ) :
    FailsAtPair a s f ↔ Gs a s θ0 = 0 ∨ Gs a s (-θ0) = 0 := by
  have hmf : IsOrbitFactor (branchMS a) (mirror f) := (h3b k a hk f hf hne).1
  have hθ0' : -θ0 ∈ (mirror f).rootSet ℝ := (mem_rootSet_mirror (-θ0)).2 (by rwa [neg_neg])
  constructor
  · rintro ⟨θ, hθ, hG⟩
    rcases hθ with hθ | hθ
    · exact Or.inl (h3e k a hk s hsw f hf θ hθ θ0 hθ0 hG)
    · exact Or.inr (h3e k a hk s hsw (mirror f) hmf θ hθ (-θ0) hθ0' hG)
  · rintro (hG | hG)
    · exact ⟨θ0, Or.inl hθ0, hG⟩
    · exact ⟨-θ0, Or.inr hθ0', hG⟩

theorem not_failsAtPair_of_empty (f : ℚ[X]) (h : ∀ θ, θ ∉ f.rootSet ℝ) (s : TV a → ℝ) :
    ¬ FailsAtPair a s f := by
  rintro ⟨θ, hθ, -⟩
  rcases hθ with hθ | hθ
  · exact h θ hθ
  · exact h (-θ) ((mem_rootSet_mirror θ).1 hθ)

theorem aeval_of_mem_rootSet {f : ℚ[X]} {θ : ℝ} (hθ : θ ∈ f.rootSet ℝ) : aeval θ f = 0 :=
  aeval_eq_zero_of_mem_rootSet hθ

/-- For an irrational pair, `t₀ = θ₀²` is not rational (Lemma 3.3(b)). -/
theorem sq_irrational (h3b : Lemma_3_3_b) (hk : 0 < k) (f : ℚ[X])
    (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f) (hdeg : f.natDegree ≠ 1)
    (θ0 : ℝ) (hθ0 : θ0 ∈ f.rootSet ℝ) : ∀ q : ℚ, (q : ℝ) ≠ θ0 ^ 2 := by
  intro q hq
  apply (h3b k a hk f hf hne).2.2.2 θ0 (aeval_of_mem_rootSet hθ0) |>.2.2 hdeg
  exact ⟨q, by rw [← hq]; rfl⟩

/-! ### The leaf row -/

section Leaf

variable (β : ℕ) (hβ : β ∈ Bset (branchMS a)) (hβ1 : 1 ≤ β)
include hβ hβ1

/-- No member of the leaf row fails at an even orbit (Lemma 3.3(a)). -/
theorem leaf_not_failsAtOrbit (h3a : Lemma_3_3_a) (hk : 0 < k) (ε Λ : ℤ) (s : TV a → ℝ)
    (hs : IsLeafRowMember a β ε Λ s) (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f)
    (hev : IsEvenPoly f) : ¬ FailsAtOrbit a s f := by
  rintro ⟨θ, hθf, hG⟩
  have hsec := isSecular_of_mem_rootSet _ hf hθf
  rw [Gs_leaf a β hβ hβ1 ε Λ s hs θ hsec] at hG
  apply (h3a k a hk f hf).2 θ (aeval_of_mem_rootSet hθf) hev
  have hθ : θ = -((ε : ℝ) + Ubeta a β (θ ^ 2) + (Λ : ℝ) / (θ ^ 2 - β)) := by linarith
  have hmem : -((ε : ℝ) + Ubeta a β (θ ^ 2) + (Λ : ℝ) / (θ ^ 2 - β)) ∈ QAdj (θ ^ 2) :=
    neg_mem (add_mem (add_mem (intCast_mem_QAdj _ ε) (Ubeta_mem a β _))
      (div_mem (intCast_mem_QAdj _ Λ) (sub_mem (self_mem_QAdj _) (natCast_mem_QAdj _ β))))
  rw [← hθ] at hmem
  exact hmem

/-- For a member of the leaf row, failing at a non-even pair is an affine condition on `Λ`. -/
theorem leaf_fails_iff (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k) (ε Λ : ℤ)
    (s : TV a → ℝ) (hs : IsLeafRowMember a β ε Λ s) (f : ℚ[X])
    (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f) (θ0 : ℝ)
    (hθ0 : θ0 ∈ f.rootSet ℝ) :
    FailsAtPair a s f ↔
      ((ε : ℝ) + Ubeta a β (θ0 ^ 2)) + (Λ : ℝ) * (1 / (θ0 ^ 2 - β)) = θ0 ∨
      ((ε : ℝ) + Ubeta a β (θ0 ^ 2)) + (Λ : ℝ) * (1 / (θ0 ^ 2 - β)) = -θ0 := by
  have hsec := isSecular_of_mem_rootSet _ hf hθ0
  have hsec' : IsSecular (branchMS a) (-θ0) := by
    unfold IsSecular at hsec ⊢
    rwa [neg_sq]
  rw [failsAtPair_iff a h3b h3e hk s hs.1 f hf hne θ0 hθ0, Gs_leaf a β hβ hβ1 ε Λ s hs θ0 hsec,
    Gs_leaf a β hβ hβ1 ε Λ s hs (-θ0) hsec', neg_sq]
  constructor
  · rintro (h | h)
    · right; rw [← div_eq_mul_one_div]; linarith
    · left; rw [← div_eq_mul_one_div]; linarith
  · rintro (h | h)
    · right; rw [← div_eq_mul_one_div] at h; linarith
    · left; rw [← div_eq_mul_one_div] at h; linarith

theorem leaf_count_eps (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℤ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
      IsLeafRowMember a β ε Λ (mem ε Λ))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f)
    (ε : ℤ) (hε : ε ∈ ({1, -1} : Set ℤ)) :
    {Λ : ℤ | Λ ∈ Lset β (kb (branchMS a) β) ∧ FailsAtPair a (mem ε Λ) f}.encard ≤ 2 := by
  by_cases hroot : ∃ θ0, θ0 ∈ f.rootSet ℝ
  · obtain ⟨θ0, hθ0⟩ := hroot
    have hsec := isSecular_of_mem_rootSet _ hf hθ0
    have hw : 1 / (θ0 ^ 2 - (β : ℝ)) ≠ 0 :=
      one_div_ne_zero (sub_ne_zero.2 (sq_ne_of_isSecular _ hsec β hβ))
    refine le_trans (Set.encard_le_encard ?_)
      (encard_affine_le_two ((ε : ℝ) + Ubeta a β (θ0 ^ 2)) _ θ0 hw)
    rintro Λ ⟨hΛ, hfail⟩
    exact (leaf_fails_iff a β hβ hβ1 h3b h3e hk ε Λ _ (hmem ε hε Λ hΛ) f hf hne θ0 hθ0).1 hfail
  · push Not at hroot
    have : {Λ : ℤ | Λ ∈ Lset β (kb (branchMS a) β) ∧ FailsAtPair a (mem ε Λ) f} = ∅ := by
      ext Λ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ => not_failsAtPair_of_empty a f hroot _
    rw [this, Set.encard_empty]
    exact zero_le

theorem leaf_count_total (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℤ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
      IsLeafRowMember a β ε Λ (mem ε Λ))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f) :
    {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset β (kb (branchMS a) β) ∧
      FailsAtPair a (mem p.1 p.2) f}.encard ≤ 4 := by
  have h1 := leaf_count_eps a β hβ hβ1 h3b h3e hk mem hmem f hf hne 1 (by simp)
  have h2 := leaf_count_eps a β hβ hβ1 h3b h3e hk mem hmem f hf hne (-1) (by simp)
  refine le_trans (encard_pm_image_le _ _ _ ?_) (le_trans (add_le_add h1 h2) (by norm_num))
  rintro ⟨ε, Λ⟩ ⟨hε, hΛ, hfail⟩
  rcases (mem_pm_iff.1 hε) with h | h
  · subst h
    exact Or.inl ⟨rfl, hΛ, hfail⟩
  · subst h
    exact Or.inr ⟨rfl, hΛ, hfail⟩

theorem leaf_count_irr (h3b : Lemma_3_3_b) (h3e : Lemma_3_3_e) (hk : 0 < k)
    (mem : ℤ → ℤ → TV a → ℝ)
    (hmem : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
      IsLeafRowMember a β ε Λ (mem ε Λ))
    (f : ℚ[X]) (hf : IsOrbitFactor (branchMS a) f) (hne : ¬ IsEvenPoly f)
    (hdeg : f.natDegree ≠ 1) :
    {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset β (kb (branchMS a) β) ∧
      FailsAtPair a (mem p.1 p.2) f}.encard ≤ 2 := by
  by_cases hroot : ∃ θ0, θ0 ∈ f.rootSet ℝ
  · obtain ⟨θ0, hθ0⟩ := hroot
    have hsec := isSecular_of_mem_rootSet _ hf hθ0
    have ht := sq_irrational a h3b hk f hf hne hdeg θ0 hθ0
    have htβ : θ0 ^ 2 - (β : ℝ) ≠ 0 := sub_ne_zero.2 (sq_ne_of_isSecular _ hsec β hβ)
    set w : ℝ := 1 / (θ0 ^ 2 - β) with hw
    have hwq : ∀ q : ℚ, (q : ℝ) ≠ w := by
      intro q hq
      have hq0 : (q : ℝ) ≠ 0 := by rw [hq, hw]; exact one_div_ne_zero htβ
      apply ht ((β : ℚ) + 1 / q)
      push_cast
      rw [hq, hw]
      field_simp
      ring
    set U := Ubeta a β (θ0 ^ 2)
    calc _ ≤ ({p : ℤ × ℤ | (p.1 : ℝ) + p.2 * w = θ0 - U} ∪
          {p : ℤ × ℤ | (p.1 : ℝ) + p.2 * w = -θ0 - U}).encard := by
          refine Set.encard_le_encard ?_
          rintro ⟨ε, Λ⟩ ⟨hε, hΛ, hfail⟩
          rcases (leaf_fails_iff a β hβ hβ1 h3b h3e hk ε Λ _ (hmem ε hε Λ hΛ) f hf hne θ0
            hθ0).1 hfail with h | h
          · left; show (ε : ℝ) + Λ * w = θ0 - U; linarith
          · right; show (ε : ℝ) + Λ * w = -θ0 - U; linarith
      _ ≤ _ + _ := Set.encard_union_le _ _
      _ ≤ 1 + 1 := add_le_add (encard_sol_le_one w _ hwq) (encard_sol_le_one w _ hwq)
      _ = 2 := by norm_num
  · push Not at hroot
    have : {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset β (kb (branchMS a) β) ∧
        FailsAtPair a (mem p.1 p.2) f} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ _ => not_failsAtPair_of_empty a f hroot _
    rw [this, Set.encard_empty]
    exact zero_le

end Leaf

end P8Rows
