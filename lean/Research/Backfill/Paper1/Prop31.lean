import Research.Backfill.Paper1.Prop31ShortChains

/-!
Complete static proof source for the frozen Proposition31.
The public declaration has exactly Challenge.Proposition31; no substitute
condition or unproved auxiliary hypothesis is an argument of the theorem.
Compilation, axiom audit, checker and fresh replay have NOT yet been run.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31

lemma last_not_pmAlt {a : ℕ} {g : ℕ → ℝ} (hga : g a = -1)
    (hna : ¬ ∀ i ≤ a, g i = -((-1) ^ a * Challenge.sAlt i)) :
    ¬ Challenge.IsPmAlt a g := by
  intro halt
  apply hna
  rcases halt with h | h
  · have ha : Challenge.sAlt a = -1 := (h a le_rfl).symm.trans hga
    intro i hi
    rw [h i hi]
    change Challenge.sAlt i = -(Challenge.sAlt a * Challenge.sAlt i)
    rw [ha]
    ring
  · have ha : Challenge.sAlt a = 1 := by have hh := h a le_rfl; rw [hga] at hh; linarith
    intro i hi
    rw [h i hi]
    change -Challenge.sAlt i = -(Challenge.sAlt a * Challenge.sAlt i)
    rw [ha, one_mul]

lemma last_other_strict {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) (hpar : b % 2 = a % 2)
    {p q Pm : ℝ} (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) (hC : Challenge.CondC a p q)
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y) (hcorner : Y a b = -1)
    (hanti : ¬ ∀ i ≤ a, Y i b = -((-1) ^ a * Challenge.sAlt i))
    (hplus : ¬ ∀ i ≤ a, Y i b = Challenge.gPlus a i) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  let g := Challenge.col Y b
  have hg : Challenge.IsSignVec a g := fun i hi => hY i hi b le_rfl
  have hga : g a = -1 := hcorner
  have hlast : ∀ i ≤ a, Y i b = g i := by intros; rfl
  have hp := (OneColumn.region_bounds hreg).1
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hΔ : 0 < Challenge.DeltaC a p g := delta_pos hp hg (last_not_pmAlt hga hanti)
  obtain hlarge | hsmall := hC g hg hga hanti hplus
  · apply strict_of_surplus hq a b p Y
    have hsum : 0 ≤ ∑ j ∈ range b, Challenge.psiCol a b p q Y j := by
      apply Finset.sum_nonneg
      intro j hj
      exact (psiCol_nonneg ha hreg hPm hS hY (Finset.mem_range.mp hj)).1
    have hρ : 0 < Challenge.mu q ((b : ℤ) - 1) := by
      rw [Additional.mu_pred_eq_nu]; exact nu_pos hq b
    have hm : q * Challenge.mu q ((b : ℤ) - 1) *
        (2 * Challenge.deltaK a p - Challenge.DeltaC a p g) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) hρ) (by linarith)
    exact hm.trans_le hsum
  · obtain ⟨k, hk, hchain, hbreak⟩ := longest_chain a b Y g
    rcases hsmall with ⟨hC1, hC2, hC3⟩
    rcases chain_cases hk with ⟨hkb, hk4⟩ | ⟨hk5, hkb⟩ | hkb
    · exact C1_strict ha hb hab hpar hreg hPm hS hY hg hkb hk4 hlast hchain
        (hbreak hkb) hC1
    · exact C2_strict ha hb hab hpar hreg hPm hS hY hg hkb hk5 hlast hchain hC2
    · subst k
      exact whole_chain_strict ha hb hab hpar hreg hY hg hlast hchain hΔ hC3

lemma sign_conclusion {a : ℕ} (ha : 2 ≤ a) {p q Pm : ℝ}
    (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hall : Challenge.CondAll a p q Pm) : Challenge.SignConclusion a p q := by
  intro b hb hpar Y hY hcorner
  have hab : Even (a + b) := by rw [Nat.even_iff]; omega
  have hp := (OneColumn.region_bounds hreg).1
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  obtain ⟨hS, hF, hC⟩ := hall
  have hminusValue : Challenge.MatEq a b Y Challenge.Yminus →
      Challenge.Gval a b p q Y = Challenge.Theta a b p q := by
    intro he
    rw [Gval_congr a b p q he]
    exact minus_value hp hq a b
  have hplusValue : Challenge.MatEq a b Y (Challenge.Yplus a b) →
      Challenge.Gval a b p q Y = Challenge.Theta a b p q := by
    intro he
    rw [Gval_congr a b p q he]
    exact GeneralEquality.plus_value hreg ha hb hab
  have hmain : Challenge.Gval a b p q Y ≤ Challenge.Theta a b p q ∧
      (Challenge.Gval a b p q Y = Challenge.Theta a b p q →
        Challenge.MatEq a b Y Challenge.Yminus ∨ Challenge.MatEq a b Y (Challenge.Yplus a b)) := by
    by_cases hminus : Challenge.MatEq a b Y Challenge.Yminus
    · exact ⟨(hminusValue hminus).le, fun _ => Or.inl hminus⟩
    · obtain ⟨J, hJb, hdev, htail⟩ := largest_deviation hminus
      by_cases hJ : J < b
      · have hs := first_deviation ha hb hab hpar hreg hPm hS hF hY hJ hdev htail
        exact ⟨hs.le, fun he => False.elim (hs.ne he)⟩
      · have hJ : J = b := by omega
        subst J
        have hanti : ¬ ∀ i ≤ a, Y i b = -((-1) ^ a * Challenge.sAlt i) := by
          intro h
          apply hdev
          intro i hi
          rw [h i hi]
          have hsign := GeneralEquality.even_sum_sign hab
          change (-1 : ℝ) ^ a = (-1) ^ b at hsign
          unfold Challenge.Yminus Challenge.sAlt
          rw [hsign]
          ring
        by_cases hplus : ∀ i ≤ a, Y i b = Challenge.gPlus a i
        · have hh := plus_case ha hb hab hreg hPm hS hY hplus
          exact ⟨hh.1, fun he => Or.inr (hh.2.mp he)⟩
        · have hs := last_other_strict ha hb hab hpar hreg hPm hS hC hY hcorner hanti hplus
          exact ⟨hs.le, fun he => False.elim (hs.ne he)⟩
  refine ⟨hmain.1, ⟨hmain.2, ?_⟩⟩
  rintro (he | he)
  · exact hminusValue he
  · exact hplusValue he

end Prop31

theorem check_Proposition31 : Challenge.Proposition31 := by
  intro a ha
  constructor
  · intro hall p q hreg
    exact Prop31.sign_conclusion ha (Or.inl hreg) (by have := hreg.2; linarith)
      (hall p q hreg)
  · intro hall p q hreg
    exact Prop31.sign_conclusion ha (Or.inr hreg) (by have := hreg.2; linarith)
      (hall p q hreg)

end CodexPaper1

#print axioms CodexPaper1.check_Proposition31
