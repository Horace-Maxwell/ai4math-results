import Research.Backfill.Paper7.SigmaSqCubic
import Research.Backfill.Paper7.RealCubeRootBound
import Research.Backfill.Paper7.Lemma44

/-! Both original frozen bounds; no restriction on the small b/t cases. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Section6
open BackfillPaper7.Challenge Paper7Rank

theorem section6_natural_threshold (b r n : ℕ) (hbr : b ≤ r+4)
    (hs : sigmaSq (r : ℤ) ≤ 2*n) :
    ∀ t : ℕ, 2*n < sigmaSq (t : ℤ) → b < t+4 := by
  intro t ht
  by_contra h
  have htr : (t : ℤ) ≤ (r : ℤ) := by
    exact_mod_cast (show t ≤ r by omega)
  have hm := sigmaSq_monotone htr
  omega
#print axioms Paper7Section6.section6_natural_threshold

theorem section6_real_cube_bound (b r n : ℕ) (hbr : b ≤ r+4)
    (hs : sigmaSq (r : ℤ) ≤ 2*n) :
    (b : ℝ) ≤ (96*(n : ℝ))^((1 : ℝ)/3)+7 := by
  have hc : (((4*(r/4) : ℕ) : ℝ))^3 ≤ 96*(n : ℝ) := by
    exact_mod_cast sigmaSq_rank_cube_budget r n hs
  have hroot := le_cube_root_of_cube_le (((4*(r/4) : ℕ) : ℝ))
    (96*(n : ℝ)) (Nat.cast_nonneg _) hc
  have hb : b ≤ 4*(r/4)+7 := by omega
  have hbR : (b : ℝ) ≤ ((4*(r/4) : ℕ) : ℝ)+7 := by exact_mod_cast hb
  linarith
#print axioms Paper7Section6.section6_real_cube_bound

theorem check_Section6Bound : BackfillPaper7.Challenge.Section6Bound := by
  intro b p q hb hpos hG
  have h := Paper7Rank.check_Lemma44 b p q hb hpos hG
  let r : ℕ := (bigEigs (SG b p q)).card
  have hr : (b : ℤ)-4 ≤ (r : ℤ) := h.2.1
  have hsZ : (sigmaSq (r : ℤ) : ℤ) ≤ 2*(nOf b p q : ℤ) := h.2.2.1
  have hbr : b ≤ r+4 := by omega
  have hs : sigmaSq (r : ℤ) ≤ 2*nOf b p q := by exact_mod_cast hsZ
  exact ⟨section6_natural_threshold b r (nOf b p q) hbr hs,
    section6_real_cube_bound b r (nOf b p q) hbr hs⟩
#print axioms Paper7Section6.check_Section6Bound

end Paper7Section6
