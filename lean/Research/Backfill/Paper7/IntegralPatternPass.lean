import Research.Backfill.Paper7.SpectralWindowPass
import Research.Backfill.Paper7.Lemma44
import Research.Backfill.Paper7.LegacyEnumeration

/-! Source-only: both original support cases and all rank/refined switches.
Negative r0-4 is handled by the already proved exact rank bound, not truncated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningSpectrum

theorem patternPass_integral (rank refined : Bool) (b N : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    PatternPass rank refined b N x := by
  have hn : (nOf b x.1 x.2 : ℤ) ≤ N := by
    exact_mod_cast (show nOf b x.1 x.2 ≤ N by rw [nOf_eq_b_weight]; exact hx.2)
  dsimp only [PatternPass]
  by_cases hzero : (Kq b x.2).card = 0
  · have hK : Kq b x.2 = ∅ := Finset.card_eq_zero.mp hzero
    have h := Paper7Rank.rank_sigma_empty b x.1 x.2 hb hG hK
    simp only [ite_eq_left hzero]
    constructor <;> intro _ <;> omega
  · have hK : (Kq b x.2).Nonempty := Finset.card_pos.mp (by omega)
    have h := Paper7Rank.rank_sigma_nonempty b x.1 x.2 hb hG hK
    simp only [ite_eq_right hzero, sub_zero]
    constructor <;> intro _ <;> omega
#print axioms Paper7PruningGuards.patternPass_integral

end Paper7PruningGuards
