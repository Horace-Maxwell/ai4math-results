import Research.Backfill.Paper7.IntegralPrefixGuards
import Research.Backfill.Paper7.IntegralPatternPass
import Research.Backfill.Paper7.VersionCanonicalGuards

/-! Source-only: every original Stage branch on an already chosen actual
integral representative. Prefix guards are proved on that representative,
not transported as relabeling invariants. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningCanonical

theorem stage_integral_of_guards (v : SearchVersion) (b N : ℕ)
    (hb : 3 ≤ b) (hN : N ≤ 49) (x : PQ b) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) (hc : VersionCanonicalGuards v b x) :
    Stage v b N x := by
  cases v with
  | a4 => exact aReaches_integral false false b N x hb hN hx hG hc
  | a5 => exact aReaches_integral true false b N x hb hN hx hG hc
  | a6 c => exact aReaches_integral true c b N x hb hN hx hG hc
  | b1 => exact ⟨⟨hx, momentPass_integral false true false b N x hb hN hx hG⟩, hc⟩
  | b2 =>
    exact ⟨bReaches_integral true false true false b N x hb hN hx hG
      (by intro h; cases h), hc⟩
  | b3 =>
    exact ⟨bReaches_integral true true true true b N x hb hN hx hG
      (fun _ => hc.2), hc.1⟩
  | c r => exact ⟨hx, patternPass_integral r false b N x hb hx hG, hc⟩
  | c2 r rr => exact ⟨hx, patternPass_integral r rr b N x hb hx hG, hc⟩
  | d1 c =>
    exact dStage_integral false false c false false b N x hb hN hx hG hc
      (by intro h; cases h)
  | d2 c l w => exact dStage_integral true l c w false b N x hb hN hx hG hc.1 hc.2
  | d3 c l w np => exact dStage_integral true l c w np b N x hb hN hx hG hc.1 hc.2
#print axioms Paper7PruningGuards.stage_integral_of_guards

end Paper7PruningGuards
