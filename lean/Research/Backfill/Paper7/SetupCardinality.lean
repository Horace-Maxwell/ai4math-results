import Research.Backfill.Paper7.SunEdgeCount

set_option autoImplicit false

namespace Paper7Setup

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem sg_order (b : ℕ) (p q : Fin b → ℕ) :
    order b (pq b p q) = nOf b p q := by
  change Fintype.card (SunV b (pq b p q)) = _
  rw [Paper7Cleared.card_sun_pq]
  rfl

#print axioms Paper7Setup.sg_order

theorem sg_edges (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    (SG b p q).edgeFinset.card = nOf b p q :=
  Paper7SunMoments.sg_edge_card b p q hb

#print axioms Paper7Setup.sg_edges

end Paper7Setup
