import Research.Backfill.Paper7.MainTheoremsOne
import Research.Backfill.Paper7.EightCompleteExclusion
import Research.Backfill.Paper7.ControlB4N49Complete
import Research.Backfill.Paper7.ControlC42Ten

/-! Source-only candidate for the exact frozen Theorem2. The complete B4
module remains pending; its future successful producer must be bound by Root.
This candidate adds no parameter, spectrum, finite-table or CRT premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Main
open BackfillPaper7.Challenge

theorem order_forty_one_excludes_control (L : Fin 4 → List ℕ)
    (hn : order 4 L ≤ 41) : ¬ Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten) := by
  rintro ⟨e⟩
  have hc := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 C42Ten at hc
  rw [Paper7Control44.control_order] at hc
  omega
#print axioms Paper7Main.order_forty_one_excludes_control

theorem check_Theorem2 : BackfillPaper7.Challenge.Theorem2 := by
  intro b L hb hp hG hn
  rcases remaining_cycles_order_forty_one b L hb hp hG hn with h4|h8
  · subst b
    refine ⟨rfl,?_⟩
    rcases (Paper7ControlB4.check_ControlB4N49 L hp (by omega)).mp hG with
      h13|h20a|h20b|h44
    · exact Or.inl h13
    · exact Or.inr (Or.inl h20a)
    · exact Or.inr (Or.inr h20b)
    · exact (order_forty_one_excludes_control L hn h44).elim
  · subst b
    exact (Paper7EightCycle.original_eight_nonintegral L hp hn hG).elim
#print axioms Paper7Main.check_Theorem2

end Paper7Main
