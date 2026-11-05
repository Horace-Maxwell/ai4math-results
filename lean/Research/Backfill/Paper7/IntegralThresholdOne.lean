import Research.Backfill.Paper7.CycleInterlacing
import Research.Backfill.Paper7.SpectralMoments

/-! Exact real-root filters from the original complex-spectrum integrality
predicate. Multiplicities are retained. No non-cycle premise is needed here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Lemma41
open BackfillPaper7.Challenge Paper7Moments

variable {V : Type} [Fintype V] [DecidableEq V]

theorem integral_gt_one_iff_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsIntegralGraph G) (x : ℝ) (hx : x ∈ spec G) : 1 < x ↔ 2 ≤ x := by
  obtain ⟨z, rfl⟩ := integral_spec_entry G hG x hx
  constructor
  · intro hz
    have hz' : (1 : ℤ) < z := by exact_mod_cast hz
    have hz'' : (2 : ℤ) ≤ z := by omega
    exact_mod_cast hz''
  · intro hz
    linarith
#print axioms Paper7Lemma41.integral_gt_one_iff_ge_two

theorem integral_filter_gt_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsIntegralGraph G) :
    (spec G).filter (fun x => 1 < x) = Bplus G := by
  apply Multiset.filter_congr
  intro x hx
  exact integral_gt_one_iff_ge_two G hG x hx
#print axioms Paper7Lemma41.integral_filter_gt_one

theorem integral_Ngt_one_eq_Bplus_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsIntegralGraph G) : Ngt G 1 = (Bplus G).card := by
  exact congrArg Multiset.card (integral_filter_gt_one G hG)
#print axioms Paper7Lemma41.integral_Ngt_one_eq_Bplus_card

/-- Full cycle-to-Bplus bound; the explicit numerical cycle count is not assumed. -/
theorem cycle_count_le_integral_Bplus (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    Ngt (SimpleGraph.cycleGraph b) 1 ≤ (Bplus (SG b p q)).card := by
  rw [← integral_Ngt_one_eq_Bplus_card (SG b p q) hG]
  exact (lemma41_interlacing b p q hb).1
#print axioms Paper7Lemma41.cycle_count_le_integral_Bplus

end Paper7Lemma41
