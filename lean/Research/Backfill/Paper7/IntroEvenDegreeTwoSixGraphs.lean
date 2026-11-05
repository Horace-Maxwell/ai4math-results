import Research.Backfill.Paper7.UnicyclicSunAssembly
import Research.Backfill.Paper7.MainTheoremTwo
import Research.Backfill.Paper7.BareCycleIntegralClassification
import Research.Backfill.Paper7.DihedralBudgetIntegral

/-! Conditional assembly helper only. The outside-degree condition is explicit
here and is not added to the frozen IntroUnicyclic21 statement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroDegreeTwoClassification
open SimpleGraph BackfillPaper7.Challenge

theorem intro21_even_off_cycle_degree_two_six_graphs
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hdeg : ∀ v, v ∉ w.support → G.degree v ≤ 2) :
    Nonempty (G ≃g cycleGraph 3) ∨
      Nonempty (G ≃g cycleGraph 4) ∨
      Nonempty (G ≃g cycleGraph 6) ∨
      Nonempty (G ≃g sunGraph 4 G13) ∨
      Nonempty (G ≃g sunGraph 4 G20a) ∨
      Nonempty (G ≃g sunGraph 4 G20b) := by
  obtain ⟨L, ⟨e⟩, _hpositive_lengths⟩ :=
    Paper7SunAssembly.unicyclic_off_cycle_degree_two_sun_iso
      G b hG r w hw hlen hdeg
  have hcard : Fintype.card V = order b L := Fintype.card_congr e.toEquiv
  have hbound : order b L ≤ 41 := by omega
  have hb3 : 3 ≤ b := Paper7Unicyclic.unicyclic_three_le hG
  have hISun : IsIntegralGraph (sunGraph b L) :=
    (Paper7PruningCanonical.integral_graphIso_iff G (sunGraph b L) e).mpr hI
  by_cases hp : 0 < pendantCount b L
  · obtain ⟨_hb4, hclass⟩ := Paper7Main.check_Theorem2 b L hb3 hp hISun hbound
    rcases hclass with h13 | h20a | h20b
    · obtain ⟨e13⟩ := h13
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e13⟩)))
    · obtain ⟨e20a⟩ := h20a
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e20a⟩))))
    · obtain ⟨e20b⟩ := h20b
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e20b⟩))))
  · have hpzero : pendantCount b L = 0 := Nat.eq_zero_of_not_pos hp
    have hcardb : Fintype.card V = b := by
      calc
        Fintype.card V = order b L := hcard
        _ = b + pendantCount b L := Paper7CycleThree.order_eq_add_pendantCount b L
        _ = b := by rw [hpzero, Nat.add_zero]
    obtain ⟨ec⟩ := Paper7UnicyclicStructure.unicyclic_card_eq_cycle_iso G b hG hcardb
    have hIcycle : IsIntegralGraph (cycleGraph b) :=
      (Paper7PruningCanonical.integral_graphIso_iff G (cycleGraph b) ec).mpr hI
    rcases (Paper7BareCycle.cycleGraph_integral_iff b hb3).mp hIcycle with h3 | h4 | h6
    · rw [h3] at hb
      norm_num at hb
    · have ec4 : G ≃g cycleGraph 4 :=
        Eq.mp (congrArg (fun k : ℕ => G ≃g cycleGraph k) h4) ec
      exact Or.inr (Or.inl ⟨ec4⟩)
    · have ec6 : G ≃g cycleGraph 6 :=
        Eq.mp (congrArg (fun k : ℕ => G ≃g cycleGraph k) h6) ec
      exact Or.inr (Or.inr (Or.inl ⟨ec6⟩))
#print axioms Paper7IntroDegreeTwoClassification.intro21_even_off_cycle_degree_two_six_graphs

end Paper7IntroDegreeTwoClassification
