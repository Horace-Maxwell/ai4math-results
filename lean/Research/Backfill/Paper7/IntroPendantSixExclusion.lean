import Research.Backfill.Paper7.IntroIntegralDegreeTwoChain
import Research.Backfill.Paper7.IntegerSpectrum

/-! A real C6 with all outside edges incident at one cycle vertex is excluded
from every integral connected graph having an eigenvalue greater than two.
The outside graph is arbitrary; it is not required to be a Sun or a path. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroLocalQuartic
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral

theorem embedding_two_neighbors
    {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (i a b : W) (hN : ∀ j, H.Adj i j ↔ j = a ∨ j = b)
    (hout : ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x) :
    ∀ x, G.Adj (f i) x ↔ x = f a ∨ x = f b := by
  have hN' : ∀ j, H.Adj i j ↔ f j = f a ∨ f j = f b := by
    intro j
    simpa only [hf.eq_iff] using hN j
  intro x
  constructor
  · intro hx
    have hm : x ∈ Set.range f := by
      by_contra hn
      exact hout x hn hx
    obtain ⟨j, rfl⟩ := hm
    exact (hN' j).mp ((hAdj i j).mpr hx)
  · rintro (rfl | rfl)
    · exact (hAdj i a).mp ((hN a).mpr (Or.inl rfl))
    · exact (hAdj i b).mp ((hN b).mpr (Or.inr rfl))
#print axioms Paper7IntroLocalQuartic.embedding_two_neighbors

theorem integral_connected_no_pendant_six
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (f : Fin 6 → V) (hf : Function.Injective f)
    (hAdj : ∀ i j, (SimpleGraph.cycleGraph 6).Adj i j ↔ G.Adj (f i) (f j))
    (k : Fin 6)
    (hout : ∀ i, i ≠ k → ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x) : False := by
  have hindex : k + 2 ≠ k + 4 ∧ k + 3 ≠ k + 1 ∧ k + 3 ≠ k + 5 ∧
      k + 1 ≠ k + 5 ∧ k + 3 ≠ k ∧ k + 2 ≠ k ∧ k + 4 ≠ k := by
    fin_cases k <;> decide
  obtain ⟨h24, h31, h35, h15, h30, h20, h40⟩ := hindex
  have h3 : ∀ j : Fin 6, (SimpleGraph.cycleGraph 6).Adj (k + 3) j ↔
      j = k + 2 ∨ j = k + 4 := by
    intro j
    fin_cases k <;> fin_cases j <;> decide
  have h2 : ∀ j : Fin 6, (SimpleGraph.cycleGraph 6).Adj (k + 2) j ↔
      j = k + 3 ∨ j = k + 1 := by
    intro j
    fin_cases k <;> fin_cases j <;> decide
  have h4 : ∀ j : Fin 6, (SimpleGraph.cycleGraph 6).Adj (k + 4) j ↔
      j = k + 3 ∨ j = k + 5 := by
    intro j
    fin_cases k <;> fin_cases j <;> decide
  exact integral_connected_no_two_step_degree_two_chain G hG hI s hs hs2
    (f (k + 3)) (f (k + 2)) (f (k + 4)) (f (k + 1)) (f (k + 5))
    (fun h => h24 (hf h)) (fun h => h31 (hf h))
    (fun h => h35 (hf h)) (fun h => h15 (hf h))
    (embedding_two_neighbors G (SimpleGraph.cycleGraph 6) f hf hAdj
      (k + 3) (k + 2) (k + 4) h3 (hout _ h30))
    (embedding_two_neighbors G (SimpleGraph.cycleGraph 6) f hf hAdj
      (k + 2) (k + 3) (k + 1) h2 (hout _ h20))
    (embedding_two_neighbors G (SimpleGraph.cycleGraph 6) f hf hAdj
      (k + 4) (k + 3) (k + 5) h4 (hout _ h40))
#print axioms Paper7IntroLocalQuartic.integral_connected_no_pendant_six

theorem integral_connected_no_single_attachment_six_side
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (S : Set V) (u : S) (e : G.induce S ≃g SimpleGraph.cycleGraph 6)
    (hboundary : ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → i = u.val) : False := by
  let f : Fin 6 → V := fun i => (e.symm i).val
  have hf : Function.Injective f := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have ha : ∀ i j, (SimpleGraph.cycleGraph 6).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    exact e.symm.map_rel_iff.symm
  have hout : ∀ i, i ≠ e u → ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x := by
    intro i hi x hx hadj
    have hxS : x ∉ S := by
      intro h
      apply hx
      exact ⟨e ⟨x, h⟩, by simp [f]⟩
    have hfi : f i = u.val := hboundary (f i) (e.symm i).property x hxS hadj
    have he : e.symm i = u := Subtype.ext hfi
    apply hi
    calc
      i = e (e.symm i) := (e.apply_symm_apply i).symm
      _ = e u := congrArg e he
  exact integral_connected_no_pendant_six G hG hI s hs hs2 f hf ha (e u) hout
#print axioms Paper7IntroLocalQuartic.integral_connected_no_single_attachment_six_side

theorem integral_radius_three_no_single_attachment_six_side
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (S : Set V) (u : S) (e : G.induce S ≃g SimpleGraph.cycleGraph 6)
    (hboundary : ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → i = u.val) : False := by
  have hm : (3 : ℤ) ∈ integerSpectrum G := Multiset.count_pos.mp (by omega)
  have hs : (3 : ℝ) ∈ spec G := by
    rw [← integerSpectrum_cast G hI]
    exact Multiset.mem_map.mpr ⟨3, hm, by norm_num⟩
  exact integral_connected_no_single_attachment_six_side G hG hI 3 hs (by norm_num)
    S u e hboundary
#print axioms Paper7IntroLocalQuartic.integral_radius_three_no_single_attachment_six_side

end Paper7IntroLocalQuartic
