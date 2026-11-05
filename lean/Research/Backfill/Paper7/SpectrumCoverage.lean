import Research.Backfill.Paper7.SpectrumGraphBasics

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Spectrum

open BackfillPaper7.Challenge

theorem sum_mult_of_integer_cover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset ℤ)
    (hS : ∀ x ∈ spec G, ∃ m ∈ S, x = (m : ℝ)) :
    ∑ m ∈ S, mult G (m : ℝ) = Fintype.card V := by
  classical
  have hcover : ∀ x ∈ spec G, x ∈ S.image (fun m : ℤ => (m : ℝ)) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hS x hx
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  calc
    (∑ m ∈ S, mult G (m : ℝ)) =
        ∑ x ∈ S.image (fun m : ℤ => (m : ℝ)), (spec G).count x := by
      unfold mult
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact Int.cast_injective hab
    _ = (spec G).card := Multiset.sum_count_eq_card hcover
    _ = Fintype.card V := spec_card G

#print axioms Paper7Spectrum.sum_mult_of_integer_cover

end Paper7Spectrum
