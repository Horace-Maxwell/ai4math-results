import Research.Backfill.Paper7.C61ClassificationBounds
import Research.Backfill.Paper7.IntegerFactorWindow

/-! A smaller spectral domain for a future certificate. These bounds follow
from the actual whole spectrum and its second moment, not sample roots. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Classification
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem bplus_entry_le_six (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (x : ℝ) (hx : x ∈ Bplus (SG 6 p q)) :
    x ≤ 6 := by
  have hnonneg : ∀ y ∈ (Bplus (SG 6 p q)).map (fun z => z ^ 2), (0 : ℝ) ≤ y := by
    intro y hy
    obtain ⟨z, _hz, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg z
  have hsq : x ^ 2 ≤ S2 (SG 6 p q) :=
    Multiset.single_le_sum hnonneg (x ^ 2) (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide)
    hG (by decide)).2.1
  have hm : (0 : ℝ) ≤ mult (SG 6 p q) 1 := Nat.cast_nonneg _
  have hnR : (nOf 6 p q : ℝ) ≤ 42 := by exact_mod_cast hn
  have hxspec : x ∈ spec (SG 6 p q) := (Multiset.mem_filter.mp hx).1
  obtain ⟨z, rfl⟩ := Paper7Moments.integral_spec_entry (SG 6 p q) hG x hxspec
  by_contra h
  have hz : (6 : ℤ) < z := by exact_mod_cast (lt_of_not_ge h)
  have hz7 : (7 : ℝ) ≤ z := by exact_mod_cast (show (7 : ℤ) ≤ z by omega)
  nlinarith
#print axioms Paper7C61Classification.bplus_entry_le_six

theorem spec_abs_le_six (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (x : ℝ) (hx : x ∈ spec (SG 6 p q)) :
    |x| ≤ 6 := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide)
    hG (by decide)).1
  have hupper (y : ℝ) (hy : y ∈ spec (SG 6 p q)) : y ≤ 6 := by
    by_cases h2 : 2 ≤ y
    · exact bplus_entry_le_six p q hn hG y (Multiset.mem_filter.mpr ⟨hy, h2⟩)
    · linarith
  have hneg : -x ∈ spec (SG 6 p q) := by
    have hm : 0 < mult (SG 6 p q) x := Multiset.count_pos.mpr hx
    rw [hs x] at hm
    exact Multiset.count_pos.mp hm
  exact abs_le.mpr ⟨by have := hupper (-x) hneg; linarith, hupper x hx⟩
#print axioms Paper7C61Classification.spec_abs_le_six

theorem graphPhi_integer_window_six (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    IntegerFactorizationOn (graphPhi (SG 6 p q)) (integerWindow 6) := by
  obtain ⟨_S, hfactor⟩ :=
    (Paper7Spectrum.integral_iff_integerFactorization (SG 6 p q)).mp hG
  have hs : (graphPhi (SG 6 p q)).Splits :=
    (Paper7SpectralWindow.integerFactorizationOn_splits_roots hfactor).1
  have hm : (graphPhi (SG 6 p q)).Monic := Matrix.charpoly_monic _
  apply Paper7SpectralWindow.integerFactorizationOn_of_splits hm hs
  intro z hz
  have hroot : Polynomial.IsRoot
      ((graphPhi (SG 6 p q)).map (Int.castRingHom ℝ)) (z : ℝ) :=
    (Polynomial.isRoot_of_mem_roots hz).map
  rw [Paper7Spectrum.graphPhi_map (SG 6 p q) ℝ] at hroot
  have hspec : (z : ℝ) ∈ spec (SG 6 p q) :=
    (Polynomial.mem_roots ((SG 6 p q).adjMatrix ℝ).charpoly_monic.ne_zero).mpr hroot
  have habs := spec_abs_le_six p q hn hG (z : ℝ) hspec
  change z ∈ Finset.Icc (-(6 : ℤ)) (6 : ℤ)
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp habs).1
  · exact_mod_cast (abs_le.mp habs).2
#print axioms Paper7C61Classification.graphPhi_integer_window_six

end Paper7C61Classification
