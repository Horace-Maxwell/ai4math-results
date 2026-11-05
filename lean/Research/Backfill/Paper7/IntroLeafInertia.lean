import Research.Backfill.Paper7.IntroLeafDegreeMass
import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.IntroEvenSpectralAlternatives

/-! The actual independent leaf set bounds positive inertia. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroFour
open Matrix BackfillPaper7.Challenge Paper7OddIntegral Paper7IntroOddMultiplicity

theorem unicyclic_positive_inertia_add_leaves_le_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) :
    nPos (G.adjMatrix ℝ) + (leafVerts G).card ≤ Fintype.card V := by
  let I : Type := {v : V // G.degree v = 1}
  have hzero : (G.adjMatrix ℝ).submatrix (fun v : I => v.val) (fun v : I => v.val) = 0 := by
    apply Matrix.ext
    intro i j
    have hnot := unicyclic_leaves_independent G b hG i.val j.val i.property j.property
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
      ite_eq_right hnot, Matrix.zero_apply]
  have hbound := (Paper7Comparison.principal_negative_inertia_bounds
    (G.adjMatrix ℝ) (Paper7Spectrum.realAdjHermitian G)
    (fun v : I => v.val) Subtype.val_injective).2
  rw [hzero] at hbound
  have hzpos : nPos (0 : Matrix I I ℝ) = 0 := by
    simpa using (Paper7Inertia.inertia_diagonal (fun _ : I => (0 : ℝ))).1
  have hzsum := Paper7Comparison.inertia_total (0 : Matrix I I ℝ) Matrix.isHermitian_zero
  have hsum := Paper7Comparison.inertia_total (G.adjMatrix ℝ)
    (Paper7Spectrum.realAdjHermitian G)
  have hcard : Fintype.card I = (leafVerts G).card := by
    change Fintype.card {v : V // G.degree v = 1} = (leafVerts G).card
    simpa only [leafVerts] using Fintype.card_subtype (fun v : V => G.degree v = 1)
  omega
#print axioms Paper7IntroFour.unicyclic_positive_inertia_add_leaves_le_card

theorem intro21_positive_inertia_actual_counts
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    nPos (G.adjMatrix ℝ) = (integerSpectrum G).count 1 + (integerSpectrum G).count 2 +
      (integerSpectrum G).count 3 + (integerSpectrum G).count 4 := by
  have hcover : ∀ z ∈ (integerSpectrum G).filter (fun z : ℤ => 0 < (z : ℝ)),
      ∃ i : Fin 9, integerWindowValue i = z := by
    intro z hz
    exact intro21_integerSpectrum_cover G b hG hI hn z (Multiset.mem_filter.mp hz).1
  have h := Paper7PruningSpectrum.finite_count_card
    ((integerSpectrum G).filter (fun z : ℤ => 0 < (z : ℝ)))
    integerWindowValue integerWindowValue_injective hcover
  norm_num [Fin.sum_univ_succ, integerWindowValue, Multiset.count_filter] at h
  have hcard : nPos (G.adjMatrix ℝ) =
      ((integerSpectrum G).filter (fun z : ℤ => 0 < (z : ℝ))).card := by
    change ((spec G).filter (fun x : ℝ => 0 < x)).card = _
    simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_apply] using
      congrArg (fun s : Multiset ℝ => (s.filter (fun x => 0 < x)).card)
        (integerSpectrum_cast G hI).symm
  rw [hcard]
  simpa only [add_assoc, Int.cast_pos] using h
#print axioms Paper7IntroFour.intro21_positive_inertia_actual_counts

end Paper7IntroFour
