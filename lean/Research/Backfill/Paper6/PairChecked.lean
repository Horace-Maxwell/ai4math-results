import Research.Backfill.Paper6.PairVenn
import Research.Backfill.Paper6.PairCertificates

set_option autoImplicit false

namespace Paper6FiveExclusion

open BackfillPaper6.V3

theorem pair_good {q : ℕ} (A B : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (hq : q ≤ 3)
    (hA : A.card = 7) (hB : B.card = 7) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.univ) (hR : ∀ i, (R i).card ≤ 7) :
    GoodWeight (hammingNorm (pairFunction A B R)) := by
  interval_cases q
  · have hc := pair_counts_complete0 all_pairs0
    rw [← actual_pair_weight0 A B R hA hB hd hu] at hc
    exact okayWeight_sound _ hc
  · have hc := pair_counts_complete1 (blockCount A R ({0} : Finset (Fin 1))) (blockCount B R ({0} : Finset (Fin 1)))
      (actual_pair_bounds1 A B R hA hB hd hu hR) all_pairs1
    rw [← actual_pair_weight1 A B R hA hB hd hu] at hc
    exact okayWeight_sound _ hc
  · have hc := pair_counts_complete2 (blockCount A R ({0} : Finset (Fin 2))) (blockCount A R ({1} : Finset (Fin 2))) (blockCount A R ({0, 1} : Finset (Fin 2))) (blockCount B R ({0} : Finset (Fin 2))) (blockCount B R ({1} : Finset (Fin 2))) (blockCount B R ({0, 1} : Finset (Fin 2)))
      (actual_pair_bounds2 A B R hA hB hd hu hR) all_pairs2
    rw [← actual_pair_weight2 A B R hA hB hd hu] at hc
    exact okayWeight_sound _ hc
  · have hc := pair_counts_complete3 (blockCount A R ({0} : Finset (Fin 3))) (blockCount A R ({1} : Finset (Fin 3))) (blockCount A R ({0, 1} : Finset (Fin 3))) (blockCount A R ({2} : Finset (Fin 3))) (blockCount A R ({0, 2} : Finset (Fin 3))) (blockCount A R ({1, 2} : Finset (Fin 3))) (blockCount A R ({0, 1, 2} : Finset (Fin 3))) (blockCount B R ({0} : Finset (Fin 3))) (blockCount B R ({1} : Finset (Fin 3))) (blockCount B R ({0, 1} : Finset (Fin 3))) (blockCount B R ({2} : Finset (Fin 3))) (blockCount B R ({0, 2} : Finset (Fin 3))) (blockCount B R ({1, 2} : Finset (Fin 3))) (blockCount B R ({0, 1, 2} : Finset (Fin 3)))
      (actual_pair_bounds3 A B R hA hB hd hu hR) all_pairs3
    rw [← actual_pair_weight3 A B R hA hB hd hu] at hc
    exact okayWeight_sound _ hc

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.pair_good
