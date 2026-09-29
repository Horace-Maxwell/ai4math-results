import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock08
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_7_50 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 1, 1, 2, 2],
    ![1, 0, 1, 2, 2, 3, 3],
    ![2, 1, 0, 1, 1, 2, 2],
    ![1, 2, 1, 0, 2, 2, 1],
    ![1, 2, 1, 2, 0, 1, 2],
    ![2, 3, 2, 2, 1, 0, 1],
    ![2, 3, 2, 1, 2, 1, 0]] u v

private theorem cert_7_50 :
    (∀ x : Fin 7, D_7_50 x x = 0) ∧
    (∀ x y : Fin 7, D_7_50 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_50 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 50).Adj x z ∧ D_7_50 z y + 1 = D_7_50 x y) ∧
    (∀ u v w : Fin 7, (reps 7 50).Adj u v → D_7_50 u w ≤ D_7_50 v w + 1) := by
  decide +kernel

theorem classify_7_50 : ¬ Challenge.IsMedian (reps 7 50) ∨
    (Challenge.Question3' (reps 7 50) ∧ Challenge.Question4 (reps 7 50)) := by
  have hD : ∀ x y, (reps 7 50).dist x y = D_7_50 x y :=
    dist_eq_of_certificate (reps 7 50) D_7_50 cert_7_50.1 cert_7_50.2.1
      cert_7_50.2.2.1 cert_7_50.2.2.2
  have hc : (reps 7 50).Connected := connected_of_dist (reps 7 50) D_7_50 hD cert_7_50.2.1
  have hd : (reps 7 50).diam = 3 :=
    diam_eq_of_table (reps 7 50) D_7_50 hc hD 3
      (by decide +kernel) 1 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 50) = 7 :=
    triameter_eq_of_table (reps 7 50) D_7_50 hD 7
      (by decide +kernel) 1 3 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 50) D_7_50 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 50) D_7_50 hD 3 7 hd ht (by decide +kernel)⟩

private def D_7_51 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 2, 1, 1],
    ![1, 0, 1, 2, 3, 2, 2],
    ![2, 1, 0, 1, 2, 3, 1],
    ![3, 2, 1, 0, 1, 2, 2],
    ![2, 3, 2, 1, 0, 1, 1],
    ![1, 2, 3, 2, 1, 0, 2],
    ![1, 2, 1, 2, 1, 2, 0]] u v

private theorem cert_7_51 :
    (∀ x : Fin 7, D_7_51 x x = 0) ∧
    (∀ x y : Fin 7, D_7_51 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_51 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 51).Adj x z ∧ D_7_51 z y + 1 = D_7_51 x y) ∧
    (∀ u v w : Fin 7, (reps 7 51).Adj u v → D_7_51 u w ≤ D_7_51 v w + 1) := by
  decide +kernel

theorem classify_7_51 : ¬ Challenge.IsMedian (reps 7 51) ∨
    (Challenge.Question3' (reps 7 51) ∧ Challenge.Question4 (reps 7 51)) := by
  have hD : ∀ x y, (reps 7 51).dist x y = D_7_51 x y :=
    dist_eq_of_certificate (reps 7 51) D_7_51 cert_7_51.1 cert_7_51.2.1
      cert_7_51.2.2.1 cert_7_51.2.2.2
  have hc : (reps 7 51).Connected := connected_of_dist (reps 7 51) D_7_51 hD cert_7_51.2.1
  have hd : (reps 7 51).diam = 3 :=
    diam_eq_of_table (reps 7 51) D_7_51 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 51) = 6 :=
    triameter_eq_of_table (reps 7 51) D_7_51 hD 6
      (by decide +kernel) 0 0 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 51) D_7_51 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 51) D_7_51 hD 3 6 hd ht (by decide +kernel)⟩

private def D_7_52 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 1, 2, 1, 1],
    ![1, 0, 1, 2, 1, 2, 2],
    ![2, 1, 0, 1, 2, 1, 3],
    ![1, 2, 1, 0, 1, 2, 2],
    ![2, 1, 2, 1, 0, 1, 3],
    ![1, 2, 1, 2, 1, 0, 2],
    ![1, 2, 3, 2, 3, 2, 0]] u v

private theorem cert_7_52 :
    (∀ x : Fin 7, D_7_52 x x = 0) ∧
    (∀ x y : Fin 7, D_7_52 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_52 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 52).Adj x z ∧ D_7_52 z y + 1 = D_7_52 x y) ∧
    (∀ u v w : Fin 7, (reps 7 52).Adj u v → D_7_52 u w ≤ D_7_52 v w + 1) := by
  decide +kernel

theorem classify_7_52 : ¬ Challenge.IsMedian (reps 7 52) ∨
    (Challenge.Question3' (reps 7 52) ∧ Challenge.Question4 (reps 7 52)) := by
  have hD : ∀ x y, (reps 7 52).dist x y = D_7_52 x y :=
    dist_eq_of_certificate (reps 7 52) D_7_52 cert_7_52.1 cert_7_52.2.1
      cert_7_52.2.2.1 cert_7_52.2.2.2
  have hc : (reps 7 52).Connected := connected_of_dist (reps 7 52) D_7_52 hD cert_7_52.2.1
  have hd : (reps 7 52).diam = 3 :=
    diam_eq_of_table (reps 7 52) D_7_52 hc hD 3
      (by decide +kernel) 2 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 52) = 8 :=
    triameter_eq_of_table (reps 7 52) D_7_52 hD 8
      (by decide +kernel) 2 4 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 52) D_7_52 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 52) D_7_52 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_53 (u v : Fin 7) : ℕ :=
  ![![0, 2, 1, 1, 1, 1, 1],
    ![2, 0, 1, 1, 1, 1, 1],
    ![1, 1, 0, 2, 2, 2, 2],
    ![1, 1, 2, 0, 2, 2, 2],
    ![1, 1, 2, 2, 0, 2, 2],
    ![1, 1, 2, 2, 2, 0, 2],
    ![1, 1, 2, 2, 2, 2, 0]] u v

private theorem cert_7_53 :
    (∀ x : Fin 7, D_7_53 x x = 0) ∧
    (∀ x y : Fin 7, D_7_53 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_53 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 53).Adj x z ∧ D_7_53 z y + 1 = D_7_53 x y) ∧
    (∀ u v w : Fin 7, (reps 7 53).Adj u v → D_7_53 u w ≤ D_7_53 v w + 1) := by
  decide +kernel

theorem classify_7_53 : ¬ Challenge.IsMedian (reps 7 53) ∨
    (Challenge.Question3' (reps 7 53) ∧ Challenge.Question4 (reps 7 53)) := by
  have hD : ∀ x y, (reps 7 53).dist x y = D_7_53 x y :=
    dist_eq_of_certificate (reps 7 53) D_7_53 cert_7_53.1 cert_7_53.2.1
      cert_7_53.2.2.1 cert_7_53.2.2.2
  exact Or.inl (not_median_of_two (reps 7 53) D_7_53 hD 2 3 4 0 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_7_54 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 2, 2],
    ![2, 0, 1, 1, 1, 2, 2],
    ![3, 1, 0, 2, 2, 1, 3],
    ![1, 1, 2, 0, 2, 1, 1],
    ![1, 1, 2, 2, 0, 1, 1],
    ![2, 2, 1, 1, 1, 0, 2],
    ![2, 2, 3, 1, 1, 2, 0]] u v

private theorem cert_7_54 :
    (∀ x : Fin 7, D_7_54 x x = 0) ∧
    (∀ x y : Fin 7, D_7_54 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_54 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 54).Adj x z ∧ D_7_54 z y + 1 = D_7_54 x y) ∧
    (∀ u v w : Fin 7, (reps 7 54).Adj u v → D_7_54 u w ≤ D_7_54 v w + 1) := by
  decide +kernel

theorem classify_7_54 : ¬ Challenge.IsMedian (reps 7 54) ∨
    (Challenge.Question3' (reps 7 54) ∧ Challenge.Question4 (reps 7 54)) := by
  have hD : ∀ x y, (reps 7 54).dist x y = D_7_54 x y :=
    dist_eq_of_certificate (reps 7 54) D_7_54 cert_7_54.1 cert_7_54.2.1
      cert_7_54.2.2.1 cert_7_54.2.2.2
  have hc : (reps 7 54).Connected := connected_of_dist (reps 7 54) D_7_54 hD cert_7_54.2.1
  have hd : (reps 7 54).diam = 3 :=
    diam_eq_of_table (reps 7 54) D_7_54 hc hD 3
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 54) = 8 :=
    triameter_eq_of_table (reps 7 54) D_7_54 hD 8
      (by decide +kernel) 0 2 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 54) D_7_54 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 54) D_7_54 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_55 (u v : Fin 7) : ℕ :=
  ![![0, 2, 1, 1, 2, 1, 3],
    ![2, 0, 1, 1, 2, 3, 1],
    ![1, 1, 0, 2, 1, 2, 2],
    ![1, 1, 2, 0, 1, 2, 2],
    ![2, 2, 1, 1, 0, 1, 1],
    ![1, 3, 2, 2, 1, 0, 2],
    ![3, 1, 2, 2, 1, 2, 0]] u v

private theorem cert_7_55 :
    (∀ x : Fin 7, D_7_55 x x = 0) ∧
    (∀ x y : Fin 7, D_7_55 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_55 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 55).Adj x z ∧ D_7_55 z y + 1 = D_7_55 x y) ∧
    (∀ u v w : Fin 7, (reps 7 55).Adj u v → D_7_55 u w ≤ D_7_55 v w + 1) := by
  decide +kernel

theorem classify_7_55 : ¬ Challenge.IsMedian (reps 7 55) ∨
    (Challenge.Question3' (reps 7 55) ∧ Challenge.Question4 (reps 7 55)) := by
  have hD : ∀ x y, (reps 7 55).dist x y = D_7_55 x y :=
    dist_eq_of_certificate (reps 7 55) D_7_55 cert_7_55.1 cert_7_55.2.1
      cert_7_55.2.2.1 cert_7_55.2.2.2
  have hc : (reps 7 55).Connected := connected_of_dist (reps 7 55) D_7_55 hD cert_7_55.2.1
  have hd : (reps 7 55).diam = 3 :=
    diam_eq_of_table (reps 7 55) D_7_55 hc hD 3
      (by decide +kernel) 0 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 55) = 6 :=
    triameter_eq_of_table (reps 7 55) D_7_55 hD 6
      (by decide +kernel) 0 0 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 55) D_7_55 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 55) D_7_55 hD 3 6 hd ht (by decide +kernel)⟩

private def D_7_56 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 2, 2, 1, 1],
    ![1, 0, 1, 2, 1, 2, 2],
    ![2, 1, 0, 1, 2, 1, 2],
    ![2, 2, 1, 0, 1, 2, 1],
    ![2, 1, 2, 1, 0, 1, 2],
    ![1, 2, 1, 2, 1, 0, 2],
    ![1, 2, 2, 1, 2, 2, 0]] u v

private theorem cert_7_56 :
    (∀ x : Fin 7, D_7_56 x x = 0) ∧
    (∀ x y : Fin 7, D_7_56 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_56 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 56).Adj x z ∧ D_7_56 z y + 1 = D_7_56 x y) ∧
    (∀ u v w : Fin 7, (reps 7 56).Adj u v → D_7_56 u w ≤ D_7_56 v w + 1) := by
  decide +kernel

theorem classify_7_56 : ¬ Challenge.IsMedian (reps 7 56) ∨
    (Challenge.Question3' (reps 7 56) ∧ Challenge.Question4 (reps 7 56)) := by
  have hD : ∀ x y, (reps 7 56).dist x y = D_7_56 x y :=
    dist_eq_of_certificate (reps 7 56) D_7_56 cert_7_56.1 cert_7_56.2.1
      cert_7_56.2.2.1 cert_7_56.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 7) 1 3
  have hnone : ∀ x : Fin 7, ¬ ((D_7_56 0 x + D_7_56 x 1 = D_7_56 0 1) ∧
      (D_7_56 0 x + D_7_56 x 3 = D_7_56 0 3) ∧
      (D_7_56 1 x + D_7_56 x 3 = D_7_56 1 3)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_7_57 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 1, 1, 2, 2],
    ![1, 0, 1, 2, 2, 1, 3],
    ![2, 1, 0, 1, 1, 2, 2],
    ![1, 2, 1, 0, 2, 1, 1],
    ![1, 2, 1, 2, 0, 1, 1],
    ![2, 1, 2, 1, 1, 0, 2],
    ![2, 3, 2, 1, 1, 2, 0]] u v

private theorem cert_7_57 :
    (∀ x : Fin 7, D_7_57 x x = 0) ∧
    (∀ x y : Fin 7, D_7_57 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_57 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 57).Adj x z ∧ D_7_57 z y + 1 = D_7_57 x y) ∧
    (∀ u v w : Fin 7, (reps 7 57).Adj u v → D_7_57 u w ≤ D_7_57 v w + 1) := by
  decide +kernel

theorem classify_7_57 : ¬ Challenge.IsMedian (reps 7 57) ∨
    (Challenge.Question3' (reps 7 57) ∧ Challenge.Question4 (reps 7 57)) := by
  have hD : ∀ x y, (reps 7 57).dist x y = D_7_57 x y :=
    dist_eq_of_certificate (reps 7 57) D_7_57 cert_7_57.1 cert_7_57.2.1
      cert_7_57.2.2.1 cert_7_57.2.2.2
  exact Or.inl (not_median_of_two (reps 7 57) D_7_57 hD 0 2 5 1 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_7_58 (u v : Fin 7) : ℕ :=
  ![![0, 1, 1, 2, 1, 1, 2],
    ![1, 0, 2, 1, 2, 2, 1],
    ![1, 2, 0, 1, 2, 2, 1],
    ![2, 1, 1, 0, 1, 1, 2],
    ![1, 2, 2, 1, 0, 2, 1],
    ![1, 2, 2, 1, 2, 0, 1],
    ![2, 1, 1, 2, 1, 1, 0]] u v

private theorem cert_7_58 :
    (∀ x : Fin 7, D_7_58 x x = 0) ∧
    (∀ x y : Fin 7, D_7_58 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_58 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 58).Adj x z ∧ D_7_58 z y + 1 = D_7_58 x y) ∧
    (∀ u v w : Fin 7, (reps 7 58).Adj u v → D_7_58 u w ≤ D_7_58 v w + 1) := by
  decide +kernel

theorem classify_7_58 : ¬ Challenge.IsMedian (reps 7 58) ∨
    (Challenge.Question3' (reps 7 58) ∧ Challenge.Question4 (reps 7 58)) := by
  have hD : ∀ x y, (reps 7 58).dist x y = D_7_58 x y :=
    dist_eq_of_certificate (reps 7 58) D_7_58 cert_7_58.1 cert_7_58.2.1
      cert_7_58.2.2.1 cert_7_58.2.2.2
  have hc : (reps 7 58).Connected := connected_of_dist (reps 7 58) D_7_58 hD cert_7_58.2.1
  have hd : (reps 7 58).diam = 2 :=
    diam_eq_of_table (reps 7 58) D_7_58 hc hD 2
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 58) = 6 :=
    triameter_eq_of_table (reps 7 58) D_7_58 hD 6
      (by decide +kernel) 0 3 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 58) D_7_58 hc hD 2 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 58) D_7_58 hD 2 6 hd ht (by decide +kernel)⟩

#print axioms classify_7_50
#print axioms classify_7_51
#print axioms classify_7_52
#print axioms classify_7_53
#print axioms classify_7_54
#print axioms classify_7_55
#print axioms classify_7_56
#print axioms classify_7_57
#print axioms classify_7_58

end CodexPaper4.SmallMedianClassificationBlock08
