import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock02
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_6_10 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 2, 1, 2],
    ![1, 0, 1, 2, 2, 1],
    ![2, 1, 0, 1, 2, 2],
    ![2, 2, 1, 0, 1, 3],
    ![1, 2, 2, 1, 0, 3],
    ![2, 1, 2, 3, 3, 0]] u v

private theorem cert_6_10 :
    (∀ x : Fin 6, D_6_10 x x = 0) ∧
    (∀ x y : Fin 6, D_6_10 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_10 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 10).Adj x z ∧ D_6_10 z y + 1 = D_6_10 x y) ∧
    (∀ u v w : Fin 6, (reps 6 10).Adj u v → D_6_10 u w ≤ D_6_10 v w + 1) := by
  decide +kernel

theorem classify_6_10 : ¬ Challenge.IsMedian (reps 6 10) ∨
    (Challenge.Question3' (reps 6 10) ∧ Challenge.Question4 (reps 6 10)) := by
  have hD : ∀ x y, (reps 6 10).dist x y = D_6_10 x y :=
    dist_eq_of_certificate (reps 6 10) D_6_10 cert_6_10.1 cert_6_10.2.1
      cert_6_10.2.2.1 cert_6_10.2.2.2
  have hc : (reps 6 10).Connected := connected_of_dist (reps 6 10) D_6_10 hD cert_6_10.2.1
  have hd : (reps 6 10).diam = 3 :=
    diam_eq_of_table (reps 6 10) D_6_10 hc hD 3
      (by decide +kernel) 3 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 10) = 7 :=
    triameter_eq_of_table (reps 6 10) D_6_10 hD 7
      (by decide +kernel) 0 3 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 10) D_6_10 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 10) D_6_10 hD 3 7 hd ht (by decide +kernel)⟩

private def D_6_11 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 3, 2, 1],
    ![1, 0, 1, 2, 3, 2],
    ![2, 1, 0, 1, 2, 3],
    ![3, 2, 1, 0, 1, 2],
    ![2, 3, 2, 1, 0, 1],
    ![1, 2, 3, 2, 1, 0]] u v

private theorem cert_6_11 :
    (∀ x : Fin 6, D_6_11 x x = 0) ∧
    (∀ x y : Fin 6, D_6_11 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_11 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 11).Adj x z ∧ D_6_11 z y + 1 = D_6_11 x y) ∧
    (∀ u v w : Fin 6, (reps 6 11).Adj u v → D_6_11 u w ≤ D_6_11 v w + 1) := by
  decide +kernel

theorem classify_6_11 : ¬ Challenge.IsMedian (reps 6 11) ∨
    (Challenge.Question3' (reps 6 11) ∧ Challenge.Question4 (reps 6 11)) := by
  have hD : ∀ x y, (reps 6 11).dist x y = D_6_11 x y :=
    dist_eq_of_certificate (reps 6 11) D_6_11 cert_6_11.1 cert_6_11.2.1
      cert_6_11.2.2.1 cert_6_11.2.2.2
  have hc : (reps 6 11).Connected := connected_of_dist (reps 6 11) D_6_11 hD cert_6_11.2.1
  have hd : (reps 6 11).diam = 3 :=
    diam_eq_of_table (reps 6 11) D_6_11 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 11) = 6 :=
    triameter_eq_of_table (reps 6 11) D_6_11 hD 6
      (by decide +kernel) 0 0 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 11) D_6_11 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 11) D_6_11 hD 3 6 hd ht (by decide +kernel)⟩

private def D_6_12 (u v : Fin 6) : ℕ :=
  ![![0, 2, 1, 2, 3, 2],
    ![2, 0, 1, 2, 1, 2],
    ![1, 1, 0, 1, 2, 1],
    ![2, 2, 1, 0, 1, 2],
    ![3, 1, 2, 1, 0, 1],
    ![2, 2, 1, 2, 1, 0]] u v

private theorem cert_6_12 :
    (∀ x : Fin 6, D_6_12 x x = 0) ∧
    (∀ x y : Fin 6, D_6_12 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_12 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 12).Adj x z ∧ D_6_12 z y + 1 = D_6_12 x y) ∧
    (∀ u v w : Fin 6, (reps 6 12).Adj u v → D_6_12 u w ≤ D_6_12 v w + 1) := by
  decide +kernel

theorem classify_6_12 : ¬ Challenge.IsMedian (reps 6 12) ∨
    (Challenge.Question3' (reps 6 12) ∧ Challenge.Question4 (reps 6 12)) := by
  have hD : ∀ x y, (reps 6 12).dist x y = D_6_12 x y :=
    dist_eq_of_certificate (reps 6 12) D_6_12 cert_6_12.1 cert_6_12.2.1
      cert_6_12.2.2.1 cert_6_12.2.2.2
  exact Or.inl (not_median_of_two (reps 6 12) D_6_12 hD 1 3 5 2 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_6_13 (u v : Fin 6) : ℕ :=
  ![![0, 2, 1, 3, 3, 2],
    ![2, 0, 1, 1, 1, 2],
    ![1, 1, 0, 2, 2, 1],
    ![3, 1, 2, 0, 2, 1],
    ![3, 1, 2, 2, 0, 1],
    ![2, 2, 1, 1, 1, 0]] u v

private theorem cert_6_13 :
    (∀ x : Fin 6, D_6_13 x x = 0) ∧
    (∀ x y : Fin 6, D_6_13 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_13 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 13).Adj x z ∧ D_6_13 z y + 1 = D_6_13 x y) ∧
    (∀ u v w : Fin 6, (reps 6 13).Adj u v → D_6_13 u w ≤ D_6_13 v w + 1) := by
  decide +kernel

theorem classify_6_13 : ¬ Challenge.IsMedian (reps 6 13) ∨
    (Challenge.Question3' (reps 6 13) ∧ Challenge.Question4 (reps 6 13)) := by
  have hD : ∀ x y, (reps 6 13).dist x y = D_6_13 x y :=
    dist_eq_of_certificate (reps 6 13) D_6_13 cert_6_13.1 cert_6_13.2.1
      cert_6_13.2.2.1 cert_6_13.2.2.2
  have hc : (reps 6 13).Connected := connected_of_dist (reps 6 13) D_6_13 hD cert_6_13.2.1
  have hd : (reps 6 13).diam = 3 :=
    diam_eq_of_table (reps 6 13) D_6_13 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 13) = 8 :=
    triameter_eq_of_table (reps 6 13) D_6_13 hD 8
      (by decide +kernel) 0 3 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 13) D_6_13 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 13) D_6_13 hD 3 8 hd ht (by decide +kernel)⟩

private def D_6_14 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 1, 2, 1],
    ![1, 0, 1, 2, 3, 2],
    ![2, 1, 0, 1, 2, 3],
    ![1, 2, 1, 0, 1, 2],
    ![2, 3, 2, 1, 0, 1],
    ![1, 2, 3, 2, 1, 0]] u v

private theorem cert_6_14 :
    (∀ x : Fin 6, D_6_14 x x = 0) ∧
    (∀ x y : Fin 6, D_6_14 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_14 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 14).Adj x z ∧ D_6_14 z y + 1 = D_6_14 x y) ∧
    (∀ u v w : Fin 6, (reps 6 14).Adj u v → D_6_14 u w ≤ D_6_14 v w + 1) := by
  decide +kernel

theorem classify_6_14 : ¬ Challenge.IsMedian (reps 6 14) ∨
    (Challenge.Question3' (reps 6 14) ∧ Challenge.Question4 (reps 6 14)) := by
  have hD : ∀ x y, (reps 6 14).dist x y = D_6_14 x y :=
    dist_eq_of_certificate (reps 6 14) D_6_14 cert_6_14.1 cert_6_14.2.1
      cert_6_14.2.2.1 cert_6_14.2.2.2
  have hc : (reps 6 14).Connected := connected_of_dist (reps 6 14) D_6_14 hD cert_6_14.2.1
  have hd : (reps 6 14).diam = 3 :=
    diam_eq_of_table (reps 6 14) D_6_14 hc hD 3
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 14) = 6 :=
    triameter_eq_of_table (reps 6 14) D_6_14 hD 6
      (by decide +kernel) 0 1 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 14) D_6_14 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 14) D_6_14 hD 3 6 hd ht (by decide +kernel)⟩

private def D_6_15 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 2, 1, 1],
    ![1, 0, 1, 2, 2, 2],
    ![2, 1, 0, 1, 2, 2],
    ![2, 2, 1, 0, 1, 1],
    ![1, 2, 2, 1, 0, 2],
    ![1, 2, 2, 1, 2, 0]] u v

private theorem cert_6_15 :
    (∀ x : Fin 6, D_6_15 x x = 0) ∧
    (∀ x y : Fin 6, D_6_15 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_15 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 15).Adj x z ∧ D_6_15 z y + 1 = D_6_15 x y) ∧
    (∀ u v w : Fin 6, (reps 6 15).Adj u v → D_6_15 u w ≤ D_6_15 v w + 1) := by
  decide +kernel

theorem classify_6_15 : ¬ Challenge.IsMedian (reps 6 15) ∨
    (Challenge.Question3' (reps 6 15) ∧ Challenge.Question4 (reps 6 15)) := by
  have hD : ∀ x y, (reps 6 15).dist x y = D_6_15 x y :=
    dist_eq_of_certificate (reps 6 15) D_6_15 cert_6_15.1 cert_6_15.2.1
      cert_6_15.2.2.1 cert_6_15.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 6) 1 3
  have hnone : ∀ x : Fin 6, ¬ ((D_6_15 0 x + D_6_15 x 1 = D_6_15 0 1) ∧
      (D_6_15 0 x + D_6_15 x 3 = D_6_15 0 3) ∧
      (D_6_15 1 x + D_6_15 x 3 = D_6_15 1 3)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_6_16 (u v : Fin 6) : ℕ :=
  ![![0, 2, 2, 2, 1, 1],
    ![2, 0, 2, 2, 1, 1],
    ![2, 2, 0, 2, 1, 1],
    ![2, 2, 2, 0, 1, 1],
    ![1, 1, 1, 1, 0, 2],
    ![1, 1, 1, 1, 2, 0]] u v

private theorem cert_6_16 :
    (∀ x : Fin 6, D_6_16 x x = 0) ∧
    (∀ x y : Fin 6, D_6_16 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_16 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 16).Adj x z ∧ D_6_16 z y + 1 = D_6_16 x y) ∧
    (∀ u v w : Fin 6, (reps 6 16).Adj u v → D_6_16 u w ≤ D_6_16 v w + 1) := by
  decide +kernel

theorem classify_6_16 : ¬ Challenge.IsMedian (reps 6 16) ∨
    (Challenge.Question3' (reps 6 16) ∧ Challenge.Question4 (reps 6 16)) := by
  have hD : ∀ x y, (reps 6 16).dist x y = D_6_16 x y :=
    dist_eq_of_certificate (reps 6 16) D_6_16 cert_6_16.1 cert_6_16.2.1
      cert_6_16.2.2.1 cert_6_16.2.2.2
  exact Or.inl (not_median_of_two (reps 6 16) D_6_16 hD 0 1 2 4 5
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_6_17 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 3, 2, 1],
    ![1, 0, 1, 2, 1, 2],
    ![2, 1, 0, 1, 2, 1],
    ![3, 2, 1, 0, 1, 2],
    ![2, 1, 2, 1, 0, 1],
    ![1, 2, 1, 2, 1, 0]] u v

private theorem cert_6_17 :
    (∀ x : Fin 6, D_6_17 x x = 0) ∧
    (∀ x y : Fin 6, D_6_17 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_17 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 17).Adj x z ∧ D_6_17 z y + 1 = D_6_17 x y) ∧
    (∀ u v w : Fin 6, (reps 6 17).Adj u v → D_6_17 u w ≤ D_6_17 v w + 1) := by
  decide +kernel

theorem classify_6_17 : ¬ Challenge.IsMedian (reps 6 17) ∨
    (Challenge.Question3' (reps 6 17) ∧ Challenge.Question4 (reps 6 17)) := by
  have hD : ∀ x y, (reps 6 17).dist x y = D_6_17 x y :=
    dist_eq_of_certificate (reps 6 17) D_6_17 cert_6_17.1 cert_6_17.2.1
      cert_6_17.2.2.1 cert_6_17.2.2.2
  have hc : (reps 6 17).Connected := connected_of_dist (reps 6 17) D_6_17 hD cert_6_17.2.1
  have hd : (reps 6 17).diam = 3 :=
    diam_eq_of_table (reps 6 17) D_6_17 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 17) = 6 :=
    triameter_eq_of_table (reps 6 17) D_6_17 hD 6
      (by decide +kernel) 0 0 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 17) D_6_17 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 17) D_6_17 hD 3 6 hd ht (by decide +kernel)⟩

private def D_6_18 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 1, 2, 1],
    ![1, 0, 1, 2, 1, 2],
    ![2, 1, 0, 1, 2, 1],
    ![1, 2, 1, 0, 1, 2],
    ![2, 1, 2, 1, 0, 1],
    ![1, 2, 1, 2, 1, 0]] u v

private theorem cert_6_18 :
    (∀ x : Fin 6, D_6_18 x x = 0) ∧
    (∀ x y : Fin 6, D_6_18 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_18 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 18).Adj x z ∧ D_6_18 z y + 1 = D_6_18 x y) ∧
    (∀ u v w : Fin 6, (reps 6 18).Adj u v → D_6_18 u w ≤ D_6_18 v w + 1) := by
  decide +kernel

theorem classify_6_18 : ¬ Challenge.IsMedian (reps 6 18) ∨
    (Challenge.Question3' (reps 6 18) ∧ Challenge.Question4 (reps 6 18)) := by
  have hD : ∀ x y, (reps 6 18).dist x y = D_6_18 x y :=
    dist_eq_of_certificate (reps 6 18) D_6_18 cert_6_18.1 cert_6_18.2.1
      cert_6_18.2.2.1 cert_6_18.2.2.2
  have hc : (reps 6 18).Connected := connected_of_dist (reps 6 18) D_6_18 hD cert_6_18.2.1
  have hd : (reps 6 18).diam = 2 :=
    diam_eq_of_table (reps 6 18) D_6_18 hc hD 2
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 18) = 6 :=
    triameter_eq_of_table (reps 6 18) D_6_18 hD 6
      (by decide +kernel) 0 2 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 18) D_6_18 hc hD 2 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 18) D_6_18 hD 2 6 hd ht (by decide +kernel)⟩

#print axioms classify_6_10
#print axioms classify_6_11
#print axioms classify_6_12
#print axioms classify_6_13
#print axioms classify_6_14
#print axioms classify_6_15
#print axioms classify_6_16
#print axioms classify_6_17
#print axioms classify_6_18

end CodexPaper4.SmallMedianClassificationBlock02
