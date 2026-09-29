import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock04
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_7_10 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 4, 5, 1],
    ![1, 0, 1, 2, 3, 4, 2],
    ![2, 1, 0, 1, 2, 3, 3],
    ![3, 2, 1, 0, 1, 2, 4],
    ![4, 3, 2, 1, 0, 1, 5],
    ![5, 4, 3, 2, 1, 0, 6],
    ![1, 2, 3, 4, 5, 6, 0]] u v

private theorem cert_7_10 :
    (∀ x : Fin 7, D_7_10 x x = 0) ∧
    (∀ x y : Fin 7, D_7_10 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_10 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 10).Adj x z ∧ D_7_10 z y + 1 = D_7_10 x y) ∧
    (∀ u v w : Fin 7, (reps 7 10).Adj u v → D_7_10 u w ≤ D_7_10 v w + 1) := by
  decide +kernel

theorem classify_7_10 : ¬ Challenge.IsMedian (reps 7 10) ∨
    (Challenge.Question3' (reps 7 10) ∧ Challenge.Question4 (reps 7 10)) := by
  have hD : ∀ x y, (reps 7 10).dist x y = D_7_10 x y :=
    dist_eq_of_certificate (reps 7 10) D_7_10 cert_7_10.1 cert_7_10.2.1
      cert_7_10.2.2.1 cert_7_10.2.2.2
  have hc : (reps 7 10).Connected := connected_of_dist (reps 7 10) D_7_10 hD cert_7_10.2.1
  have hd : (reps 7 10).diam = 6 :=
    diam_eq_of_table (reps 7 10) D_7_10 hc hD 6
      (by decide +kernel) 5 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 10) = 12 :=
    triameter_eq_of_table (reps 7 10) D_7_10 hD 12
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 10) D_7_10 hc hD 6 12 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 10) D_7_10 hD 6 12 hd ht (by decide +kernel)⟩

private def D_7_11 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 3, 3],
    ![2, 0, 1, 1, 1, 1, 1],
    ![3, 1, 0, 2, 2, 2, 2],
    ![1, 1, 2, 0, 2, 2, 2],
    ![1, 1, 2, 2, 0, 2, 2],
    ![3, 1, 2, 2, 2, 0, 2],
    ![3, 1, 2, 2, 2, 2, 0]] u v

private theorem cert_7_11 :
    (∀ x : Fin 7, D_7_11 x x = 0) ∧
    (∀ x y : Fin 7, D_7_11 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_11 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 11).Adj x z ∧ D_7_11 z y + 1 = D_7_11 x y) ∧
    (∀ u v w : Fin 7, (reps 7 11).Adj u v → D_7_11 u w ≤ D_7_11 v w + 1) := by
  decide +kernel

theorem classify_7_11 : ¬ Challenge.IsMedian (reps 7 11) ∨
    (Challenge.Question3' (reps 7 11) ∧ Challenge.Question4 (reps 7 11)) := by
  have hD : ∀ x y, (reps 7 11).dist x y = D_7_11 x y :=
    dist_eq_of_certificate (reps 7 11) D_7_11 cert_7_11.1 cert_7_11.2.1
      cert_7_11.2.2.1 cert_7_11.2.2.2
  have hc : (reps 7 11).Connected := connected_of_dist (reps 7 11) D_7_11 hD cert_7_11.2.1
  have hd : (reps 7 11).diam = 3 :=
    diam_eq_of_table (reps 7 11) D_7_11 hc hD 3
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 11) = 8 :=
    triameter_eq_of_table (reps 7 11) D_7_11 hD 8
      (by decide +kernel) 0 2 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 11) D_7_11 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 11) D_7_11 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_12 (u v : Fin 7) : ℕ :=
  ![![0, 3, 2, 3, 2, 1, 2],
    ![3, 0, 1, 2, 3, 2, 3],
    ![2, 1, 0, 1, 2, 1, 2],
    ![3, 2, 1, 0, 3, 2, 1],
    ![2, 3, 2, 3, 0, 1, 2],
    ![1, 2, 1, 2, 1, 0, 1],
    ![2, 3, 2, 1, 2, 1, 0]] u v

private theorem cert_7_12 :
    (∀ x : Fin 7, D_7_12 x x = 0) ∧
    (∀ x y : Fin 7, D_7_12 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_12 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 12).Adj x z ∧ D_7_12 z y + 1 = D_7_12 x y) ∧
    (∀ u v w : Fin 7, (reps 7 12).Adj u v → D_7_12 u w ≤ D_7_12 v w + 1) := by
  decide +kernel

theorem classify_7_12 : ¬ Challenge.IsMedian (reps 7 12) ∨
    (Challenge.Question3' (reps 7 12) ∧ Challenge.Question4 (reps 7 12)) := by
  have hD : ∀ x y, (reps 7 12).dist x y = D_7_12 x y :=
    dist_eq_of_certificate (reps 7 12) D_7_12 cert_7_12.1 cert_7_12.2.1
      cert_7_12.2.2.1 cert_7_12.2.2.2
  have hc : (reps 7 12).Connected := connected_of_dist (reps 7 12) D_7_12 hD cert_7_12.2.1
  have hd : (reps 7 12).diam = 3 :=
    diam_eq_of_table (reps 7 12) D_7_12 hc hD 3
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 12) = 8 :=
    triameter_eq_of_table (reps 7 12) D_7_12 hD 8
      (by decide +kernel) 0 1 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 12) D_7_12 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 12) D_7_12 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_13 (u v : Fin 7) : ℕ :=
  ![![0, 1, 3, 2, 2, 4, 4],
    ![1, 0, 2, 1, 1, 3, 3],
    ![3, 2, 0, 1, 1, 1, 1],
    ![2, 1, 1, 0, 2, 2, 2],
    ![2, 1, 1, 2, 0, 2, 2],
    ![4, 3, 1, 2, 2, 0, 2],
    ![4, 3, 1, 2, 2, 2, 0]] u v

private theorem cert_7_13 :
    (∀ x : Fin 7, D_7_13 x x = 0) ∧
    (∀ x y : Fin 7, D_7_13 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_13 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 13).Adj x z ∧ D_7_13 z y + 1 = D_7_13 x y) ∧
    (∀ u v w : Fin 7, (reps 7 13).Adj u v → D_7_13 u w ≤ D_7_13 v w + 1) := by
  decide +kernel

theorem classify_7_13 : ¬ Challenge.IsMedian (reps 7 13) ∨
    (Challenge.Question3' (reps 7 13) ∧ Challenge.Question4 (reps 7 13)) := by
  have hD : ∀ x y, (reps 7 13).dist x y = D_7_13 x y :=
    dist_eq_of_certificate (reps 7 13) D_7_13 cert_7_13.1 cert_7_13.2.1
      cert_7_13.2.2.1 cert_7_13.2.2.2
  have hc : (reps 7 13).Connected := connected_of_dist (reps 7 13) D_7_13 hD cert_7_13.2.1
  have hd : (reps 7 13).diam = 4 :=
    diam_eq_of_table (reps 7 13) D_7_13 hc hD 4
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 13) = 10 :=
    triameter_eq_of_table (reps 7 13) D_7_13 hD 10
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 13) D_7_13 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 13) D_7_13 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_14 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 2, 2],
    ![2, 0, 1, 1, 1, 2, 2],
    ![3, 1, 0, 2, 2, 3, 3],
    ![1, 1, 2, 0, 2, 3, 1],
    ![1, 1, 2, 2, 0, 1, 3],
    ![2, 2, 3, 3, 1, 0, 4],
    ![2, 2, 3, 1, 3, 4, 0]] u v

private theorem cert_7_14 :
    (∀ x : Fin 7, D_7_14 x x = 0) ∧
    (∀ x y : Fin 7, D_7_14 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_14 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 14).Adj x z ∧ D_7_14 z y + 1 = D_7_14 x y) ∧
    (∀ u v w : Fin 7, (reps 7 14).Adj u v → D_7_14 u w ≤ D_7_14 v w + 1) := by
  decide +kernel

theorem classify_7_14 : ¬ Challenge.IsMedian (reps 7 14) ∨
    (Challenge.Question3' (reps 7 14) ∧ Challenge.Question4 (reps 7 14)) := by
  have hD : ∀ x y, (reps 7 14).dist x y = D_7_14 x y :=
    dist_eq_of_certificate (reps 7 14) D_7_14 cert_7_14.1 cert_7_14.2.1
      cert_7_14.2.2.1 cert_7_14.2.2.2
  have hc : (reps 7 14).Connected := connected_of_dist (reps 7 14) D_7_14 hD cert_7_14.2.1
  have hd : (reps 7 14).diam = 4 :=
    diam_eq_of_table (reps 7 14) D_7_14 hc hD 4
      (by decide +kernel) 5 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 14) = 10 :=
    triameter_eq_of_table (reps 7 14) D_7_14 hD 10
      (by decide +kernel) 2 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 14) D_7_14 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 14) D_7_14 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_15 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 4, 3],
    ![2, 0, 1, 1, 1, 2, 1],
    ![3, 1, 0, 2, 2, 1, 2],
    ![1, 1, 2, 0, 2, 3, 2],
    ![1, 1, 2, 2, 0, 3, 2],
    ![4, 2, 1, 3, 3, 0, 3],
    ![3, 1, 2, 2, 2, 3, 0]] u v

private theorem cert_7_15 :
    (∀ x : Fin 7, D_7_15 x x = 0) ∧
    (∀ x y : Fin 7, D_7_15 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_15 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 15).Adj x z ∧ D_7_15 z y + 1 = D_7_15 x y) ∧
    (∀ u v w : Fin 7, (reps 7 15).Adj u v → D_7_15 u w ≤ D_7_15 v w + 1) := by
  decide +kernel

theorem classify_7_15 : ¬ Challenge.IsMedian (reps 7 15) ∨
    (Challenge.Question3' (reps 7 15) ∧ Challenge.Question4 (reps 7 15)) := by
  have hD : ∀ x y, (reps 7 15).dist x y = D_7_15 x y :=
    dist_eq_of_certificate (reps 7 15) D_7_15 cert_7_15.1 cert_7_15.2.1
      cert_7_15.2.2.1 cert_7_15.2.2.2
  have hc : (reps 7 15).Connected := connected_of_dist (reps 7 15) D_7_15 hD cert_7_15.2.1
  have hd : (reps 7 15).diam = 4 :=
    diam_eq_of_table (reps 7 15) D_7_15 hc hD 4
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 15) = 10 :=
    triameter_eq_of_table (reps 7 15) D_7_15 hD 10
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 15) D_7_15 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 15) D_7_15 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_16 (u v : Fin 7) : ℕ :=
  ![![0, 1, 1, 2, 1, 1, 2],
    ![1, 0, 2, 3, 2, 2, 3],
    ![1, 2, 0, 1, 2, 2, 2],
    ![2, 3, 1, 0, 3, 2, 1],
    ![1, 2, 2, 3, 0, 2, 3],
    ![1, 2, 2, 2, 2, 0, 1],
    ![2, 3, 2, 1, 3, 1, 0]] u v

private theorem cert_7_16 :
    (∀ x : Fin 7, D_7_16 x x = 0) ∧
    (∀ x y : Fin 7, D_7_16 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_16 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 16).Adj x z ∧ D_7_16 z y + 1 = D_7_16 x y) ∧
    (∀ u v w : Fin 7, (reps 7 16).Adj u v → D_7_16 u w ≤ D_7_16 v w + 1) := by
  decide +kernel

theorem classify_7_16 : ¬ Challenge.IsMedian (reps 7 16) ∨
    (Challenge.Question3' (reps 7 16) ∧ Challenge.Question4 (reps 7 16)) := by
  have hD : ∀ x y, (reps 7 16).dist x y = D_7_16 x y :=
    dist_eq_of_certificate (reps 7 16) D_7_16 cert_7_16.1 cert_7_16.2.1
      cert_7_16.2.2.1 cert_7_16.2.2.2
  have hc : (reps 7 16).Connected := connected_of_dist (reps 7 16) D_7_16 hD cert_7_16.2.1
  have hd : (reps 7 16).diam = 3 :=
    diam_eq_of_table (reps 7 16) D_7_16 hc hD 3
      (by decide +kernel) 1 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 16) = 8 :=
    triameter_eq_of_table (reps 7 16) D_7_16 hD 8
      (by decide +kernel) 1 3 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 16) D_7_16 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 16) D_7_16 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_17 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 4, 2, 3],
    ![1, 0, 1, 2, 3, 1, 2],
    ![2, 1, 0, 1, 2, 2, 1],
    ![3, 2, 1, 0, 1, 3, 2],
    ![4, 3, 2, 1, 0, 4, 3],
    ![2, 1, 2, 3, 4, 0, 1],
    ![3, 2, 1, 2, 3, 1, 0]] u v

private theorem cert_7_17 :
    (∀ x : Fin 7, D_7_17 x x = 0) ∧
    (∀ x y : Fin 7, D_7_17 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_17 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 17).Adj x z ∧ D_7_17 z y + 1 = D_7_17 x y) ∧
    (∀ u v w : Fin 7, (reps 7 17).Adj u v → D_7_17 u w ≤ D_7_17 v w + 1) := by
  decide +kernel

theorem classify_7_17 : ¬ Challenge.IsMedian (reps 7 17) ∨
    (Challenge.Question3' (reps 7 17) ∧ Challenge.Question4 (reps 7 17)) := by
  have hD : ∀ x y, (reps 7 17).dist x y = D_7_17 x y :=
    dist_eq_of_certificate (reps 7 17) D_7_17 cert_7_17.1 cert_7_17.2.1
      cert_7_17.2.2.1 cert_7_17.2.2.2
  have hc : (reps 7 17).Connected := connected_of_dist (reps 7 17) D_7_17 hD cert_7_17.2.1
  have hd : (reps 7 17).diam = 4 :=
    diam_eq_of_table (reps 7 17) D_7_17 hc hD 4
      (by decide +kernel) 0 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 17) = 10 :=
    triameter_eq_of_table (reps 7 17) D_7_17 hD 10
      (by decide +kernel) 0 4 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 17) D_7_17 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 17) D_7_17 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_18 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 1, 2, 3],
    ![1, 0, 1, 2, 2, 2, 3],
    ![2, 1, 0, 1, 2, 1, 2],
    ![3, 2, 1, 0, 3, 2, 3],
    ![1, 2, 2, 3, 0, 1, 2],
    ![2, 2, 1, 2, 1, 0, 1],
    ![3, 3, 2, 3, 2, 1, 0]] u v

private theorem cert_7_18 :
    (∀ x : Fin 7, D_7_18 x x = 0) ∧
    (∀ x y : Fin 7, D_7_18 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_18 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 18).Adj x z ∧ D_7_18 z y + 1 = D_7_18 x y) ∧
    (∀ u v w : Fin 7, (reps 7 18).Adj u v → D_7_18 u w ≤ D_7_18 v w + 1) := by
  decide +kernel

theorem classify_7_18 : ¬ Challenge.IsMedian (reps 7 18) ∨
    (Challenge.Question3' (reps 7 18) ∧ Challenge.Question4 (reps 7 18)) := by
  have hD : ∀ x y, (reps 7 18).dist x y = D_7_18 x y :=
    dist_eq_of_certificate (reps 7 18) D_7_18 cert_7_18.1 cert_7_18.2.1
      cert_7_18.2.2.1 cert_7_18.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 7) 1 5
  have hnone : ∀ x : Fin 7, ¬ ((D_7_18 0 x + D_7_18 x 1 = D_7_18 0 1) ∧
      (D_7_18 0 x + D_7_18 x 5 = D_7_18 0 5) ∧
      (D_7_18 1 x + D_7_18 x 5 = D_7_18 1 5)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_7_19 (u v : Fin 7) : ℕ :=
  ![![0, 1, 1, 2, 2, 1, 3],
    ![1, 0, 2, 3, 1, 2, 4],
    ![1, 2, 0, 1, 3, 2, 2],
    ![2, 3, 1, 0, 4, 1, 1],
    ![2, 1, 3, 4, 0, 3, 5],
    ![1, 2, 2, 1, 3, 0, 2],
    ![3, 4, 2, 1, 5, 2, 0]] u v

private theorem cert_7_19 :
    (∀ x : Fin 7, D_7_19 x x = 0) ∧
    (∀ x y : Fin 7, D_7_19 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_19 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 19).Adj x z ∧ D_7_19 z y + 1 = D_7_19 x y) ∧
    (∀ u v w : Fin 7, (reps 7 19).Adj u v → D_7_19 u w ≤ D_7_19 v w + 1) := by
  decide +kernel

theorem classify_7_19 : ¬ Challenge.IsMedian (reps 7 19) ∨
    (Challenge.Question3' (reps 7 19) ∧ Challenge.Question4 (reps 7 19)) := by
  have hD : ∀ x y, (reps 7 19).dist x y = D_7_19 x y :=
    dist_eq_of_certificate (reps 7 19) D_7_19 cert_7_19.1 cert_7_19.2.1
      cert_7_19.2.2.1 cert_7_19.2.2.2
  have hc : (reps 7 19).Connected := connected_of_dist (reps 7 19) D_7_19 hD cert_7_19.2.1
  have hd : (reps 7 19).diam = 5 :=
    diam_eq_of_table (reps 7 19) D_7_19 hc hD 5
      (by decide +kernel) 4 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 19) = 10 :=
    triameter_eq_of_table (reps 7 19) D_7_19 hD 10
      (by decide +kernel) 0 4 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 19) D_7_19 hc hD 5 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 19) D_7_19 hD 5 10 hd ht (by decide +kernel)⟩

#print axioms classify_7_10
#print axioms classify_7_11
#print axioms classify_7_12
#print axioms classify_7_13
#print axioms classify_7_14
#print axioms classify_7_15
#print axioms classify_7_16
#print axioms classify_7_17
#print axioms classify_7_18
#print axioms classify_7_19

end CodexPaper4.SmallMedianClassificationBlock04
