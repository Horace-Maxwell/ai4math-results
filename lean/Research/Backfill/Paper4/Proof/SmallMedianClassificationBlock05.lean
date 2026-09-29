import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock05
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_7_20 (u v : Fin 7) : ℕ :=
  ![![0, 2, 1, 2, 2, 1, 2],
    ![2, 0, 1, 2, 4, 3, 3],
    ![1, 1, 0, 1, 3, 2, 2],
    ![2, 2, 1, 0, 3, 2, 1],
    ![2, 4, 3, 3, 0, 1, 2],
    ![1, 3, 2, 2, 1, 0, 1],
    ![2, 3, 2, 1, 2, 1, 0]] u v

private theorem cert_7_20 :
    (∀ x : Fin 7, D_7_20 x x = 0) ∧
    (∀ x y : Fin 7, D_7_20 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_20 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 20).Adj x z ∧ D_7_20 z y + 1 = D_7_20 x y) ∧
    (∀ u v w : Fin 7, (reps 7 20).Adj u v → D_7_20 u w ≤ D_7_20 v w + 1) := by
  decide +kernel

theorem classify_7_20 : ¬ Challenge.IsMedian (reps 7 20) ∨
    (Challenge.Question3' (reps 7 20) ∧ Challenge.Question4 (reps 7 20)) := by
  have hD : ∀ x y, (reps 7 20).dist x y = D_7_20 x y :=
    dist_eq_of_certificate (reps 7 20) D_7_20 cert_7_20.1 cert_7_20.2.1
      cert_7_20.2.2.1 cert_7_20.2.2.2
  have hc : (reps 7 20).Connected := connected_of_dist (reps 7 20) D_7_20 hD cert_7_20.2.1
  have hd : (reps 7 20).diam = 4 :=
    diam_eq_of_table (reps 7 20) D_7_20 hc hD 4
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 20) = 9 :=
    triameter_eq_of_table (reps 7 20) D_7_20 hD 9
      (by decide +kernel) 1 3 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 20) D_7_20 hc hD 4 9 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 20) D_7_20 hD 4 9 hd ht (by decide +kernel)⟩

private def D_7_21 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 4, 4],
    ![2, 0, 1, 1, 1, 2, 2],
    ![3, 1, 0, 2, 2, 1, 1],
    ![1, 1, 2, 0, 2, 3, 3],
    ![1, 1, 2, 2, 0, 3, 3],
    ![4, 2, 1, 3, 3, 0, 2],
    ![4, 2, 1, 3, 3, 2, 0]] u v

private theorem cert_7_21 :
    (∀ x : Fin 7, D_7_21 x x = 0) ∧
    (∀ x y : Fin 7, D_7_21 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_21 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 21).Adj x z ∧ D_7_21 z y + 1 = D_7_21 x y) ∧
    (∀ u v w : Fin 7, (reps 7 21).Adj u v → D_7_21 u w ≤ D_7_21 v w + 1) := by
  decide +kernel

theorem classify_7_21 : ¬ Challenge.IsMedian (reps 7 21) ∨
    (Challenge.Question3' (reps 7 21) ∧ Challenge.Question4 (reps 7 21)) := by
  have hD : ∀ x y, (reps 7 21).dist x y = D_7_21 x y :=
    dist_eq_of_certificate (reps 7 21) D_7_21 cert_7_21.1 cert_7_21.2.1
      cert_7_21.2.2.1 cert_7_21.2.2.2
  have hc : (reps 7 21).Connected := connected_of_dist (reps 7 21) D_7_21 hD cert_7_21.2.1
  have hd : (reps 7 21).diam = 4 :=
    diam_eq_of_table (reps 7 21) D_7_21 hc hD 4
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 21) = 10 :=
    triameter_eq_of_table (reps 7 21) D_7_21 hD 10
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 21) D_7_21 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 21) D_7_21 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_22 (u v : Fin 7) : ℕ :=
  ![![0, 4, 3, 1, 1, 2, 2],
    ![4, 0, 1, 3, 3, 2, 2],
    ![3, 1, 0, 2, 2, 1, 1],
    ![1, 3, 2, 0, 2, 3, 1],
    ![1, 3, 2, 2, 0, 1, 3],
    ![2, 2, 1, 3, 1, 0, 2],
    ![2, 2, 1, 1, 3, 2, 0]] u v

private theorem cert_7_22 :
    (∀ x : Fin 7, D_7_22 x x = 0) ∧
    (∀ x y : Fin 7, D_7_22 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_22 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 22).Adj x z ∧ D_7_22 z y + 1 = D_7_22 x y) ∧
    (∀ u v w : Fin 7, (reps 7 22).Adj u v → D_7_22 u w ≤ D_7_22 v w + 1) := by
  decide +kernel

theorem classify_7_22 : ¬ Challenge.IsMedian (reps 7 22) ∨
    (Challenge.Question3' (reps 7 22) ∧ Challenge.Question4 (reps 7 22)) := by
  have hD : ∀ x y, (reps 7 22).dist x y = D_7_22 x y :=
    dist_eq_of_certificate (reps 7 22) D_7_22 cert_7_22.1 cert_7_22.2.1
      cert_7_22.2.2.1 cert_7_22.2.2.2
  have hc : (reps 7 22).Connected := connected_of_dist (reps 7 22) D_7_22 hD cert_7_22.2.1
  have hd : (reps 7 22).diam = 4 :=
    diam_eq_of_table (reps 7 22) D_7_22 hc hD 4
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 22) = 8 :=
    triameter_eq_of_table (reps 7 22) D_7_22 hD 8
      (by decide +kernel) 0 0 1 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 22) D_7_22 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 22) D_7_22 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_23 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 1, 1, 5, 4],
    ![2, 0, 1, 1, 1, 3, 2],
    ![3, 1, 0, 2, 2, 2, 1],
    ![1, 1, 2, 0, 2, 4, 3],
    ![1, 1, 2, 2, 0, 4, 3],
    ![5, 3, 2, 4, 4, 0, 1],
    ![4, 2, 1, 3, 3, 1, 0]] u v

private theorem cert_7_23 :
    (∀ x : Fin 7, D_7_23 x x = 0) ∧
    (∀ x y : Fin 7, D_7_23 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_23 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 23).Adj x z ∧ D_7_23 z y + 1 = D_7_23 x y) ∧
    (∀ u v w : Fin 7, (reps 7 23).Adj u v → D_7_23 u w ≤ D_7_23 v w + 1) := by
  decide +kernel

theorem classify_7_23 : ¬ Challenge.IsMedian (reps 7 23) ∨
    (Challenge.Question3' (reps 7 23) ∧ Challenge.Question4 (reps 7 23)) := by
  have hD : ∀ x y, (reps 7 23).dist x y = D_7_23 x y :=
    dist_eq_of_certificate (reps 7 23) D_7_23 cert_7_23.1 cert_7_23.2.1
      cert_7_23.2.2.1 cert_7_23.2.2.2
  have hc : (reps 7 23).Connected := connected_of_dist (reps 7 23) D_7_23 hD cert_7_23.2.1
  have hd : (reps 7 23).diam = 5 :=
    diam_eq_of_table (reps 7 23) D_7_23 hc hD 5
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 23) = 10 :=
    triameter_eq_of_table (reps 7 23) D_7_23 hD 10
      (by decide +kernel) 0 0 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 23) D_7_23 hc hD 5 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 23) D_7_23 hD 5 10 hd ht (by decide +kernel)⟩

private def D_7_24 (u v : Fin 7) : ℕ :=
  ![![0, 2, 1, 2, 1, 1, 2],
    ![2, 0, 3, 4, 1, 3, 4],
    ![1, 3, 0, 1, 2, 2, 2],
    ![2, 4, 1, 0, 3, 2, 1],
    ![1, 1, 2, 3, 0, 2, 3],
    ![1, 3, 2, 2, 2, 0, 1],
    ![2, 4, 2, 1, 3, 1, 0]] u v

private theorem cert_7_24 :
    (∀ x : Fin 7, D_7_24 x x = 0) ∧
    (∀ x y : Fin 7, D_7_24 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_24 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 24).Adj x z ∧ D_7_24 z y + 1 = D_7_24 x y) ∧
    (∀ u v w : Fin 7, (reps 7 24).Adj u v → D_7_24 u w ≤ D_7_24 v w + 1) := by
  decide +kernel

theorem classify_7_24 : ¬ Challenge.IsMedian (reps 7 24) ∨
    (Challenge.Question3' (reps 7 24) ∧ Challenge.Question4 (reps 7 24)) := by
  have hD : ∀ x y, (reps 7 24).dist x y = D_7_24 x y :=
    dist_eq_of_certificate (reps 7 24) D_7_24 cert_7_24.1 cert_7_24.2.1
      cert_7_24.2.2.1 cert_7_24.2.2.2
  have hc : (reps 7 24).Connected := connected_of_dist (reps 7 24) D_7_24 hD cert_7_24.2.1
  have hd : (reps 7 24).diam = 4 :=
    diam_eq_of_table (reps 7 24) D_7_24 hc hD 4
      (by decide +kernel) 1 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 24) = 9 :=
    triameter_eq_of_table (reps 7 24) D_7_24 hD 9
      (by decide +kernel) 1 2 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 24) D_7_24 hc hD 4 9 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 24) D_7_24 hD 4 9 hd ht (by decide +kernel)⟩

private def D_7_25 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 3, 2, 1],
    ![1, 0, 1, 2, 3, 3, 2],
    ![2, 1, 0, 1, 2, 3, 3],
    ![3, 2, 1, 0, 1, 2, 3],
    ![3, 3, 2, 1, 0, 1, 2],
    ![2, 3, 3, 2, 1, 0, 1],
    ![1, 2, 3, 3, 2, 1, 0]] u v

private theorem cert_7_25 :
    (∀ x : Fin 7, D_7_25 x x = 0) ∧
    (∀ x y : Fin 7, D_7_25 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_25 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 25).Adj x z ∧ D_7_25 z y + 1 = D_7_25 x y) ∧
    (∀ u v w : Fin 7, (reps 7 25).Adj u v → D_7_25 u w ≤ D_7_25 v w + 1) := by
  decide +kernel

theorem classify_7_25 : ¬ Challenge.IsMedian (reps 7 25) ∨
    (Challenge.Question3' (reps 7 25) ∧ Challenge.Question4 (reps 7 25)) := by
  have hD : ∀ x y, (reps 7 25).dist x y = D_7_25 x y :=
    dist_eq_of_certificate (reps 7 25) D_7_25 cert_7_25.1 cert_7_25.2.1
      cert_7_25.2.2.1 cert_7_25.2.2.2
  have hc : (reps 7 25).Connected := connected_of_dist (reps 7 25) D_7_25 hD cert_7_25.2.1
  have hd : (reps 7 25).diam = 3 :=
    diam_eq_of_table (reps 7 25) D_7_25 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 25) = 7 :=
    triameter_eq_of_table (reps 7 25) D_7_25 hD 7
      (by decide +kernel) 0 1 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 25) D_7_25 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 25) D_7_25 hD 3 7 hd ht (by decide +kernel)⟩

private def D_7_26 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 1, 1, 3, 3],
    ![1, 0, 1, 2, 2, 2, 2],
    ![2, 1, 0, 1, 1, 1, 1],
    ![1, 2, 1, 0, 2, 2, 2],
    ![1, 2, 1, 2, 0, 2, 2],
    ![3, 2, 1, 2, 2, 0, 2],
    ![3, 2, 1, 2, 2, 2, 0]] u v

private theorem cert_7_26 :
    (∀ x : Fin 7, D_7_26 x x = 0) ∧
    (∀ x y : Fin 7, D_7_26 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_26 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 26).Adj x z ∧ D_7_26 z y + 1 = D_7_26 x y) ∧
    (∀ u v w : Fin 7, (reps 7 26).Adj u v → D_7_26 u w ≤ D_7_26 v w + 1) := by
  decide +kernel

theorem classify_7_26 : ¬ Challenge.IsMedian (reps 7 26) ∨
    (Challenge.Question3' (reps 7 26) ∧ Challenge.Question4 (reps 7 26)) := by
  have hD : ∀ x y, (reps 7 26).dist x y = D_7_26 x y :=
    dist_eq_of_certificate (reps 7 26) D_7_26 cert_7_26.1 cert_7_26.2.1
      cert_7_26.2.2.1 cert_7_26.2.2.2
  have hc : (reps 7 26).Connected := connected_of_dist (reps 7 26) D_7_26 hD cert_7_26.2.1
  have hd : (reps 7 26).diam = 3 :=
    diam_eq_of_table (reps 7 26) D_7_26 hc hD 3
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 26) = 8 :=
    triameter_eq_of_table (reps 7 26) D_7_26 hD 8
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 26) D_7_26 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 26) D_7_26 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_27 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 2, 2],
    ![2, 0, 2, 1, 1, 2, 2],
    ![2, 2, 0, 1, 1, 2, 2],
    ![1, 1, 1, 0, 2, 3, 1],
    ![1, 1, 1, 2, 0, 1, 3],
    ![2, 2, 2, 3, 1, 0, 4],
    ![2, 2, 2, 1, 3, 4, 0]] u v

private theorem cert_7_27 :
    (∀ x : Fin 7, D_7_27 x x = 0) ∧
    (∀ x y : Fin 7, D_7_27 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_27 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 27).Adj x z ∧ D_7_27 z y + 1 = D_7_27 x y) ∧
    (∀ u v w : Fin 7, (reps 7 27).Adj u v → D_7_27 u w ≤ D_7_27 v w + 1) := by
  decide +kernel

theorem classify_7_27 : ¬ Challenge.IsMedian (reps 7 27) ∨
    (Challenge.Question3' (reps 7 27) ∧ Challenge.Question4 (reps 7 27)) := by
  have hD : ∀ x y, (reps 7 27).dist x y = D_7_27 x y :=
    dist_eq_of_certificate (reps 7 27) D_7_27 cert_7_27.1 cert_7_27.2.1
      cert_7_27.2.2.1 cert_7_27.2.2.2
  have hc : (reps 7 27).Connected := connected_of_dist (reps 7 27) D_7_27 hD cert_7_27.2.1
  have hd : (reps 7 27).diam = 4 :=
    diam_eq_of_table (reps 7 27) D_7_27 hc hD 4
      (by decide +kernel) 5 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 27) = 8 :=
    triameter_eq_of_table (reps 7 27) D_7_27 hD 8
      (by decide +kernel) 0 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 27) D_7_27 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 27) D_7_27 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_28 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 2, 3],
    ![2, 0, 2, 1, 1, 2, 3],
    ![2, 2, 0, 1, 1, 2, 1],
    ![1, 1, 1, 0, 2, 3, 2],
    ![1, 1, 1, 2, 0, 1, 2],
    ![2, 2, 2, 3, 1, 0, 3],
    ![3, 3, 1, 2, 2, 3, 0]] u v

private theorem cert_7_28 :
    (∀ x : Fin 7, D_7_28 x x = 0) ∧
    (∀ x y : Fin 7, D_7_28 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_28 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 28).Adj x z ∧ D_7_28 z y + 1 = D_7_28 x y) ∧
    (∀ u v w : Fin 7, (reps 7 28).Adj u v → D_7_28 u w ≤ D_7_28 v w + 1) := by
  decide +kernel

theorem classify_7_28 : ¬ Challenge.IsMedian (reps 7 28) ∨
    (Challenge.Question3' (reps 7 28) ∧ Challenge.Question4 (reps 7 28)) := by
  have hD : ∀ x y, (reps 7 28).dist x y = D_7_28 x y :=
    dist_eq_of_certificate (reps 7 28) D_7_28 cert_7_28.1 cert_7_28.2.1
      cert_7_28.2.2.1 cert_7_28.2.2.2
  have hc : (reps 7 28).Connected := connected_of_dist (reps 7 28) D_7_28 hD cert_7_28.2.1
  have hd : (reps 7 28).diam = 3 :=
    diam_eq_of_table (reps 7 28) D_7_28 hc hD 3
      (by decide +kernel) 0 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 28) = 8 :=
    triameter_eq_of_table (reps 7 28) D_7_28 hD 8
      (by decide +kernel) 0 1 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 28) D_7_28 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 28) D_7_28 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_29 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 3, 3],
    ![2, 0, 2, 1, 1, 3, 3],
    ![2, 2, 0, 1, 1, 1, 1],
    ![1, 1, 1, 0, 2, 2, 2],
    ![1, 1, 1, 2, 0, 2, 2],
    ![3, 3, 1, 2, 2, 0, 2],
    ![3, 3, 1, 2, 2, 2, 0]] u v

private theorem cert_7_29 :
    (∀ x : Fin 7, D_7_29 x x = 0) ∧
    (∀ x y : Fin 7, D_7_29 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_29 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 29).Adj x z ∧ D_7_29 z y + 1 = D_7_29 x y) ∧
    (∀ u v w : Fin 7, (reps 7 29).Adj u v → D_7_29 u w ≤ D_7_29 v w + 1) := by
  decide +kernel

theorem classify_7_29 : ¬ Challenge.IsMedian (reps 7 29) ∨
    (Challenge.Question3' (reps 7 29) ∧ Challenge.Question4 (reps 7 29)) := by
  have hD : ∀ x y, (reps 7 29).dist x y = D_7_29 x y :=
    dist_eq_of_certificate (reps 7 29) D_7_29 cert_7_29.1 cert_7_29.2.1
      cert_7_29.2.2.1 cert_7_29.2.2.2
  have hc : (reps 7 29).Connected := connected_of_dist (reps 7 29) D_7_29 hD cert_7_29.2.1
  have hd : (reps 7 29).diam = 3 :=
    diam_eq_of_table (reps 7 29) D_7_29 hc hD 3
      (by decide +kernel) 0 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 29) = 8 :=
    triameter_eq_of_table (reps 7 29) D_7_29 hD 8
      (by decide +kernel) 0 1 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 29) D_7_29 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 29) D_7_29 hD 3 8 hd ht (by decide +kernel)⟩

#print axioms classify_7_20
#print axioms classify_7_21
#print axioms classify_7_22
#print axioms classify_7_23
#print axioms classify_7_24
#print axioms classify_7_25
#print axioms classify_7_26
#print axioms classify_7_27
#print axioms classify_7_28
#print axioms classify_7_29

end CodexPaper4.SmallMedianClassificationBlock05
