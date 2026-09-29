import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock00
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_1_00 (u v : Fin 1) : ℕ :=
  ![![0]] u v

private theorem cert_1_00 :
    (∀ x : Fin 1, D_1_00 x x = 0) ∧
    (∀ x y : Fin 1, D_1_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 1, D_1_00 x y ≠ 0 →
      ∃ z : Fin 1, (reps 1 0).Adj x z ∧ D_1_00 z y + 1 = D_1_00 x y) ∧
    (∀ u v w : Fin 1, (reps 1 0).Adj u v → D_1_00 u w ≤ D_1_00 v w + 1) := by
  decide +kernel

theorem classify_1_00 : ¬ Challenge.IsMedian (reps 1 0) ∨
    (Challenge.Question3' (reps 1 0) ∧ Challenge.Question4 (reps 1 0)) := by
  have hD : ∀ x y, (reps 1 0).dist x y = D_1_00 x y :=
    dist_eq_of_certificate (reps 1 0) D_1_00 cert_1_00.1 cert_1_00.2.1
      cert_1_00.2.2.1 cert_1_00.2.2.2
  have hc : (reps 1 0).Connected := connected_of_dist (reps 1 0) D_1_00 hD cert_1_00.2.1
  have hd : (reps 1 0).diam = 0 :=
    diam_eq_of_table (reps 1 0) D_1_00 hc hD 0
      (by decide +kernel) 0 0 (by decide +kernel)
  have ht : Challenge.triameter (reps 1 0) = 0 :=
    triameter_eq_of_table (reps 1 0) D_1_00 hD 0
      (by decide +kernel) 0 0 0 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 1 0) D_1_00 hc hD 0 0 hd ht
      (by decide +kernel),
    question4_of_table (reps 1 0) D_1_00 hD 0 0 hd ht (by decide +kernel)⟩

private def D_2_00 (u v : Fin 2) : ℕ :=
  ![![0, 1],
    ![1, 0]] u v

private theorem cert_2_00 :
    (∀ x : Fin 2, D_2_00 x x = 0) ∧
    (∀ x y : Fin 2, D_2_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 2, D_2_00 x y ≠ 0 →
      ∃ z : Fin 2, (reps 2 0).Adj x z ∧ D_2_00 z y + 1 = D_2_00 x y) ∧
    (∀ u v w : Fin 2, (reps 2 0).Adj u v → D_2_00 u w ≤ D_2_00 v w + 1) := by
  decide +kernel

theorem classify_2_00 : ¬ Challenge.IsMedian (reps 2 0) ∨
    (Challenge.Question3' (reps 2 0) ∧ Challenge.Question4 (reps 2 0)) := by
  have hD : ∀ x y, (reps 2 0).dist x y = D_2_00 x y :=
    dist_eq_of_certificate (reps 2 0) D_2_00 cert_2_00.1 cert_2_00.2.1
      cert_2_00.2.2.1 cert_2_00.2.2.2
  have hc : (reps 2 0).Connected := connected_of_dist (reps 2 0) D_2_00 hD cert_2_00.2.1
  have hd : (reps 2 0).diam = 1 :=
    diam_eq_of_table (reps 2 0) D_2_00 hc hD 1
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 2 0) = 2 :=
    triameter_eq_of_table (reps 2 0) D_2_00 hD 2
      (by decide +kernel) 0 0 1 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 2 0) D_2_00 hc hD 1 2 hd ht
      (by decide +kernel),
    question4_of_table (reps 2 0) D_2_00 hD 1 2 hd ht (by decide +kernel)⟩

private def D_3_00 (u v : Fin 3) : ℕ :=
  ![![0, 1, 1],
    ![1, 0, 2],
    ![1, 2, 0]] u v

private theorem cert_3_00 :
    (∀ x : Fin 3, D_3_00 x x = 0) ∧
    (∀ x y : Fin 3, D_3_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 3, D_3_00 x y ≠ 0 →
      ∃ z : Fin 3, (reps 3 0).Adj x z ∧ D_3_00 z y + 1 = D_3_00 x y) ∧
    (∀ u v w : Fin 3, (reps 3 0).Adj u v → D_3_00 u w ≤ D_3_00 v w + 1) := by
  decide +kernel

theorem classify_3_00 : ¬ Challenge.IsMedian (reps 3 0) ∨
    (Challenge.Question3' (reps 3 0) ∧ Challenge.Question4 (reps 3 0)) := by
  have hD : ∀ x y, (reps 3 0).dist x y = D_3_00 x y :=
    dist_eq_of_certificate (reps 3 0) D_3_00 cert_3_00.1 cert_3_00.2.1
      cert_3_00.2.2.1 cert_3_00.2.2.2
  have hc : (reps 3 0).Connected := connected_of_dist (reps 3 0) D_3_00 hD cert_3_00.2.1
  have hd : (reps 3 0).diam = 2 :=
    diam_eq_of_table (reps 3 0) D_3_00 hc hD 2
      (by decide +kernel) 1 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 3 0) = 4 :=
    triameter_eq_of_table (reps 3 0) D_3_00 hD 4
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 3 0) D_3_00 hc hD 2 4 hd ht
      (by decide +kernel),
    question4_of_table (reps 3 0) D_3_00 hD 2 4 hd ht (by decide +kernel)⟩

private def D_4_00 (u v : Fin 4) : ℕ :=
  ![![0, 2, 2, 1],
    ![2, 0, 2, 1],
    ![2, 2, 0, 1],
    ![1, 1, 1, 0]] u v

private theorem cert_4_00 :
    (∀ x : Fin 4, D_4_00 x x = 0) ∧
    (∀ x y : Fin 4, D_4_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 4, D_4_00 x y ≠ 0 →
      ∃ z : Fin 4, (reps 4 0).Adj x z ∧ D_4_00 z y + 1 = D_4_00 x y) ∧
    (∀ u v w : Fin 4, (reps 4 0).Adj u v → D_4_00 u w ≤ D_4_00 v w + 1) := by
  decide +kernel

theorem classify_4_00 : ¬ Challenge.IsMedian (reps 4 0) ∨
    (Challenge.Question3' (reps 4 0) ∧ Challenge.Question4 (reps 4 0)) := by
  have hD : ∀ x y, (reps 4 0).dist x y = D_4_00 x y :=
    dist_eq_of_certificate (reps 4 0) D_4_00 cert_4_00.1 cert_4_00.2.1
      cert_4_00.2.2.1 cert_4_00.2.2.2
  have hc : (reps 4 0).Connected := connected_of_dist (reps 4 0) D_4_00 hD cert_4_00.2.1
  have hd : (reps 4 0).diam = 2 :=
    diam_eq_of_table (reps 4 0) D_4_00 hc hD 2
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 4 0) = 6 :=
    triameter_eq_of_table (reps 4 0) D_4_00 hD 6
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 4 0) D_4_00 hc hD 2 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 4 0) D_4_00 hD 2 6 hd ht (by decide +kernel)⟩

private def D_4_01 (u v : Fin 4) : ℕ :=
  ![![0, 1, 2, 1],
    ![1, 0, 1, 2],
    ![2, 1, 0, 3],
    ![1, 2, 3, 0]] u v

private theorem cert_4_01 :
    (∀ x : Fin 4, D_4_01 x x = 0) ∧
    (∀ x y : Fin 4, D_4_01 x y = 0 → x = y) ∧
    (∀ x y : Fin 4, D_4_01 x y ≠ 0 →
      ∃ z : Fin 4, (reps 4 1).Adj x z ∧ D_4_01 z y + 1 = D_4_01 x y) ∧
    (∀ u v w : Fin 4, (reps 4 1).Adj u v → D_4_01 u w ≤ D_4_01 v w + 1) := by
  decide +kernel

theorem classify_4_01 : ¬ Challenge.IsMedian (reps 4 1) ∨
    (Challenge.Question3' (reps 4 1) ∧ Challenge.Question4 (reps 4 1)) := by
  have hD : ∀ x y, (reps 4 1).dist x y = D_4_01 x y :=
    dist_eq_of_certificate (reps 4 1) D_4_01 cert_4_01.1 cert_4_01.2.1
      cert_4_01.2.2.1 cert_4_01.2.2.2
  have hc : (reps 4 1).Connected := connected_of_dist (reps 4 1) D_4_01 hD cert_4_01.2.1
  have hd : (reps 4 1).diam = 3 :=
    diam_eq_of_table (reps 4 1) D_4_01 hc hD 3
      (by decide +kernel) 2 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 4 1) = 6 :=
    triameter_eq_of_table (reps 4 1) D_4_01 hD 6
      (by decide +kernel) 0 2 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 4 1) D_4_01 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 4 1) D_4_01 hD 3 6 hd ht (by decide +kernel)⟩

private def D_4_02 (u v : Fin 4) : ℕ :=
  ![![0, 1, 2, 1],
    ![1, 0, 1, 2],
    ![2, 1, 0, 1],
    ![1, 2, 1, 0]] u v

private theorem cert_4_02 :
    (∀ x : Fin 4, D_4_02 x x = 0) ∧
    (∀ x y : Fin 4, D_4_02 x y = 0 → x = y) ∧
    (∀ x y : Fin 4, D_4_02 x y ≠ 0 →
      ∃ z : Fin 4, (reps 4 2).Adj x z ∧ D_4_02 z y + 1 = D_4_02 x y) ∧
    (∀ u v w : Fin 4, (reps 4 2).Adj u v → D_4_02 u w ≤ D_4_02 v w + 1) := by
  decide +kernel

theorem classify_4_02 : ¬ Challenge.IsMedian (reps 4 2) ∨
    (Challenge.Question3' (reps 4 2) ∧ Challenge.Question4 (reps 4 2)) := by
  have hD : ∀ x y, (reps 4 2).dist x y = D_4_02 x y :=
    dist_eq_of_certificate (reps 4 2) D_4_02 cert_4_02.1 cert_4_02.2.1
      cert_4_02.2.2.1 cert_4_02.2.2.2
  have hc : (reps 4 2).Connected := connected_of_dist (reps 4 2) D_4_02 hD cert_4_02.2.1
  have hd : (reps 4 2).diam = 2 :=
    diam_eq_of_table (reps 4 2) D_4_02 hc hD 2
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 4 2) = 4 :=
    triameter_eq_of_table (reps 4 2) D_4_02 hD 4
      (by decide +kernel) 0 0 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 4 2) D_4_02 hc hD 2 4 hd ht
      (by decide +kernel),
    question4_of_table (reps 4 2) D_4_02 hD 2 4 hd ht (by decide +kernel)⟩

private def D_5_00 (u v : Fin 5) : ℕ :=
  ![![0, 2, 2, 2, 1],
    ![2, 0, 2, 2, 1],
    ![2, 2, 0, 2, 1],
    ![2, 2, 2, 0, 1],
    ![1, 1, 1, 1, 0]] u v

private theorem cert_5_00 :
    (∀ x : Fin 5, D_5_00 x x = 0) ∧
    (∀ x y : Fin 5, D_5_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_00 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 0).Adj x z ∧ D_5_00 z y + 1 = D_5_00 x y) ∧
    (∀ u v w : Fin 5, (reps 5 0).Adj u v → D_5_00 u w ≤ D_5_00 v w + 1) := by
  decide +kernel

theorem classify_5_00 : ¬ Challenge.IsMedian (reps 5 0) ∨
    (Challenge.Question3' (reps 5 0) ∧ Challenge.Question4 (reps 5 0)) := by
  have hD : ∀ x y, (reps 5 0).dist x y = D_5_00 x y :=
    dist_eq_of_certificate (reps 5 0) D_5_00 cert_5_00.1 cert_5_00.2.1
      cert_5_00.2.2.1 cert_5_00.2.2.2
  have hc : (reps 5 0).Connected := connected_of_dist (reps 5 0) D_5_00 hD cert_5_00.2.1
  have hd : (reps 5 0).diam = 2 :=
    diam_eq_of_table (reps 5 0) D_5_00 hc hD 2
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 5 0) = 6 :=
    triameter_eq_of_table (reps 5 0) D_5_00 hD 6
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 5 0) D_5_00 hc hD 2 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 5 0) D_5_00 hD 2 6 hd ht (by decide +kernel)⟩

private def D_5_01 (u v : Fin 5) : ℕ :=
  ![![0, 3, 3, 2, 1],
    ![3, 0, 2, 1, 2],
    ![3, 2, 0, 1, 2],
    ![2, 1, 1, 0, 1],
    ![1, 2, 2, 1, 0]] u v

private theorem cert_5_01 :
    (∀ x : Fin 5, D_5_01 x x = 0) ∧
    (∀ x y : Fin 5, D_5_01 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_01 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 1).Adj x z ∧ D_5_01 z y + 1 = D_5_01 x y) ∧
    (∀ u v w : Fin 5, (reps 5 1).Adj u v → D_5_01 u w ≤ D_5_01 v w + 1) := by
  decide +kernel

theorem classify_5_01 : ¬ Challenge.IsMedian (reps 5 1) ∨
    (Challenge.Question3' (reps 5 1) ∧ Challenge.Question4 (reps 5 1)) := by
  have hD : ∀ x y, (reps 5 1).dist x y = D_5_01 x y :=
    dist_eq_of_certificate (reps 5 1) D_5_01 cert_5_01.1 cert_5_01.2.1
      cert_5_01.2.2.1 cert_5_01.2.2.2
  have hc : (reps 5 1).Connected := connected_of_dist (reps 5 1) D_5_01 hD cert_5_01.2.1
  have hd : (reps 5 1).diam = 3 :=
    diam_eq_of_table (reps 5 1) D_5_01 hc hD 3
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 5 1) = 8 :=
    triameter_eq_of_table (reps 5 1) D_5_01 hD 8
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 5 1) D_5_01 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 5 1) D_5_01 hD 3 8 hd ht (by decide +kernel)⟩

private def D_5_02 (u v : Fin 5) : ℕ :=
  ![![0, 1, 2, 3, 1],
    ![1, 0, 1, 2, 2],
    ![2, 1, 0, 1, 3],
    ![3, 2, 1, 0, 4],
    ![1, 2, 3, 4, 0]] u v

private theorem cert_5_02 :
    (∀ x : Fin 5, D_5_02 x x = 0) ∧
    (∀ x y : Fin 5, D_5_02 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_02 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 2).Adj x z ∧ D_5_02 z y + 1 = D_5_02 x y) ∧
    (∀ u v w : Fin 5, (reps 5 2).Adj u v → D_5_02 u w ≤ D_5_02 v w + 1) := by
  decide +kernel

theorem classify_5_02 : ¬ Challenge.IsMedian (reps 5 2) ∨
    (Challenge.Question3' (reps 5 2) ∧ Challenge.Question4 (reps 5 2)) := by
  have hD : ∀ x y, (reps 5 2).dist x y = D_5_02 x y :=
    dist_eq_of_certificate (reps 5 2) D_5_02 cert_5_02.1 cert_5_02.2.1
      cert_5_02.2.2.1 cert_5_02.2.2.2
  have hc : (reps 5 2).Connected := connected_of_dist (reps 5 2) D_5_02 hD cert_5_02.2.1
  have hd : (reps 5 2).diam = 4 :=
    diam_eq_of_table (reps 5 2) D_5_02 hc hD 4
      (by decide +kernel) 3 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 5 2) = 8 :=
    triameter_eq_of_table (reps 5 2) D_5_02 hD 8
      (by decide +kernel) 0 3 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 5 2) D_5_02 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 5 2) D_5_02 hD 4 8 hd ht (by decide +kernel)⟩

private def D_5_03 (u v : Fin 5) : ℕ :=
  ![![0, 1, 3, 2, 2],
    ![1, 0, 2, 1, 1],
    ![3, 2, 0, 1, 1],
    ![2, 1, 1, 0, 2],
    ![2, 1, 1, 2, 0]] u v

private theorem cert_5_03 :
    (∀ x : Fin 5, D_5_03 x x = 0) ∧
    (∀ x y : Fin 5, D_5_03 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_03 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 3).Adj x z ∧ D_5_03 z y + 1 = D_5_03 x y) ∧
    (∀ u v w : Fin 5, (reps 5 3).Adj u v → D_5_03 u w ≤ D_5_03 v w + 1) := by
  decide +kernel

theorem classify_5_03 : ¬ Challenge.IsMedian (reps 5 3) ∨
    (Challenge.Question3' (reps 5 3) ∧ Challenge.Question4 (reps 5 3)) := by
  have hD : ∀ x y, (reps 5 3).dist x y = D_5_03 x y :=
    dist_eq_of_certificate (reps 5 3) D_5_03 cert_5_03.1 cert_5_03.2.1
      cert_5_03.2.2.1 cert_5_03.2.2.2
  have hc : (reps 5 3).Connected := connected_of_dist (reps 5 3) D_5_03 hD cert_5_03.2.1
  have hd : (reps 5 3).diam = 3 :=
    diam_eq_of_table (reps 5 3) D_5_03 hc hD 3
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 5 3) = 6 :=
    triameter_eq_of_table (reps 5 3) D_5_03 hD 6
      (by decide +kernel) 0 0 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 5 3) D_5_03 hc hD 3 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 5 3) D_5_03 hD 3 6 hd ht (by decide +kernel)⟩

private def D_5_04 (u v : Fin 5) : ℕ :=
  ![![0, 1, 2, 2, 1],
    ![1, 0, 1, 2, 2],
    ![2, 1, 0, 1, 2],
    ![2, 2, 1, 0, 1],
    ![1, 2, 2, 1, 0]] u v

private theorem cert_5_04 :
    (∀ x : Fin 5, D_5_04 x x = 0) ∧
    (∀ x y : Fin 5, D_5_04 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_04 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 4).Adj x z ∧ D_5_04 z y + 1 = D_5_04 x y) ∧
    (∀ u v w : Fin 5, (reps 5 4).Adj u v → D_5_04 u w ≤ D_5_04 v w + 1) := by
  decide +kernel

theorem classify_5_04 : ¬ Challenge.IsMedian (reps 5 4) ∨
    (Challenge.Question3' (reps 5 4) ∧ Challenge.Question4 (reps 5 4)) := by
  have hD : ∀ x y, (reps 5 4).dist x y = D_5_04 x y :=
    dist_eq_of_certificate (reps 5 4) D_5_04 cert_5_04.1 cert_5_04.2.1
      cert_5_04.2.2.1 cert_5_04.2.2.2
  have hc : (reps 5 4).Connected := connected_of_dist (reps 5 4) D_5_04 hD cert_5_04.2.1
  have hd : (reps 5 4).diam = 2 :=
    diam_eq_of_table (reps 5 4) D_5_04 hc hD 2
      (by decide +kernel) 0 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 5 4) = 5 :=
    triameter_eq_of_table (reps 5 4) D_5_04 hD 5
      (by decide +kernel) 0 1 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 5 4) D_5_04 hc hD 2 5 hd ht
      (by decide +kernel),
    question4_of_table (reps 5 4) D_5_04 hD 2 5 hd ht (by decide +kernel)⟩

private def D_5_05 (u v : Fin 5) : ℕ :=
  ![![0, 2, 1, 1, 1],
    ![2, 0, 1, 1, 1],
    ![1, 1, 0, 2, 2],
    ![1, 1, 2, 0, 2],
    ![1, 1, 2, 2, 0]] u v

private theorem cert_5_05 :
    (∀ x : Fin 5, D_5_05 x x = 0) ∧
    (∀ x y : Fin 5, D_5_05 x y = 0 → x = y) ∧
    (∀ x y : Fin 5, D_5_05 x y ≠ 0 →
      ∃ z : Fin 5, (reps 5 5).Adj x z ∧ D_5_05 z y + 1 = D_5_05 x y) ∧
    (∀ u v w : Fin 5, (reps 5 5).Adj u v → D_5_05 u w ≤ D_5_05 v w + 1) := by
  decide +kernel

theorem classify_5_05 : ¬ Challenge.IsMedian (reps 5 5) ∨
    (Challenge.Question3' (reps 5 5) ∧ Challenge.Question4 (reps 5 5)) := by
  have hD : ∀ x y, (reps 5 5).dist x y = D_5_05 x y :=
    dist_eq_of_certificate (reps 5 5) D_5_05 cert_5_05.1 cert_5_05.2.1
      cert_5_05.2.2.1 cert_5_05.2.2.2
  exact Or.inl (not_median_of_two (reps 5 5) D_5_05 hD 2 3 4 0 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

#print axioms classify_1_00
#print axioms classify_2_00
#print axioms classify_3_00
#print axioms classify_4_00
#print axioms classify_4_01
#print axioms classify_4_02
#print axioms classify_5_00
#print axioms classify_5_01
#print axioms classify_5_02
#print axioms classify_5_03
#print axioms classify_5_04
#print axioms classify_5_05

end CodexPaper4.SmallMedianClassificationBlock00
