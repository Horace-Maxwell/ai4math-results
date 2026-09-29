import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock01
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_6_00 (u v : Fin 6) : ℕ :=
  ![![0, 2, 2, 2, 2, 1],
    ![2, 0, 2, 2, 2, 1],
    ![2, 2, 0, 2, 2, 1],
    ![2, 2, 2, 0, 2, 1],
    ![2, 2, 2, 2, 0, 1],
    ![1, 1, 1, 1, 1, 0]] u v

private theorem cert_6_00 :
    (∀ x : Fin 6, D_6_00 x x = 0) ∧
    (∀ x y : Fin 6, D_6_00 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_00 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 0).Adj x z ∧ D_6_00 z y + 1 = D_6_00 x y) ∧
    (∀ u v w : Fin 6, (reps 6 0).Adj u v → D_6_00 u w ≤ D_6_00 v w + 1) := by
  decide +kernel

theorem classify_6_00 : ¬ Challenge.IsMedian (reps 6 0) ∨
    (Challenge.Question3' (reps 6 0) ∧ Challenge.Question4 (reps 6 0)) := by
  have hD : ∀ x y, (reps 6 0).dist x y = D_6_00 x y :=
    dist_eq_of_certificate (reps 6 0) D_6_00 cert_6_00.1 cert_6_00.2.1
      cert_6_00.2.2.1 cert_6_00.2.2.2
  have hc : (reps 6 0).Connected := connected_of_dist (reps 6 0) D_6_00 hD cert_6_00.2.1
  have hd : (reps 6 0).diam = 2 :=
    diam_eq_of_table (reps 6 0) D_6_00 hc hD 2
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 0) = 6 :=
    triameter_eq_of_table (reps 6 0) D_6_00 hD 6
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 0) D_6_00 hc hD 2 6 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 0) D_6_00 hD 2 6 hd ht (by decide +kernel)⟩

private def D_6_01 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 3, 2, 2],
    ![1, 0, 1, 2, 1, 1],
    ![2, 1, 0, 1, 2, 2],
    ![3, 2, 1, 0, 3, 3],
    ![2, 1, 2, 3, 0, 2],
    ![2, 1, 2, 3, 2, 0]] u v

private theorem cert_6_01 :
    (∀ x : Fin 6, D_6_01 x x = 0) ∧
    (∀ x y : Fin 6, D_6_01 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_01 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 1).Adj x z ∧ D_6_01 z y + 1 = D_6_01 x y) ∧
    (∀ u v w : Fin 6, (reps 6 1).Adj u v → D_6_01 u w ≤ D_6_01 v w + 1) := by
  decide +kernel

theorem classify_6_01 : ¬ Challenge.IsMedian (reps 6 1) ∨
    (Challenge.Question3' (reps 6 1) ∧ Challenge.Question4 (reps 6 1)) := by
  have hD : ∀ x y, (reps 6 1).dist x y = D_6_01 x y :=
    dist_eq_of_certificate (reps 6 1) D_6_01 cert_6_01.1 cert_6_01.2.1
      cert_6_01.2.2.1 cert_6_01.2.2.2
  have hc : (reps 6 1).Connected := connected_of_dist (reps 6 1) D_6_01 hD cert_6_01.2.1
  have hd : (reps 6 1).diam = 3 :=
    diam_eq_of_table (reps 6 1) D_6_01 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 1) = 8 :=
    triameter_eq_of_table (reps 6 1) D_6_01 hD 8
      (by decide +kernel) 0 3 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 1) D_6_01 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 1) D_6_01 hD 3 8 hd ht (by decide +kernel)⟩

private def D_6_02 (u v : Fin 6) : ℕ :=
  ![![0, 1, 1, 1, 2, 2],
    ![1, 0, 2, 2, 3, 3],
    ![1, 2, 0, 2, 3, 3],
    ![1, 2, 2, 0, 1, 1],
    ![2, 3, 3, 1, 0, 2],
    ![2, 3, 3, 1, 2, 0]] u v

private theorem cert_6_02 :
    (∀ x : Fin 6, D_6_02 x x = 0) ∧
    (∀ x y : Fin 6, D_6_02 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_02 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 2).Adj x z ∧ D_6_02 z y + 1 = D_6_02 x y) ∧
    (∀ u v w : Fin 6, (reps 6 2).Adj u v → D_6_02 u w ≤ D_6_02 v w + 1) := by
  decide +kernel

theorem classify_6_02 : ¬ Challenge.IsMedian (reps 6 2) ∨
    (Challenge.Question3' (reps 6 2) ∧ Challenge.Question4 (reps 6 2)) := by
  have hD : ∀ x y, (reps 6 2).dist x y = D_6_02 x y :=
    dist_eq_of_certificate (reps 6 2) D_6_02 cert_6_02.1 cert_6_02.2.1
      cert_6_02.2.2.1 cert_6_02.2.2.2
  have hc : (reps 6 2).Connected := connected_of_dist (reps 6 2) D_6_02 hD cert_6_02.2.1
  have hd : (reps 6 2).diam = 3 :=
    diam_eq_of_table (reps 6 2) D_6_02 hc hD 3
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 2) = 8 :=
    triameter_eq_of_table (reps 6 2) D_6_02 hD 8
      (by decide +kernel) 1 2 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 2) D_6_02 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 2) D_6_02 hD 3 8 hd ht (by decide +kernel)⟩

private def D_6_03 (u v : Fin 6) : ℕ :=
  ![![0, 1, 2, 2, 3, 3],
    ![1, 0, 1, 1, 2, 2],
    ![2, 1, 0, 2, 1, 3],
    ![2, 1, 2, 0, 3, 1],
    ![3, 2, 1, 3, 0, 4],
    ![3, 2, 3, 1, 4, 0]] u v

private theorem cert_6_03 :
    (∀ x : Fin 6, D_6_03 x x = 0) ∧
    (∀ x y : Fin 6, D_6_03 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_03 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 3).Adj x z ∧ D_6_03 z y + 1 = D_6_03 x y) ∧
    (∀ u v w : Fin 6, (reps 6 3).Adj u v → D_6_03 u w ≤ D_6_03 v w + 1) := by
  decide +kernel

theorem classify_6_03 : ¬ Challenge.IsMedian (reps 6 3) ∨
    (Challenge.Question3' (reps 6 3) ∧ Challenge.Question4 (reps 6 3)) := by
  have hD : ∀ x y, (reps 6 3).dist x y = D_6_03 x y :=
    dist_eq_of_certificate (reps 6 3) D_6_03 cert_6_03.1 cert_6_03.2.1
      cert_6_03.2.2.1 cert_6_03.2.2.2
  have hc : (reps 6 3).Connected := connected_of_dist (reps 6 3) D_6_03 hD cert_6_03.2.1
  have hd : (reps 6 3).diam = 4 :=
    diam_eq_of_table (reps 6 3) D_6_03 hc hD 4
      (by decide +kernel) 4 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 3) = 10 :=
    triameter_eq_of_table (reps 6 3) D_6_03 hD 10
      (by decide +kernel) 0 4 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 3) D_6_03 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 3) D_6_03 hD 4 10 hd ht (by decide +kernel)⟩

private def D_6_04 (u v : Fin 6) : ℕ :=
  ![![0, 3, 3, 2, 1, 1],
    ![3, 0, 2, 1, 2, 4],
    ![3, 2, 0, 1, 2, 4],
    ![2, 1, 1, 0, 1, 3],
    ![1, 2, 2, 1, 0, 2],
    ![1, 4, 4, 3, 2, 0]] u v

private theorem cert_6_04 :
    (∀ x : Fin 6, D_6_04 x x = 0) ∧
    (∀ x y : Fin 6, D_6_04 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_04 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 4).Adj x z ∧ D_6_04 z y + 1 = D_6_04 x y) ∧
    (∀ u v w : Fin 6, (reps 6 4).Adj u v → D_6_04 u w ≤ D_6_04 v w + 1) := by
  decide +kernel

theorem classify_6_04 : ¬ Challenge.IsMedian (reps 6 4) ∨
    (Challenge.Question3' (reps 6 4) ∧ Challenge.Question4 (reps 6 4)) := by
  have hD : ∀ x y, (reps 6 4).dist x y = D_6_04 x y :=
    dist_eq_of_certificate (reps 6 4) D_6_04 cert_6_04.1 cert_6_04.2.1
      cert_6_04.2.2.1 cert_6_04.2.2.2
  have hc : (reps 6 4).Connected := connected_of_dist (reps 6 4) D_6_04 hD cert_6_04.2.1
  have hd : (reps 6 4).diam = 4 :=
    diam_eq_of_table (reps 6 4) D_6_04 hc hD 4
      (by decide +kernel) 1 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 4) = 10 :=
    triameter_eq_of_table (reps 6 4) D_6_04 hD 10
      (by decide +kernel) 1 2 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 4) D_6_04 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 4) D_6_04 hD 4 10 hd ht (by decide +kernel)⟩

private def D_6_05 (u v : Fin 6) : ℕ :=
  ![![0, 1, 4, 3, 2, 1],
    ![1, 0, 5, 4, 3, 2],
    ![4, 5, 0, 1, 2, 3],
    ![3, 4, 1, 0, 1, 2],
    ![2, 3, 2, 1, 0, 1],
    ![1, 2, 3, 2, 1, 0]] u v

private theorem cert_6_05 :
    (∀ x : Fin 6, D_6_05 x x = 0) ∧
    (∀ x y : Fin 6, D_6_05 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_05 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 5).Adj x z ∧ D_6_05 z y + 1 = D_6_05 x y) ∧
    (∀ u v w : Fin 6, (reps 6 5).Adj u v → D_6_05 u w ≤ D_6_05 v w + 1) := by
  decide +kernel

theorem classify_6_05 : ¬ Challenge.IsMedian (reps 6 5) ∨
    (Challenge.Question3' (reps 6 5) ∧ Challenge.Question4 (reps 6 5)) := by
  have hD : ∀ x y, (reps 6 5).dist x y = D_6_05 x y :=
    dist_eq_of_certificate (reps 6 5) D_6_05 cert_6_05.1 cert_6_05.2.1
      cert_6_05.2.2.1 cert_6_05.2.2.2
  have hc : (reps 6 5).Connected := connected_of_dist (reps 6 5) D_6_05 hD cert_6_05.2.1
  have hd : (reps 6 5).diam = 5 :=
    diam_eq_of_table (reps 6 5) D_6_05 hc hD 5
      (by decide +kernel) 1 2 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 5) = 10 :=
    triameter_eq_of_table (reps 6 5) D_6_05 hD 10
      (by decide +kernel) 0 1 2 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 5) D_6_05 hc hD 5 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 5) D_6_05 hD 5 10 hd ht (by decide +kernel)⟩

private def D_6_06 (u v : Fin 6) : ℕ :=
  ![![0, 2, 1, 1, 1, 1],
    ![2, 0, 1, 1, 3, 3],
    ![1, 1, 0, 2, 2, 2],
    ![1, 1, 2, 0, 2, 2],
    ![1, 3, 2, 2, 0, 2],
    ![1, 3, 2, 2, 2, 0]] u v

private theorem cert_6_06 :
    (∀ x : Fin 6, D_6_06 x x = 0) ∧
    (∀ x y : Fin 6, D_6_06 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_06 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 6).Adj x z ∧ D_6_06 z y + 1 = D_6_06 x y) ∧
    (∀ u v w : Fin 6, (reps 6 6).Adj u v → D_6_06 u w ≤ D_6_06 v w + 1) := by
  decide +kernel

theorem classify_6_06 : ¬ Challenge.IsMedian (reps 6 6) ∨
    (Challenge.Question3' (reps 6 6) ∧ Challenge.Question4 (reps 6 6)) := by
  have hD : ∀ x y, (reps 6 6).dist x y = D_6_06 x y :=
    dist_eq_of_certificate (reps 6 6) D_6_06 cert_6_06.1 cert_6_06.2.1
      cert_6_06.2.2.1 cert_6_06.2.2.2
  have hc : (reps 6 6).Connected := connected_of_dist (reps 6 6) D_6_06 hD cert_6_06.2.1
  have hd : (reps 6 6).diam = 3 :=
    diam_eq_of_table (reps 6 6) D_6_06 hc hD 3
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 6) = 8 :=
    triameter_eq_of_table (reps 6 6) D_6_06 hD 8
      (by decide +kernel) 1 4 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 6) D_6_06 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 6) D_6_06 hD 3 8 hd ht (by decide +kernel)⟩

private def D_6_07 (u v : Fin 6) : ℕ :=
  ![![0, 2, 1, 1, 1, 2],
    ![2, 0, 1, 1, 3, 2],
    ![1, 1, 0, 2, 2, 3],
    ![1, 1, 2, 0, 2, 1],
    ![1, 3, 2, 2, 0, 3],
    ![2, 2, 3, 1, 3, 0]] u v

private theorem cert_6_07 :
    (∀ x : Fin 6, D_6_07 x x = 0) ∧
    (∀ x y : Fin 6, D_6_07 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_07 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 7).Adj x z ∧ D_6_07 z y + 1 = D_6_07 x y) ∧
    (∀ u v w : Fin 6, (reps 6 7).Adj u v → D_6_07 u w ≤ D_6_07 v w + 1) := by
  decide +kernel

theorem classify_6_07 : ¬ Challenge.IsMedian (reps 6 7) ∨
    (Challenge.Question3' (reps 6 7) ∧ Challenge.Question4 (reps 6 7)) := by
  have hD : ∀ x y, (reps 6 7).dist x y = D_6_07 x y :=
    dist_eq_of_certificate (reps 6 7) D_6_07 cert_6_07.1 cert_6_07.2.1
      cert_6_07.2.2.1 cert_6_07.2.2.2
  have hc : (reps 6 7).Connected := connected_of_dist (reps 6 7) D_6_07 hD cert_6_07.2.1
  have hd : (reps 6 7).diam = 3 :=
    diam_eq_of_table (reps 6 7) D_6_07 hc hD 3
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 7) = 8 :=
    triameter_eq_of_table (reps 6 7) D_6_07 hD 8
      (by decide +kernel) 1 4 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 7) D_6_07 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 7) D_6_07 hD 3 8 hd ht (by decide +kernel)⟩

private def D_6_08 (u v : Fin 6) : ℕ :=
  ![![0, 4, 1, 3, 2, 2],
    ![4, 0, 3, 1, 2, 2],
    ![1, 3, 0, 2, 1, 1],
    ![3, 1, 2, 0, 1, 1],
    ![2, 2, 1, 1, 0, 2],
    ![2, 2, 1, 1, 2, 0]] u v

private theorem cert_6_08 :
    (∀ x : Fin 6, D_6_08 x x = 0) ∧
    (∀ x y : Fin 6, D_6_08 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_08 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 8).Adj x z ∧ D_6_08 z y + 1 = D_6_08 x y) ∧
    (∀ u v w : Fin 6, (reps 6 8).Adj u v → D_6_08 u w ≤ D_6_08 v w + 1) := by
  decide +kernel

theorem classify_6_08 : ¬ Challenge.IsMedian (reps 6 8) ∨
    (Challenge.Question3' (reps 6 8) ∧ Challenge.Question4 (reps 6 8)) := by
  have hD : ∀ x y, (reps 6 8).dist x y = D_6_08 x y :=
    dist_eq_of_certificate (reps 6 8) D_6_08 cert_6_08.1 cert_6_08.2.1
      cert_6_08.2.2.1 cert_6_08.2.2.2
  have hc : (reps 6 8).Connected := connected_of_dist (reps 6 8) D_6_08 hD cert_6_08.2.1
  have hd : (reps 6 8).diam = 4 :=
    diam_eq_of_table (reps 6 8) D_6_08 hc hD 4
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 8) = 8 :=
    triameter_eq_of_table (reps 6 8) D_6_08 hD 8
      (by decide +kernel) 0 0 1 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 8) D_6_08 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 8) D_6_08 hD 4 8 hd ht (by decide +kernel)⟩

private def D_6_09 (u v : Fin 6) : ℕ :=
  ![![0, 2, 2, 3, 1, 1],
    ![2, 0, 2, 1, 1, 3],
    ![2, 2, 0, 1, 1, 3],
    ![3, 1, 1, 0, 2, 4],
    ![1, 1, 1, 2, 0, 2],
    ![1, 3, 3, 4, 2, 0]] u v

private theorem cert_6_09 :
    (∀ x : Fin 6, D_6_09 x x = 0) ∧
    (∀ x y : Fin 6, D_6_09 x y = 0 → x = y) ∧
    (∀ x y : Fin 6, D_6_09 x y ≠ 0 →
      ∃ z : Fin 6, (reps 6 9).Adj x z ∧ D_6_09 z y + 1 = D_6_09 x y) ∧
    (∀ u v w : Fin 6, (reps 6 9).Adj u v → D_6_09 u w ≤ D_6_09 v w + 1) := by
  decide +kernel

theorem classify_6_09 : ¬ Challenge.IsMedian (reps 6 9) ∨
    (Challenge.Question3' (reps 6 9) ∧ Challenge.Question4 (reps 6 9)) := by
  have hD : ∀ x y, (reps 6 9).dist x y = D_6_09 x y :=
    dist_eq_of_certificate (reps 6 9) D_6_09 cert_6_09.1 cert_6_09.2.1
      cert_6_09.2.2.1 cert_6_09.2.2.2
  have hc : (reps 6 9).Connected := connected_of_dist (reps 6 9) D_6_09 hD cert_6_09.2.1
  have hd : (reps 6 9).diam = 4 :=
    diam_eq_of_table (reps 6 9) D_6_09 hc hD 4
      (by decide +kernel) 3 5 (by decide +kernel)
  have ht : Challenge.triameter (reps 6 9) = 8 :=
    triameter_eq_of_table (reps 6 9) D_6_09 hD 8
      (by decide +kernel) 0 3 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 6 9) D_6_09 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 6 9) D_6_09 hD 4 8 hd ht (by decide +kernel)⟩

#print axioms classify_6_00
#print axioms classify_6_01
#print axioms classify_6_02
#print axioms classify_6_03
#print axioms classify_6_04
#print axioms classify_6_05
#print axioms classify_6_06
#print axioms classify_6_07
#print axioms classify_6_08
#print axioms classify_6_09

end CodexPaper4.SmallMedianClassificationBlock01
