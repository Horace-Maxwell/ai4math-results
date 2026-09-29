import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock06
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_7_30 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 3, 1],
    ![2, 0, 2, 1, 1, 3, 3],
    ![2, 2, 0, 1, 1, 1, 3],
    ![1, 1, 1, 0, 2, 2, 2],
    ![1, 1, 1, 2, 0, 2, 2],
    ![3, 3, 1, 2, 2, 0, 4],
    ![1, 3, 3, 2, 2, 4, 0]] u v

private theorem cert_7_30 :
    (∀ x : Fin 7, D_7_30 x x = 0) ∧
    (∀ x y : Fin 7, D_7_30 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_30 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 30).Adj x z ∧ D_7_30 z y + 1 = D_7_30 x y) ∧
    (∀ u v w : Fin 7, (reps 7 30).Adj u v → D_7_30 u w ≤ D_7_30 v w + 1) := by
  decide +kernel

theorem classify_7_30 : ¬ Challenge.IsMedian (reps 7 30) ∨
    (Challenge.Question3' (reps 7 30) ∧ Challenge.Question4 (reps 7 30)) := by
  have hD : ∀ x y, (reps 7 30).dist x y = D_7_30 x y :=
    dist_eq_of_certificate (reps 7 30) D_7_30 cert_7_30.1 cert_7_30.2.1
      cert_7_30.2.2.1 cert_7_30.2.2.2
  have hc : (reps 7 30).Connected := connected_of_dist (reps 7 30) D_7_30 hD cert_7_30.2.1
  have hd : (reps 7 30).diam = 4 :=
    diam_eq_of_table (reps 7 30) D_7_30 hc hD 4
      (by decide +kernel) 5 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 30) = 10 :=
    triameter_eq_of_table (reps 7 30) D_7_30 hD 10
      (by decide +kernel) 1 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 30) D_7_30 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 30) D_7_30 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_31 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 2, 2, 3],
    ![1, 0, 1, 2, 1, 1, 2],
    ![2, 1, 0, 1, 2, 2, 1],
    ![3, 2, 1, 0, 1, 3, 2],
    ![2, 1, 2, 1, 0, 2, 3],
    ![2, 1, 2, 3, 2, 0, 1],
    ![3, 2, 1, 2, 3, 1, 0]] u v

private theorem cert_7_31 :
    (∀ x : Fin 7, D_7_31 x x = 0) ∧
    (∀ x y : Fin 7, D_7_31 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_31 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 31).Adj x z ∧ D_7_31 z y + 1 = D_7_31 x y) ∧
    (∀ u v w : Fin 7, (reps 7 31).Adj u v → D_7_31 u w ≤ D_7_31 v w + 1) := by
  decide +kernel

theorem classify_7_31 : ¬ Challenge.IsMedian (reps 7 31) ∨
    (Challenge.Question3' (reps 7 31) ∧ Challenge.Question4 (reps 7 31)) := by
  have hD : ∀ x y, (reps 7 31).dist x y = D_7_31 x y :=
    dist_eq_of_certificate (reps 7 31) D_7_31 cert_7_31.1 cert_7_31.2.1
      cert_7_31.2.2.1 cert_7_31.2.2.2
  have hc : (reps 7 31).Connected := connected_of_dist (reps 7 31) D_7_31 hD cert_7_31.2.1
  have hd : (reps 7 31).diam = 3 :=
    diam_eq_of_table (reps 7 31) D_7_31 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 31) = 8 :=
    triameter_eq_of_table (reps 7 31) D_7_31 hD 8
      (by decide +kernel) 0 3 5 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 31) D_7_31 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 31) D_7_31 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_32 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 3, 2, 2],
    ![1, 0, 1, 2, 2, 1, 1],
    ![2, 1, 0, 1, 2, 2, 2],
    ![3, 2, 1, 0, 1, 2, 2],
    ![3, 2, 2, 1, 0, 1, 1],
    ![2, 1, 2, 2, 1, 0, 2],
    ![2, 1, 2, 2, 1, 2, 0]] u v

private theorem cert_7_32 :
    (∀ x : Fin 7, D_7_32 x x = 0) ∧
    (∀ x y : Fin 7, D_7_32 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_32 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 32).Adj x z ∧ D_7_32 z y + 1 = D_7_32 x y) ∧
    (∀ u v w : Fin 7, (reps 7 32).Adj u v → D_7_32 u w ≤ D_7_32 v w + 1) := by
  decide +kernel

theorem classify_7_32 : ¬ Challenge.IsMedian (reps 7 32) ∨
    (Challenge.Question3' (reps 7 32) ∧ Challenge.Question4 (reps 7 32)) := by
  have hD : ∀ x y, (reps 7 32).dist x y = D_7_32 x y :=
    dist_eq_of_certificate (reps 7 32) D_7_32 cert_7_32.1 cert_7_32.2.1
      cert_7_32.2.2.1 cert_7_32.2.2.2
  have hc : (reps 7 32).Connected := connected_of_dist (reps 7 32) D_7_32 hD cert_7_32.2.1
  have hd : (reps 7 32).diam = 3 :=
    diam_eq_of_table (reps 7 32) D_7_32 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 32) = 7 :=
    triameter_eq_of_table (reps 7 32) D_7_32 hD 7
      (by decide +kernel) 0 2 4 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 32) D_7_32 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 32) D_7_32 hD 3 7 hd ht (by decide +kernel)⟩

private def D_7_33 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 2, 3],
    ![2, 0, 2, 1, 1, 2, 3],
    ![2, 2, 0, 1, 1, 2, 3],
    ![1, 1, 1, 0, 2, 3, 4],
    ![1, 1, 1, 2, 0, 1, 2],
    ![2, 2, 2, 3, 1, 0, 1],
    ![3, 3, 3, 4, 2, 1, 0]] u v

private theorem cert_7_33 :
    (∀ x : Fin 7, D_7_33 x x = 0) ∧
    (∀ x y : Fin 7, D_7_33 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_33 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 33).Adj x z ∧ D_7_33 z y + 1 = D_7_33 x y) ∧
    (∀ u v w : Fin 7, (reps 7 33).Adj u v → D_7_33 u w ≤ D_7_33 v w + 1) := by
  decide +kernel

theorem classify_7_33 : ¬ Challenge.IsMedian (reps 7 33) ∨
    (Challenge.Question3' (reps 7 33) ∧ Challenge.Question4 (reps 7 33)) := by
  have hD : ∀ x y, (reps 7 33).dist x y = D_7_33 x y :=
    dist_eq_of_certificate (reps 7 33) D_7_33 cert_7_33.1 cert_7_33.2.1
      cert_7_33.2.2.1 cert_7_33.2.2.2
  have hc : (reps 7 33).Connected := connected_of_dist (reps 7 33) D_7_33 hD cert_7_33.2.1
  have hd : (reps 7 33).diam = 4 :=
    diam_eq_of_table (reps 7 33) D_7_33 hc hD 4
      (by decide +kernel) 3 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 33) = 8 :=
    triameter_eq_of_table (reps 7 33) D_7_33 hD 8
      (by decide +kernel) 0 1 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 33) D_7_33 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 33) D_7_33 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_34 (u v : Fin 7) : ℕ :=
  ![![0, 2, 3, 2, 1, 3, 4],
    ![2, 0, 1, 2, 1, 1, 2],
    ![3, 1, 0, 1, 2, 2, 1],
    ![2, 2, 1, 0, 1, 3, 2],
    ![1, 1, 2, 1, 0, 2, 3],
    ![3, 1, 2, 3, 2, 0, 1],
    ![4, 2, 1, 2, 3, 1, 0]] u v

private theorem cert_7_34 :
    (∀ x : Fin 7, D_7_34 x x = 0) ∧
    (∀ x y : Fin 7, D_7_34 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_34 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 34).Adj x z ∧ D_7_34 z y + 1 = D_7_34 x y) ∧
    (∀ u v w : Fin 7, (reps 7 34).Adj u v → D_7_34 u w ≤ D_7_34 v w + 1) := by
  decide +kernel

theorem classify_7_34 : ¬ Challenge.IsMedian (reps 7 34) ∨
    (Challenge.Question3' (reps 7 34) ∧ Challenge.Question4 (reps 7 34)) := by
  have hD : ∀ x y, (reps 7 34).dist x y = D_7_34 x y :=
    dist_eq_of_certificate (reps 7 34) D_7_34 cert_7_34.1 cert_7_34.2.1
      cert_7_34.2.2.1 cert_7_34.2.2.2
  have hc : (reps 7 34).Connected := connected_of_dist (reps 7 34) D_7_34 hD cert_7_34.2.1
  have hd : (reps 7 34).diam = 4 :=
    diam_eq_of_table (reps 7 34) D_7_34 hc hD 4
      (by decide +kernel) 0 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 34) = 8 :=
    triameter_eq_of_table (reps 7 34) D_7_34 hD 8
      (by decide +kernel) 0 0 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 34) D_7_34 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 34) D_7_34 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_35 (u v : Fin 7) : ℕ :=
  ![![0, 3, 2, 3, 1, 2, 3],
    ![3, 0, 1, 2, 2, 1, 2],
    ![2, 1, 0, 1, 1, 2, 2],
    ![3, 2, 1, 0, 2, 2, 1],
    ![1, 2, 1, 2, 0, 1, 2],
    ![2, 1, 2, 2, 1, 0, 1],
    ![3, 2, 2, 1, 2, 1, 0]] u v

private theorem cert_7_35 :
    (∀ x : Fin 7, D_7_35 x x = 0) ∧
    (∀ x y : Fin 7, D_7_35 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_35 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 35).Adj x z ∧ D_7_35 z y + 1 = D_7_35 x y) ∧
    (∀ u v w : Fin 7, (reps 7 35).Adj u v → D_7_35 u w ≤ D_7_35 v w + 1) := by
  decide +kernel

theorem classify_7_35 : ¬ Challenge.IsMedian (reps 7 35) ∨
    (Challenge.Question3' (reps 7 35) ∧ Challenge.Question4 (reps 7 35)) := by
  have hD : ∀ x y, (reps 7 35).dist x y = D_7_35 x y :=
    dist_eq_of_certificate (reps 7 35) D_7_35 cert_7_35.1 cert_7_35.2.1
      cert_7_35.2.2.1 cert_7_35.2.2.2
  have hc : (reps 7 35).Connected := connected_of_dist (reps 7 35) D_7_35 hD cert_7_35.2.1
  have hd : (reps 7 35).diam = 3 :=
    diam_eq_of_table (reps 7 35) D_7_35 hc hD 3
      (by decide +kernel) 0 1 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 35) = 8 :=
    triameter_eq_of_table (reps 7 35) D_7_35 hD 8
      (by decide +kernel) 0 1 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 35) D_7_35 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 35) D_7_35 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_36 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 2, 1, 1],
    ![2, 0, 1, 2, 2, 1, 3],
    ![2, 1, 0, 1, 1, 2, 3],
    ![1, 2, 1, 0, 2, 2, 2],
    ![2, 2, 1, 2, 0, 1, 3],
    ![1, 1, 2, 2, 1, 0, 2],
    ![1, 3, 3, 2, 3, 2, 0]] u v

private theorem cert_7_36 :
    (∀ x : Fin 7, D_7_36 x x = 0) ∧
    (∀ x y : Fin 7, D_7_36 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_36 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 36).Adj x z ∧ D_7_36 z y + 1 = D_7_36 x y) ∧
    (∀ u v w : Fin 7, (reps 7 36).Adj u v → D_7_36 u w ≤ D_7_36 v w + 1) := by
  decide +kernel

theorem classify_7_36 : ¬ Challenge.IsMedian (reps 7 36) ∨
    (Challenge.Question3' (reps 7 36) ∧ Challenge.Question4 (reps 7 36)) := by
  have hD : ∀ x y, (reps 7 36).dist x y = D_7_36 x y :=
    dist_eq_of_certificate (reps 7 36) D_7_36 cert_7_36.1 cert_7_36.2.1
      cert_7_36.2.2.1 cert_7_36.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 7) 1 2
  have hnone : ∀ x : Fin 7, ¬ ((D_7_36 0 x + D_7_36 x 1 = D_7_36 0 1) ∧
      (D_7_36 0 x + D_7_36 x 2 = D_7_36 0 2) ∧
      (D_7_36 1 x + D_7_36 x 2 = D_7_36 1 2)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_7_37 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 1, 1, 3, 4],
    ![2, 0, 2, 1, 1, 3, 4],
    ![2, 2, 0, 1, 1, 1, 2],
    ![1, 1, 1, 0, 2, 2, 3],
    ![1, 1, 1, 2, 0, 2, 3],
    ![3, 3, 1, 2, 2, 0, 1],
    ![4, 4, 2, 3, 3, 1, 0]] u v

private theorem cert_7_37 :
    (∀ x : Fin 7, D_7_37 x x = 0) ∧
    (∀ x y : Fin 7, D_7_37 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_37 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 37).Adj x z ∧ D_7_37 z y + 1 = D_7_37 x y) ∧
    (∀ u v w : Fin 7, (reps 7 37).Adj u v → D_7_37 u w ≤ D_7_37 v w + 1) := by
  decide +kernel

theorem classify_7_37 : ¬ Challenge.IsMedian (reps 7 37) ∨
    (Challenge.Question3' (reps 7 37) ∧ Challenge.Question4 (reps 7 37)) := by
  have hD : ∀ x y, (reps 7 37).dist x y = D_7_37 x y :=
    dist_eq_of_certificate (reps 7 37) D_7_37 cert_7_37.1 cert_7_37.2.1
      cert_7_37.2.2.1 cert_7_37.2.2.2
  have hc : (reps 7 37).Connected := connected_of_dist (reps 7 37) D_7_37 hD cert_7_37.2.1
  have hd : (reps 7 37).diam = 4 :=
    diam_eq_of_table (reps 7 37) D_7_37 hc hD 4
      (by decide +kernel) 0 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 37) = 10 :=
    triameter_eq_of_table (reps 7 37) D_7_37 hD 10
      (by decide +kernel) 0 1 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 37) D_7_37 hc hD 4 10 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 37) D_7_37 hD 4 10 hd ht (by decide +kernel)⟩

private def D_7_38 (u v : Fin 7) : ℕ :=
  ![![0, 1, 3, 4, 3, 1, 2],
    ![1, 0, 2, 3, 2, 2, 1],
    ![3, 2, 0, 1, 2, 2, 1],
    ![4, 3, 1, 0, 1, 3, 2],
    ![3, 2, 2, 1, 0, 2, 1],
    ![1, 2, 2, 3, 2, 0, 1],
    ![2, 1, 1, 2, 1, 1, 0]] u v

private theorem cert_7_38 :
    (∀ x : Fin 7, D_7_38 x x = 0) ∧
    (∀ x y : Fin 7, D_7_38 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_38 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 38).Adj x z ∧ D_7_38 z y + 1 = D_7_38 x y) ∧
    (∀ u v w : Fin 7, (reps 7 38).Adj u v → D_7_38 u w ≤ D_7_38 v w + 1) := by
  decide +kernel

theorem classify_7_38 : ¬ Challenge.IsMedian (reps 7 38) ∨
    (Challenge.Question3' (reps 7 38) ∧ Challenge.Question4 (reps 7 38)) := by
  have hD : ∀ x y, (reps 7 38).dist x y = D_7_38 x y :=
    dist_eq_of_certificate (reps 7 38) D_7_38 cert_7_38.1 cert_7_38.2.1
      cert_7_38.2.2.1 cert_7_38.2.2.2
  have hc : (reps 7 38).Connected := connected_of_dist (reps 7 38) D_7_38 hD cert_7_38.2.1
  have hd : (reps 7 38).diam = 4 :=
    diam_eq_of_table (reps 7 38) D_7_38 hc hD 4
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 38) = 8 :=
    triameter_eq_of_table (reps 7 38) D_7_38 hD 8
      (by decide +kernel) 0 0 3 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 38) D_7_38 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 38) D_7_38 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_39 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 1, 2, 3],
    ![1, 0, 1, 2, 2, 2, 3],
    ![2, 1, 0, 1, 2, 1, 2],
    ![3, 2, 1, 0, 3, 2, 1],
    ![1, 2, 2, 3, 0, 1, 2],
    ![2, 2, 1, 2, 1, 0, 1],
    ![3, 3, 2, 1, 2, 1, 0]] u v

private theorem cert_7_39 :
    (∀ x : Fin 7, D_7_39 x x = 0) ∧
    (∀ x y : Fin 7, D_7_39 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_39 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 39).Adj x z ∧ D_7_39 z y + 1 = D_7_39 x y) ∧
    (∀ u v w : Fin 7, (reps 7 39).Adj u v → D_7_39 u w ≤ D_7_39 v w + 1) := by
  decide +kernel

theorem classify_7_39 : ¬ Challenge.IsMedian (reps 7 39) ∨
    (Challenge.Question3' (reps 7 39) ∧ Challenge.Question4 (reps 7 39)) := by
  have hD : ∀ x y, (reps 7 39).dist x y = D_7_39 x y :=
    dist_eq_of_certificate (reps 7 39) D_7_39 cert_7_39.1 cert_7_39.2.1
      cert_7_39.2.2.1 cert_7_39.2.2.2
  have hc : (reps 7 39).Connected := connected_of_dist (reps 7 39) D_7_39 hD cert_7_39.2.1
  have hd : (reps 7 39).diam = 3 :=
    diam_eq_of_table (reps 7 39) D_7_39 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 39) = 7 :=
    triameter_eq_of_table (reps 7 39) D_7_39 hD 7
      (by decide +kernel) 0 1 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 39) D_7_39 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 39) D_7_39 hD 3 7 hd ht (by decide +kernel)⟩

#print axioms classify_7_30
#print axioms classify_7_31
#print axioms classify_7_32
#print axioms classify_7_33
#print axioms classify_7_34
#print axioms classify_7_35
#print axioms classify_7_36
#print axioms classify_7_37
#print axioms classify_7_38
#print axioms classify_7_39

end CodexPaper4.SmallMedianClassificationBlock06
