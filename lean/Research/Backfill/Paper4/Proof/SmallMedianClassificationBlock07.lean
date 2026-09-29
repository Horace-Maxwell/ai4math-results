import Research.Backfill.Paper4.Proof.SmallMetricCertificate
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Actual graph classification for a bounded group of accepted representatives.
Every leaf proves the complete nonmedian-or-Q3prime-and-Q4 disjunction.
Formal acceptance and resource measurements are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.SmallMedianClassificationBlock07
open BackfillPaper4 SimpleGraph SmallMetricCertificate TriangleFreeEnumerationFamily

private def D_7_40 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 2, 1, 2],
    ![1, 0, 1, 2, 3, 2, 1],
    ![2, 1, 0, 1, 2, 3, 2],
    ![3, 2, 1, 0, 1, 2, 3],
    ![2, 3, 2, 1, 0, 1, 2],
    ![1, 2, 3, 2, 1, 0, 1],
    ![2, 1, 2, 3, 2, 1, 0]] u v

private theorem cert_7_40 :
    (∀ x : Fin 7, D_7_40 x x = 0) ∧
    (∀ x y : Fin 7, D_7_40 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_40 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 40).Adj x z ∧ D_7_40 z y + 1 = D_7_40 x y) ∧
    (∀ u v w : Fin 7, (reps 7 40).Adj u v → D_7_40 u w ≤ D_7_40 v w + 1) := by
  decide +kernel

theorem classify_7_40 : ¬ Challenge.IsMedian (reps 7 40) ∨
    (Challenge.Question3' (reps 7 40) ∧ Challenge.Question4 (reps 7 40)) := by
  have hD : ∀ x y, (reps 7 40).dist x y = D_7_40 x y :=
    dist_eq_of_certificate (reps 7 40) D_7_40 cert_7_40.1 cert_7_40.2.1
      cert_7_40.2.2.1 cert_7_40.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 7) 2 4
  have hnone : ∀ x : Fin 7, ¬ ((D_7_40 0 x + D_7_40 x 2 = D_7_40 0 2) ∧
      (D_7_40 0 x + D_7_40 x 4 = D_7_40 0 4) ∧
      (D_7_40 2 x + D_7_40 x 4 = D_7_40 2 4)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_7_41 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 2, 2, 1, 1],
    ![1, 0, 1, 2, 3, 2, 2],
    ![2, 1, 0, 1, 2, 3, 2],
    ![2, 2, 1, 0, 1, 2, 1],
    ![2, 3, 2, 1, 0, 1, 2],
    ![1, 2, 3, 2, 1, 0, 2],
    ![1, 2, 2, 1, 2, 2, 0]] u v

private theorem cert_7_41 :
    (∀ x : Fin 7, D_7_41 x x = 0) ∧
    (∀ x y : Fin 7, D_7_41 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_41 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 41).Adj x z ∧ D_7_41 z y + 1 = D_7_41 x y) ∧
    (∀ u v w : Fin 7, (reps 7 41).Adj u v → D_7_41 u w ≤ D_7_41 v w + 1) := by
  decide +kernel

theorem classify_7_41 : ¬ Challenge.IsMedian (reps 7 41) ∨
    (Challenge.Question3' (reps 7 41) ∧ Challenge.Question4 (reps 7 41)) := by
  have hD : ∀ x y, (reps 7 41).dist x y = D_7_41 x y :=
    dist_eq_of_certificate (reps 7 41) D_7_41 cert_7_41.1 cert_7_41.2.1
      cert_7_41.2.2.1 cert_7_41.2.2.2
  have hc : (reps 7 41).Connected := connected_of_dist (reps 7 41) D_7_41 hD cert_7_41.2.1
  have hd : (reps 7 41).diam = 3 :=
    diam_eq_of_table (reps 7 41) D_7_41 hc hD 3
      (by decide +kernel) 1 4 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 41) = 7 :=
    triameter_eq_of_table (reps 7 41) D_7_41 hD 7
      (by decide +kernel) 1 4 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 41) D_7_41 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 41) D_7_41 hD 3 7 hd ht (by decide +kernel)⟩

private def D_7_42 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 2, 1, 1, 2],
    ![2, 0, 2, 2, 1, 1, 2],
    ![2, 2, 0, 2, 1, 1, 2],
    ![2, 2, 2, 0, 1, 1, 2],
    ![1, 1, 1, 1, 0, 2, 1],
    ![1, 1, 1, 1, 2, 0, 3],
    ![2, 2, 2, 2, 1, 3, 0]] u v

private theorem cert_7_42 :
    (∀ x : Fin 7, D_7_42 x x = 0) ∧
    (∀ x y : Fin 7, D_7_42 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_42 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 42).Adj x z ∧ D_7_42 z y + 1 = D_7_42 x y) ∧
    (∀ u v w : Fin 7, (reps 7 42).Adj u v → D_7_42 u w ≤ D_7_42 v w + 1) := by
  decide +kernel

theorem classify_7_42 : ¬ Challenge.IsMedian (reps 7 42) ∨
    (Challenge.Question3' (reps 7 42) ∧ Challenge.Question4 (reps 7 42)) := by
  have hD : ∀ x y, (reps 7 42).dist x y = D_7_42 x y :=
    dist_eq_of_certificate (reps 7 42) D_7_42 cert_7_42.1 cert_7_42.2.1
      cert_7_42.2.2.1 cert_7_42.2.2.2
  exact Or.inl (not_median_of_two (reps 7 42) D_7_42 hD 0 1 2 4 5
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_7_43 (u v : Fin 7) : ℕ :=
  ![![0, 2, 2, 2, 1, 1, 3],
    ![2, 0, 2, 2, 1, 1, 1],
    ![2, 2, 0, 2, 1, 1, 3],
    ![2, 2, 2, 0, 1, 1, 3],
    ![1, 1, 1, 1, 0, 2, 2],
    ![1, 1, 1, 1, 2, 0, 2],
    ![3, 1, 3, 3, 2, 2, 0]] u v

private theorem cert_7_43 :
    (∀ x : Fin 7, D_7_43 x x = 0) ∧
    (∀ x y : Fin 7, D_7_43 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_43 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 43).Adj x z ∧ D_7_43 z y + 1 = D_7_43 x y) ∧
    (∀ u v w : Fin 7, (reps 7 43).Adj u v → D_7_43 u w ≤ D_7_43 v w + 1) := by
  decide +kernel

theorem classify_7_43 : ¬ Challenge.IsMedian (reps 7 43) ∨
    (Challenge.Question3' (reps 7 43) ∧ Challenge.Question4 (reps 7 43)) := by
  have hD : ∀ x y, (reps 7 43).dist x y = D_7_43 x y :=
    dist_eq_of_certificate (reps 7 43) D_7_43 cert_7_43.1 cert_7_43.2.1
      cert_7_43.2.2.1 cert_7_43.2.2.2
  have hc : (reps 7 43).Connected := connected_of_dist (reps 7 43) D_7_43 hD cert_7_43.2.1
  have hd : (reps 7 43).diam = 3 :=
    diam_eq_of_table (reps 7 43) D_7_43 hc hD 3
      (by decide +kernel) 0 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 43) = 8 :=
    triameter_eq_of_table (reps 7 43) D_7_43 hD 8
      (by decide +kernel) 0 2 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 43) D_7_43 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 43) D_7_43 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_44 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 2, 1, 2],
    ![1, 0, 1, 2, 1, 2, 3],
    ![2, 1, 0, 1, 2, 1, 2],
    ![3, 2, 1, 0, 1, 2, 3],
    ![2, 1, 2, 1, 0, 1, 2],
    ![1, 2, 1, 2, 1, 0, 1],
    ![2, 3, 2, 3, 2, 1, 0]] u v

private theorem cert_7_44 :
    (∀ x : Fin 7, D_7_44 x x = 0) ∧
    (∀ x y : Fin 7, D_7_44 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_44 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 44).Adj x z ∧ D_7_44 z y + 1 = D_7_44 x y) ∧
    (∀ u v w : Fin 7, (reps 7 44).Adj u v → D_7_44 u w ≤ D_7_44 v w + 1) := by
  decide +kernel

theorem classify_7_44 : ¬ Challenge.IsMedian (reps 7 44) ∨
    (Challenge.Question3' (reps 7 44) ∧ Challenge.Question4 (reps 7 44)) := by
  have hD : ∀ x y, (reps 7 44).dist x y = D_7_44 x y :=
    dist_eq_of_certificate (reps 7 44) D_7_44 cert_7_44.1 cert_7_44.2.1
      cert_7_44.2.2.1 cert_7_44.2.2.2
  have hc : (reps 7 44).Connected := connected_of_dist (reps 7 44) D_7_44 hD cert_7_44.2.1
  have hd : (reps 7 44).diam = 3 :=
    diam_eq_of_table (reps 7 44) D_7_44 hc hD 3
      (by decide +kernel) 0 3 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 44) = 8 :=
    triameter_eq_of_table (reps 7 44) D_7_44 hD 8
      (by decide +kernel) 0 3 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 44) D_7_44 hc hD 3 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 44) D_7_44 hD 3 8 hd ht (by decide +kernel)⟩

private def D_7_45 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 3, 2, 1, 1],
    ![1, 0, 1, 2, 1, 2, 2],
    ![2, 1, 0, 1, 2, 1, 3],
    ![3, 2, 1, 0, 1, 2, 4],
    ![2, 1, 2, 1, 0, 1, 3],
    ![1, 2, 1, 2, 1, 0, 2],
    ![1, 2, 3, 4, 3, 2, 0]] u v

private theorem cert_7_45 :
    (∀ x : Fin 7, D_7_45 x x = 0) ∧
    (∀ x y : Fin 7, D_7_45 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_45 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 45).Adj x z ∧ D_7_45 z y + 1 = D_7_45 x y) ∧
    (∀ u v w : Fin 7, (reps 7 45).Adj u v → D_7_45 u w ≤ D_7_45 v w + 1) := by
  decide +kernel

theorem classify_7_45 : ¬ Challenge.IsMedian (reps 7 45) ∨
    (Challenge.Question3' (reps 7 45) ∧ Challenge.Question4 (reps 7 45)) := by
  have hD : ∀ x y, (reps 7 45).dist x y = D_7_45 x y :=
    dist_eq_of_certificate (reps 7 45) D_7_45 cert_7_45.1 cert_7_45.2.1
      cert_7_45.2.2.1 cert_7_45.2.2.2
  have hc : (reps 7 45).Connected := connected_of_dist (reps 7 45) D_7_45 hD cert_7_45.2.1
  have hd : (reps 7 45).diam = 4 :=
    diam_eq_of_table (reps 7 45) D_7_45 hc hD 4
      (by decide +kernel) 3 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 45) = 8 :=
    triameter_eq_of_table (reps 7 45) D_7_45 hD 8
      (by decide +kernel) 0 3 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 45) D_7_45 hc hD 4 8 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 45) D_7_45 hD 4 8 hd ht (by decide +kernel)⟩

private def D_7_46 (u v : Fin 7) : ℕ :=
  ![![0, 2, 1, 2, 2, 1, 2],
    ![2, 0, 1, 2, 2, 1, 2],
    ![1, 1, 0, 1, 1, 2, 2],
    ![2, 2, 1, 0, 2, 2, 1],
    ![2, 2, 1, 2, 0, 1, 2],
    ![1, 1, 2, 2, 1, 0, 1],
    ![2, 2, 2, 1, 2, 1, 0]] u v

private theorem cert_7_46 :
    (∀ x : Fin 7, D_7_46 x x = 0) ∧
    (∀ x y : Fin 7, D_7_46 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_46 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 46).Adj x z ∧ D_7_46 z y + 1 = D_7_46 x y) ∧
    (∀ u v w : Fin 7, (reps 7 46).Adj u v → D_7_46 u w ≤ D_7_46 v w + 1) := by
  decide +kernel

theorem classify_7_46 : ¬ Challenge.IsMedian (reps 7 46) ∨
    (Challenge.Question3' (reps 7 46) ∧ Challenge.Question4 (reps 7 46)) := by
  have hD : ∀ x y, (reps 7 46).dist x y = D_7_46 x y :=
    dist_eq_of_certificate (reps 7 46) D_7_46 cert_7_46.1 cert_7_46.2.1
      cert_7_46.2.2.1 cert_7_46.2.2.2
  exact Or.inl (not_median_of_two (reps 7 46) D_7_46 hD 0 1 4 2 5
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_7_47 (u v : Fin 7) : ℕ :=
  ![![0, 1, 1, 2, 1, 2, 3],
    ![1, 0, 2, 3, 2, 1, 2],
    ![1, 2, 0, 1, 2, 1, 2],
    ![2, 3, 1, 0, 3, 2, 1],
    ![1, 2, 2, 3, 0, 1, 2],
    ![2, 1, 1, 2, 1, 0, 1],
    ![3, 2, 2, 1, 2, 1, 0]] u v

private theorem cert_7_47 :
    (∀ x : Fin 7, D_7_47 x x = 0) ∧
    (∀ x y : Fin 7, D_7_47 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_47 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 47).Adj x z ∧ D_7_47 z y + 1 = D_7_47 x y) ∧
    (∀ u v w : Fin 7, (reps 7 47).Adj u v → D_7_47 u w ≤ D_7_47 v w + 1) := by
  decide +kernel

theorem classify_7_47 : ¬ Challenge.IsMedian (reps 7 47) ∨
    (Challenge.Question3' (reps 7 47) ∧ Challenge.Question4 (reps 7 47)) := by
  have hD : ∀ x y, (reps 7 47).dist x y = D_7_47 x y :=
    dist_eq_of_certificate (reps 7 47) D_7_47 cert_7_47.1 cert_7_47.2.1
      cert_7_47.2.2.1 cert_7_47.2.2.2
  exact Or.inl (not_median_of_two (reps 7 47) D_7_47 hD 1 2 4 0 5
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def D_7_48 (u v : Fin 7) : ℕ :=
  ![![0, 1, 1, 2, 2, 1, 1],
    ![1, 0, 2, 2, 1, 2, 2],
    ![1, 2, 0, 1, 2, 2, 2],
    ![2, 2, 1, 0, 1, 2, 1],
    ![2, 1, 2, 1, 0, 1, 2],
    ![1, 2, 2, 2, 1, 0, 2],
    ![1, 2, 2, 1, 2, 2, 0]] u v

private theorem cert_7_48 :
    (∀ x : Fin 7, D_7_48 x x = 0) ∧
    (∀ x y : Fin 7, D_7_48 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_48 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 48).Adj x z ∧ D_7_48 z y + 1 = D_7_48 x y) ∧
    (∀ u v w : Fin 7, (reps 7 48).Adj u v → D_7_48 u w ≤ D_7_48 v w + 1) := by
  decide +kernel

theorem classify_7_48 : ¬ Challenge.IsMedian (reps 7 48) ∨
    (Challenge.Question3' (reps 7 48) ∧ Challenge.Question4 (reps 7 48)) := by
  have hD : ∀ x y, (reps 7 48).dist x y = D_7_48 x y :=
    dist_eq_of_certificate (reps 7 48) D_7_48 cert_7_48.1 cert_7_48.2.1
      cert_7_48.2.2.1 cert_7_48.2.2.2
  apply Or.inl
  intro hm
  obtain ⟨x, hx, _⟩ := hm.2 (0 : Fin 7) 1 3
  have hnone : ∀ x : Fin 7, ¬ ((D_7_48 0 x + D_7_48 x 1 = D_7_48 0 1) ∧
      (D_7_48 0 x + D_7_48 x 3 = D_7_48 0 3) ∧
      (D_7_48 1 x + D_7_48 x 3 = D_7_48 1 3)) := by
    decide +kernel
  exact hnone x (by simpa only [Challenge.InInterval, hD] using hx)

private def D_7_49 (u v : Fin 7) : ℕ :=
  ![![0, 1, 2, 1, 2, 2, 1],
    ![1, 0, 1, 2, 1, 2, 2],
    ![2, 1, 0, 1, 2, 2, 3],
    ![1, 2, 1, 0, 2, 1, 2],
    ![2, 1, 2, 2, 0, 1, 1],
    ![2, 2, 2, 1, 1, 0, 2],
    ![1, 2, 3, 2, 1, 2, 0]] u v

private theorem cert_7_49 :
    (∀ x : Fin 7, D_7_49 x x = 0) ∧
    (∀ x y : Fin 7, D_7_49 x y = 0 → x = y) ∧
    (∀ x y : Fin 7, D_7_49 x y ≠ 0 →
      ∃ z : Fin 7, (reps 7 49).Adj x z ∧ D_7_49 z y + 1 = D_7_49 x y) ∧
    (∀ u v w : Fin 7, (reps 7 49).Adj u v → D_7_49 u w ≤ D_7_49 v w + 1) := by
  decide +kernel

theorem classify_7_49 : ¬ Challenge.IsMedian (reps 7 49) ∨
    (Challenge.Question3' (reps 7 49) ∧ Challenge.Question4 (reps 7 49)) := by
  have hD : ∀ x y, (reps 7 49).dist x y = D_7_49 x y :=
    dist_eq_of_certificate (reps 7 49) D_7_49 cert_7_49.1 cert_7_49.2.1
      cert_7_49.2.2.1 cert_7_49.2.2.2
  have hc : (reps 7 49).Connected := connected_of_dist (reps 7 49) D_7_49 hD cert_7_49.2.1
  have hd : (reps 7 49).diam = 3 :=
    diam_eq_of_table (reps 7 49) D_7_49 hc hD 3
      (by decide +kernel) 2 6 (by decide +kernel)
  have ht : Challenge.triameter (reps 7 49) = 7 :=
    triameter_eq_of_table (reps 7 49) D_7_49 hD 7
      (by decide +kernel) 2 5 6 (by decide +kernel)
  exact Or.inr ⟨question3'_of_table (reps 7 49) D_7_49 hc hD 3 7 hd ht
      (by decide +kernel),
    question4_of_table (reps 7 49) D_7_49 hD 3 7 hd ht (by decide +kernel)⟩

#print axioms classify_7_40
#print axioms classify_7_41
#print axioms classify_7_42
#print axioms classify_7_43
#print axioms classify_7_44
#print axioms classify_7_45
#print axioms classify_7_46
#print axioms classify_7_47
#print axioms classify_7_48
#print axioms classify_7_49

end CodexPaper4.SmallMedianClassificationBlock07
