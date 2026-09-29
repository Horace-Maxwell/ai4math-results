import Research.Backfill.Paper4.Challenge

/-! General integer-grid interval and median arguments for the full frozen Lemma 1.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false
open scoped BigOperators

namespace CodexPaper4
open BackfillPaper4
namespace GridInterval

theorem abs_interval_iff (a b x : ℤ) :
    |a - x| + |x - b| = |a - b| ↔ min a b ≤ x ∧ x ≤ max a b := by
  constructor <;> intro h
  all_goals simp only [abs_eq_max_neg, min_def, max_def] at *
  all_goals split_ifs at * <;> omega

theorem natAbs_interval_iff (a b x : ℤ) :
    (a - x).natAbs + (x - b).natAbs = (a - b).natAbs ↔
      min a b ≤ x ∧ x ≤ max a b := by
  constructor
  · intro h
    apply (abs_interval_iff a b x).mp
    have hc := congrArg (fun n : ℕ => (n : ℤ)) h
    simpa only [Nat.cast_add, Int.natCast_natAbs] using hc
  · intro h
    have ha := (abs_interval_iff a b x).mpr h
    have hc : (((a - x).natAbs + (x - b).natAbs : ℕ) : ℤ) =
        ((a - b).natAbs : ℤ) := by
      simpa only [Nat.cast_add, Int.natCast_natAbs] using ha
    exact_mod_cast hc

theorem natAbs_triangle (a b x : ℤ) :
    (a - b).natAbs ≤ (a - x).natAbs + (x - b).natAbs := by
  simpa only [sub_add_sub_cancel] using Int.natAbs_add_le (a - x) (x - b)

theorem median_between_iff (a b c x : ℤ) :
    ((min a b ≤ x ∧ x ≤ max a b) ∧
      (min a c ≤ x ∧ x ≤ max a c) ∧
      (min b c ≤ x ∧ x ≤ max b c)) ↔ x = Challenge.med3 a b c := by
  constructor <;> intro h
  all_goals simp only [Challenge.med3, min_def, max_def] at *
  all_goals split_ifs at * <;> omega

theorem abs_triple_formula (a b c : ℤ) :
    |a - b| + |a - c| + |b - c| =
      2 * (max (max a b) c - min (min a b) c) := by
  simp only [abs_eq_max_neg, min_def, max_def]
  split_ifs <;> omega

theorem l1_eq_zero_iff {k : ℕ} (u v : Fin k → ℤ) : Challenge.l1 u v = 0 ↔ u = v := by
  constructor
  · intro h
    funext i
    have hle : (u i - v i).natAbs ≤ Challenge.l1 u v :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (u j - v j).natAbs) (Finset.mem_univ i)
    have hz : (u i - v i).natAbs = 0 := by omega
    exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hz)
  · rintro rfl
    simp [Challenge.l1]

theorem l1_triangle {k : ℕ} (u v x : Fin k → ℤ) :
    Challenge.l1 u v ≤ Challenge.l1 u x + Challenge.l1 x v := by
  unfold Challenge.l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => natAbs_triangle (u i) (v i) (x i)

theorem l1_interval_iff {k : ℕ} (u v x : Fin k → ℤ) :
    Challenge.l1 u x + Challenge.l1 x v = Challenge.l1 u v ↔
      ∀ i, min (u i) (v i) ≤ x i ∧ x i ≤ max (u i) (v i) := by
  constructor
  · intro h i
    have hsum : (∑ j, (u j - v j).natAbs) =
        ∑ j, ((u j - x j).natAbs + (x j - v j).natAbs) := by
      simpa only [Challenge.l1, Finset.sum_add_distrib] using h.symm
    have hcoord := (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (fun j _ => natAbs_triangle (u j) (v j) (x j))).mp hsum
    exact (natAbs_interval_iff (u i) (v i) (x i)).mp (hcoord i (Finset.mem_univ i)).symm
  · intro h
    unfold Challenge.l1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (natAbs_interval_iff (u i) (v i) (x i)).mpr (h i)

theorem grid_connected {k : ℕ} (S : Finset (Fin k → ℤ))
    (hne : S.Nonempty) (hA : Challenge.GridA S) : (Challenge.gridGraph S).Connected := by
  have : Nonempty S := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨⟨u, hu⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl u
  · apply SimpleGraph.Reachable.of_dist_ne_zero
    rw [hA u v]
    intro hzero
    exact huv (Subtype.ext ((l1_eq_zero_iff u.val v.val).mp hzero))

theorem grid_interval_iff {k : ℕ} (S : Finset (Fin k → ℤ))
    (hA : Challenge.GridA S) (u v x : S) :
    Challenge.InInterval (Challenge.gridGraph S) u v x ↔
      ∀ i, min (u.val i) (v.val i) ≤ x.val i ∧ x.val i ≤ max (u.val i) (v.val i) := by
  change (Challenge.gridGraph S).dist u x + (Challenge.gridGraph S).dist x v =
    (Challenge.gridGraph S).dist u v ↔ _
  rw [hA u x, hA x v, hA u v]
  exact l1_interval_iff u.val v.val x.val

theorem triple_interval_iff {k : ℕ} (S : Finset (Fin k → ℤ))
    (hA : Challenge.GridA S) (u v w x : S) :
    (Challenge.InInterval (Challenge.gridGraph S) u v x ∧
      Challenge.InInterval (Challenge.gridGraph S) u w x ∧
      Challenge.InInterval (Challenge.gridGraph S) v w x) ↔
      (x : Fin k → ℤ) = Challenge.medPt u v w := by
  constructor
  · rintro ⟨huv, huw, hvw⟩
    funext i
    exact (median_between_iff (u.val i) (v.val i) (w.val i) (x.val i)).mp
      ⟨(grid_interval_iff S hA u v x).mp huv i,
        (grid_interval_iff S hA u w x).mp huw i,
        (grid_interval_iff S hA v w x).mp hvw i⟩
  · intro hx
    have hcoord : ∀ i,
        (min (u.val i) (v.val i) ≤ x.val i ∧ x.val i ≤ max (u.val i) (v.val i)) ∧
        (min (u.val i) (w.val i) ≤ x.val i ∧ x.val i ≤ max (u.val i) (w.val i)) ∧
        (min (v.val i) (w.val i) ≤ x.val i ∧ x.val i ≤ max (v.val i) (w.val i)) := by
      intro i
      exact (median_between_iff (u.val i) (v.val i) (w.val i) (x.val i)).mpr (congrFun hx i)
    exact ⟨(grid_interval_iff S hA u v x).mpr (fun i => (hcoord i).1),
      (grid_interval_iff S hA u w x).mpr (fun i => (hcoord i).2.1),
      (grid_interval_iff S hA v w x).mpr (fun i => (hcoord i).2.2)⟩

theorem grid_median {k : ℕ} (S : Finset (Fin k → ℤ))
    (hne : S.Nonempty) (hA : Challenge.GridA S) (hB : Challenge.GridB S) :
    Challenge.IsMedian (Challenge.gridGraph S) := by
  refine ⟨grid_connected S hne hA, ?_⟩
  intro u v w
  let m : S := ⟨Challenge.medPt u v w, hB u.val v.val w.val u.property v.property w.property⟩
  refine ⟨m, (triple_interval_iff S hA u v w m).mpr rfl, ?_⟩
  intro x hx
  apply Subtype.ext
  exact (triple_interval_iff S hA u v w x).mp hx

theorem l1_cast {k : ℕ} (u v : Fin k → ℤ) :
    (Challenge.l1 u v : ℤ) = ∑ i, |u i - v i| := by
  simp only [Challenge.l1, Nat.cast_sum, Int.natCast_natAbs]

theorem grid_triple_formula {k : ℕ} (S : Finset (Fin k → ℤ))
    (hA : Challenge.GridA S) (u v w : S) :
    (Challenge.triDist (Challenge.gridGraph S) u v w : ℤ) =
      2 * ∑ i, (max (max (u.val i) (v.val i)) (w.val i) -
        min (min (u.val i) (v.val i)) (w.val i)) := by
  unfold Challenge.triDist
  rw [hA u v, hA u w, hA v w]
  simp only [Nat.cast_add, l1_cast]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact abs_triple_formula (u.val i) (v.val i) (w.val i)

end GridInterval

theorem check_Lemma1 : Challenge.Lemma1 := by
  intro k S hne hA hB
  exact ⟨GridInterval.grid_median S hne hA hB,
    GridInterval.triple_interval_iff S hA, GridInterval.grid_triple_formula S hA⟩

#print axioms check_Lemma1
end CodexPaper4
