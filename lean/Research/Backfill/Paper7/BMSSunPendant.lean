import Research.Backfill.Paper7.BMSPendantDecomposition
import Research.Backfill.Paper7.SunGraphAdjacency

/-! Actual list-entry path witnesses in the frozen SunV model. -/
set_option autoImplicit false
noncomputable section
namespace Paper7BMS
open BackfillPaper7.Challenge Paper7Cleared

def sunPendantVertex (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) : Fin ((L k).get j + 1) → SunV b L :=
  Fin.cases (Sum.inl k) (fun a => Sum.inr ⟨k, j, a⟩)
#print axioms Paper7BMS.sunPendantVertex

theorem sunPendantVertex_zero (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) : sunPendantVertex b L k j 0 = Sum.inl k := rfl
#print axioms Paper7BMS.sunPendantVertex_zero

theorem sunPendantVertex_succ (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    sunPendantVertex b L k j a.succ = Sum.inr ⟨k, j, a⟩ := rfl
#print axioms Paper7BMS.sunPendantVertex_succ

theorem sunPendantVertex_injective (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) : Function.Injective (sunPendantVertex b L k j) := by
  intro a c h
  cases a using Fin.cases with
  | zero =>
    cases c using Fin.cases with
    | zero => rfl
    | succ c => simp [sunPendantVertex] at h
  | succ a =>
    cases c using Fin.cases with
    | zero => simp [sunPendantVertex] at h
    | succ c =>
      rw [sunPendantVertex_succ, sunPendantVertex_succ,
        sun_same_arm_vertex_eq_iff] at h
      exact congrArg Fin.succ h
#print axioms Paper7BMS.sunPendantVertex_injective

theorem sunPendantVertex_neighbors (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) (i : Fin ((L k).get j + 1)) (hi : 0 < i.val)
    (w : SunV b L) :
    (sunGraph b L).Adj (sunPendantVertex b L k j i) w ↔
      ∃ r : Fin ((L k).get j + 1),
        (i.val+1 = r.val ∨ r.val+1 = i.val) ∧ w = sunPendantVertex b L k j r := by
  cases i using Fin.cases with
  | zero => simp only [Fin.val_zero] at hi; omega
  | succ a =>
    rw [sunPendantVertex_succ]
    constructor
    · intro h
      rcases w with l | ⟨l, r, c⟩
      · obtain ⟨hk, ha⟩ := (sun_arm_root_adj_iff b L l k j a).mp h
        subst l
        exact ⟨0, Or.inr (by simp only [Fin.val_zero, Fin.val_succ]; omega), rfl⟩
      · obtain ⟨hk, hj, ha⟩ := (sun_arm_adj_iff b L k l j r a c).mp h
        subst l
        have hj' : j = r := Fin.ext hj
        subst r
        exact ⟨c.succ, by simp only [Fin.val_succ]; omega, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      cases r using Fin.cases with
      | zero =>
        rw [sunPendantVertex_zero, sun_arm_root_adj_iff]
        exact ⟨rfl, by simp only [Fin.val_zero, Fin.val_succ] at hr; omega⟩
      | succ c =>
        rw [sunPendantVertex_succ, sun_arm_adj_iff]
        exact ⟨rfl, rfl, by simp only [Fin.val_succ] at hr; omega⟩
#print axioms Paper7BMS.sunPendantVertex_neighbors

theorem sun_hasPendantPath_get (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) : HasPendantPath (sunGraph b L) ((L k).get j) := by
  refine ⟨sunPendantVertex b L k j, sunPendantVertex_injective b L k j, ?_, ?_⟩
  · intro i
    rw [(sunGraph b L).adj_comm]
    apply (sunPendantVertex_neighbors b L k j i.succ (by
      change 0 < i.val + 1
      exact Nat.succ_pos i.val)
      (sunPendantVertex b L k j i.castSucc)).mpr
    exact ⟨i.castSucc, Or.inr rfl, rfl⟩
  · exact sunPendantVertex_neighbors b L k j
#print axioms Paper7BMS.sun_hasPendantPath_get

theorem sun_hasPendantPath (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (t : ℕ) (ht : t ∈ L k) : HasPendantPath (sunGraph b L) t := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ht
  rw [← hj]
  exact sun_hasPendantPath_get b L k j
#print axioms Paper7BMS.sun_hasPendantPath

theorem bms_sun : BMSTheorem21 := by
  intro b L _ h
  obtain ⟨k, t, ht, hthree⟩ := h
  have hg := bms_general (SunV b L) (sunGraph b L) t hthree
    (sun_hasPendantPath b L k t ht)
  exact ⟨hg.1, hg.2.1⟩
#print axioms Paper7BMS.bms_sun

theorem only_p1_p2 : OnlyP1P2 := by
  intro b L hb hG k t ht
  by_contra hn
  have hthree : 3 ≤ t := by omega
  have h := bms_sun b L hb ⟨k, t, ht, hthree⟩
  exact sharp_positive_interval_not_integral (sunGraph b L) h.1 hG
#print axioms Paper7BMS.only_p1_p2

end Paper7BMS
