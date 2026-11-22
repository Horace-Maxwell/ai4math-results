import Research.TaskP.RectangleDefect.BoundaryWidths

namespace TaskP.RectangleDefect

open Challenge
open scoped BigOperators Classical

noncomputable def tally {k : ℕ} {m : Counts k} (P : Tile m → Prop) : Counts k := by
  classical
  exact fun i => ∑ j : Fin (m i), if P ⟨i,j⟩ then 1 else 0

theorem tally_weight {k : ℕ} {m : Counts k} (P : Tile m → Prop) (w : Fin k → ℕ) :
    (∑ i, w i * tally P i) = ∑ t : Tile m, if P t then w t.1 else 0 := by
  classical
  rw [Fintype.sum_sigma]
  simp only [tally, Finset.mul_sum, mul_ite, mul_one, mul_zero]

theorem area_tally {k : ℕ} {m : Counts k} (P : Tile m → Prop) :
    area (tally P) = ∑ t : Tile m, if P t then t.1.val+1 else 0 :=
  tally_weight P _

theorem count_tally {k : ℕ} {m : Counts k} (P : Tile m → Prop) :
    (∑ i, tally P i) = ∑ t : Tile m, if P t then 1 else 0 := by
  simpa using tally_weight P (fun _ => 1)

theorem rowSplit_of_tiles {k n : ℕ} {m : Counts k} (hm : area m = 2*n)
    (htiles : tiles m n) : RowSplit m n := by
  classical
  obtain ⟨anchor, dir, cov, dis⟩ := htiles
  let a := fun t => (anchor t).1
  let b := fun t => (anchor t).2
  let h := fun t => (tileSize dir t).1
  let w := fun t => (tileSize dir t).2
  have hh (t : Tile m) : 1 ≤ h t := by cases hd : dir t <;> simp [h,tileSize,hd]
  have hw (t : Tile m) : 0 ≤ w t := by
    cases hd : dir t <;> simp [w,tileSize,hd]
    positivity
  obtain ⟨bounds, sumSide⟩ := boundary_widths a b h w n hh hw cov dis
  let T := fun t => a t ≠ 0
  let V := fun t : Tile m => a t = 0 ∧ dir t = true ∧ t.1.val + 1 = 2
  let B := fun t => a t = 0 ∧ ¬ V t
  have partition (i : Fin k) : tally T i + tally B i + tally V i = m i := by
    simp only [tally, ← Finset.sum_add_distrib]
    calc ∑ j : Fin (m i), _ = ∑ _j : Fin (m i), 1 := by
           apply Finset.sum_congr rfl
           intro j _
           by_cases ha : a ⟨i,j⟩ = 0 <;> by_cases hv : V ⟨i,j⟩ <;> simp_all [T,B,V]
         _ = _ := by simp
  have vsize (i : Fin k) : tally V i ≠ 0 → i.val+1=2 := by
    contrapose!
    intro hn
    have hn' : i.val ≠ 1 := by omega
    simp [tally, V, hn']
  have horizontal (t : Tile m) (ht : B t) : w t = (t.1.val+1 : ℕ) := by
    by_cases hd : dir t = true
    · have limit := (bounds t).2
      have ht0 := ht.1
      have hhreal : h t = (t.1.val+1 : ℕ) := by simp [h,tileSize,hd]
      have hnat : t.1.val+1 ≤ 2 := by exact_mod_cast (show ((t.1.val+1 : ℕ) : ℝ) ≤ 2 by linarith)
      have h2 : t.1.val+1 ≠ 2 := fun he => ht.2 ⟨ht.1,hd,he⟩
      have h1 : t.1.val+1 = 1 := by omega
      simp [w,tileSize,hd,h1]
    · simp [w,tileSize, Bool.eq_false_iff.mpr hd]
  have vertWidth (t : Tile m) (hv : V t) : w t = 1 := by simp [w,tileSize,hv.2.1]
  have bottom : area (tally B) + (∑ i, tally V i) = n := by
    rw [area_tally, count_tally, ← Finset.sum_add_distrib]
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [← sumSide, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hv : V t
    · have ha := hv.1
      simp [B, hv, ha, vertWidth t hv]
    · by_cases ha : a t = 0
      · have hb : B t := ⟨ha,hv⟩
        simp [hb,hv,ha,horizontal t hb]
      · simp [B,ha,hv]
  have varea : area (tally V) = 2 * (∑ i, tally V i) := by
    unfold area
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : tally V i = 0
    · simp [hz]
    · rw [vsize i hz]
  have areas : area (tally T) + area (tally B) + area (tally V) = area m := by
    simp only [area, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add, ← Nat.mul_add, partition]
  exact ⟨tally T,tally B,tally V,partition,vsize, by omega, bottom⟩

end TaskP.RectangleDefect
