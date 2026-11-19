import Research.TaskJ.Grid.GridClasses
import Research.TaskJ.Grid.GridEndpoints
import Research.TaskJ.Grid.GridFormula
import Research.TaskJ.Grid.GridNormalize

namespace Grid

open Challenge

theorem even_bound {ds : List ℕ} {p : List Point} (h : PositiveSides ds)
    (hp : Order ds p) (hk : 0 < evenCount ds) :
    (pathLength p : ℤ) ≤ mass ds - evenCount ds - ((2:ℤ)^(evenCount ds - 1) - 1) := by
  have hne := order_nonempty h hp
  cases p with
  | nil => contradiction
  | cons x xs =>
    have hx := radius_evenCount (length_of_mem_vertices (hp.mem_iff.mp List.mem_cons_self))
    have hy := radius_evenCount (length_of_mem_vertices (hp.mem_iff.mp List.getLastD_mem_cons))
    have he := even_loss h hp
    have hh := identity ds x xs
    rw [order_radius_sum h hp] at hh
    obtain ⟨k,hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : evenCount ds ≠ 0)
    rw [hk', pow_succ] at he
    rw [hk'] at hx hy ⊢
    simp only [Nat.succ_sub_one] 
    linarith

theorem high_upper {ds : List ℕ} {p : List Point} (h : PositiveSides ds) (hp : Order ds p)
    (ha : 3 ≤ activeCount ds) : (pathLength p : ℤ) ≤ optimumFormula ds := by
  rw [optimum_high h ha]
  by_cases he : evenCount ds = 0
  · simpa [he] using basic_bound h hp ((active_iff_large h).mp (by omega))
  · simpa [he] using even_bound h hp (by omega)

theorem optimum_narrow (d : ℕ) (hd : 1 < d) (ho : d%2=1) :
    optimumFormula [2,d] = mass [2,d] - 2 := by
  have h : PositiveSides [2,d] := by simpa [PositiveSides] using (show 0 < d by omega)
  have ha : activeCount [2,d] = 2 := by simp [activeCount, hd]
  have he : evenCount [2,d] = 1 := by simp [evenCount, ho]
  rw [optimumFormula, raw_multi h (by omega), gapFormula]
  simp [ha, he, ho]
  ring

theorem plane_upper_regular {a b : ℕ} (ha : 1 < a) (hb : 1 < b) {p : List Point}
    (hp : Order [a,b] p) (hn : ¬(a=2 ∧ b%2=1) ∧ ¬(b=2 ∧ a%2=1)) :
    (pathLength p : ℤ) ≤ optimumFormula [a,b] := by
  have h : PositiveSides [a,b] := by simp [PositiveSides]; omega
  have hc : activeCount [a,b] = 2 := by simp [activeCount, ha, hb]
  have hu := basic_bound h hp ((active_iff_large h).mp (by omega))
  rw [optimumFormula, raw_multi h (by omega), gapFormula, hc]
  by_cases ea : a%2=0 <;> by_cases eb : b%2=0
  · have he : evenCount [a,b] = 2 := by simp [evenCount, ea, eb]
    have hh := even_bound h hp (by omega)
    norm_num [he] at hh ⊢
    linarith
  · have he : evenCount [a,b] = 1 := by simp [evenCount, ea, eb]
    have hab : 4 ≤ a := by omega
    simpa [he, ea, eb, hab] using hu
  · have he : evenCount [a,b] = 1 := by simp [evenCount, ea, eb]
    have hbb : 4 ≤ b := by omega
    simpa [he, ea, eb, hbb] using hu
  · have he : evenCount [a,b] = 0 := by simp [evenCount, ea, eb]
    simpa [he] using hu

/-- The only remaining geometric input in the upper bound is the width-two odd rectangle. -/
theorem upper_of_narrow
    (narrow : ∀ d, 1 < d → d%2=1 → ∀ p, Order [2,d] p → (pathLength p : ℤ) ≤ mass [2,d] - 2) :
    LengthUpperBound := by
  have normalized (ds : List ℕ) (h : ∀ d ∈ ds, 1 < d) (p : List Point) (hp : Order ds p) :
      (pathLength p : ℤ) ≤ optimumFormula ds := by
    have hpos : PositiveSides ds := fun d hd => by have := h d hd; omega
    have hc : activeCount ds = ds.length := by
      unfold activeCount
      rw [List.filter_eq_self.mpr (fun a ha => by simpa using h a ha)]
    match ds with
    | [] =>
      have hh : p = [[]] := List.perm_singleton.mp hp
      rw [hh, optimum_empty]
      rfl
    | [d] =>
      have hd := h d (by simp)
      rw [optimum_one d hd]
      exact basic_bound hpos hp (by simp; omega)
    | [a,b] =>
      have ha := h a (by simp)
      have hb := h b (by simp)
      by_cases h₁ : a=2 ∧ b%2=1
      · obtain ⟨rfl,ho⟩ := h₁
        rw [optimum_narrow b hb ho]
        exact narrow b hb ho p hp
      by_cases h₂ : b=2 ∧ a%2=1
      · obtain ⟨rfl,ho⟩ := h₂
        obtain ⟨q,hq,hl⟩ := (Transport.BoxMap.swap a 2 []).transport_order hp
        have he : ([a,2] : List ℕ).Perm [2,a] := List.Perm.swap _ _ _
        rw [Transport.optimum_perm he, optimum_narrow a ha ho, ← hl]
        exact narrow a ha ho q hq
      exact plane_upper_regular ha hb hp ⟨h₁,h₂⟩
    | a::b::c::ds => exact high_upper hpos hp (by simp [hc])
  intro ds h p hp
  obtain ⟨⟨f⟩,_⟩ := Transport.strip_maps ds
  obtain ⟨q,hq,hl⟩ := f.transport_order hp
  rw [← Transport.optimum_effective ds h, ← hl]
  apply normalized _ _ q hq
  intro d hd
  obtain ⟨hm,he⟩ := List.mem_filter.mp hd
  have := h d hm
  simp at he
  omega

end Grid
