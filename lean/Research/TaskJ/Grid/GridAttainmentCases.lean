import Research.TaskJ.Grid.GridAttainmentFormula

namespace Grid.Attainment

open Challenge

def coreCost (k q base : ℕ) : ℤ :=
  if k = 0 then (if q = 0 then 0 else 2)
  else if k = 1 ∧ q = 1 ∧ base = 2 then 4 else evenCost k

theorem large_even_iff {ds : List ℕ} (hl : ds.length = 2) (he : evenCount ds = 1) :
    (∀ d ∈ ds, d%2=0 → 4 ≤ d) ↔ ∃ d ∈ ds, d%2=0 ∧ 4 ≤ d := by
  match ds with
  | [a,b] =>
    by_cases ea : a%2=0 <;> by_cases eb : b%2=0 <;> simp_all [evenCount]
  | [] | [_] | _::_::_::_ => simp at hl

theorem normalized_cost {ds : List ℕ} (h : ∀ d ∈ ds, 1 < d) (base : ℕ)
    (hb : ds.length=2 → evenCount ds=1 →
      (base=2 ↔ ¬∃ d ∈ ds, d%2=0 ∧ 4 ≤ d)) :
    requiredCost ds = coreCost (evenCount ds) (ds.length - evenCount ds) base := by
  have hpos : PositiveSides ds := fun d hd => by have := h d hd; omega
  have ha : activeCount ds = ds.length := by
    unfold activeCount
    rw [List.filter_eq_self.mpr (fun d hd => by simpa using h d hd)]
  have hle : evenCount ds ≤ ds.length := List.length_filter_le _ _
  match ds with
  | [] => rfl
  | [d] =>
    rw [single_cost d (h d (by simp))]
    have hd : evenCount [d] = 0 ∨ evenCount [d] = 1 := by simp only [List.length_cons, List.length_nil] at hle; omega
    rcases hd with hd | hd <;> norm_num [coreCost,evenCost,hd]
  | [a,b] =>
    let ds := [a,b]
    change requiredCost ds = coreCost (evenCount ds) (ds.length - evenCount ds) base
    have ha' : activeCount ds = 2 := ha
    have hl : ds.length = 2 := rfl
    have hk : evenCount ds = 0 ∨ evenCount ds = 1 ∨ evenCount ds = 2 := by
      change evenCount ds ≤ ds.length at hle
      omega
    rcases hk with hk | hk | hk
    · rw [plane_odd hpos ha' hk]
      simp [coreCost, hk, hl]
    · specialize hb hl hk
      by_cases hw : ∃ d ∈ ds, d%2=0 ∧ 4≤d
      · have hbw : base ≠ 2 := fun he => (hb.mp he) hw
        rw [plane_wide hpos ha' hk hw]
        norm_num [coreCost,evenCost,hl,hk,hbw]
      · rw [plane_narrow hpos ha' hk hw]
        norm_num [coreCost,hl,hk,hb.mpr hw]
    · rw [plane_even hpos ha' hk]
      norm_num [coreCost,hk]
  | a::b::c::rest =>
    let ds := a::b::c::rest
    change requiredCost ds = coreCost (evenCount ds) (ds.length - evenCount ds) base
    have hl : 3 ≤ ds.length := by simp [ds]
    have hc : 3 ≤ activeCount ds := by exact ha ▸ hl
    by_cases hk : evenCount ds = 0
    · rw [high_odd hpos hc hk]
      simp [coreCost,hk,show ds.length ≠ 0 by omega]
    · have hn : ¬(evenCount ds = 1 ∧ ds.length-evenCount ds = 1 ∧ base=2) := by omega
      rw [high_even hpos hc hk]
      simp [coreCost,hk,hn]
      rfl

end Grid.Attainment
