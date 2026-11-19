import Research.TaskJ.Grid.GridMass
import Research.TaskJ.Grid.GridSigns

namespace Grid

open Challenge

theorem active_cons (d : ℕ) (ds : List ℕ) : activeCount (d :: ds) =
    if 1 < d then activeCount ds + 1 else activeCount ds := by
  by_cases hd : 1 < d <;> simp [activeCount, hd]

theorem active_iff_large {ds : List ℕ} (h : PositiveSides ds) :
    0 < activeCount ds ↔ 1 < ds.prod := by
  induction ds with
  | nil => simp [activeCount]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : PositiveSides ds := fun a ha => h a (by simp [ha])
    have hp := List.prod_pos_iff_forall_pos_nat.mpr ht
    have hh := ih ht
    rw [active_cons, List.prod_cons]
    by_cases he : 1 < d
    · simp only [he, ite_true, Nat.zero_lt_succ, true_iff]
      nlinarith
    · have heq : d = 1 := by omega
      simp [heq, hh]

theorem multiplicity_gt_one {ds : List ℕ} (h : PositiveSides ds)
    (ha : 2 ≤ activeCount ds) {d : ℕ} (hd : d ∈ ds) : 1 < ds.prod/d := by
  have he := List.perm_cons_erase hd
  have hp := he.prod_eq
  have hc : activeCount ds = activeCount (d :: ds.erase d) := (he.filter _).length_eq
  have ht : PositiveSides (ds.erase d) := fun a hmem => h a (List.mem_of_mem_erase hmem)
  have hr : 0 < activeCount (ds.erase d) := by
    rw [active_cons] at hc
    split at hc <;> omega
  have hl := (active_iff_large ht).mp hr
  rwa [hp, List.prod_cons, Nat.mul_div_cancel_left _ (h d hd)]

private theorem raw_eq_mass_aux (n : ℕ) (ds : List ℕ) (h : ∀ d ∈ ds, 1 < n/d) :
    (ds.map (rawTerm n)).sum = massAt n ds - evenCount ds := by
  induction ds with
  | nil => simp [massAt, evenCount]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : ∀ a ∈ ds, 1 < n/a := fun a ha => h a (by simp [ha])
    change rawTerm n d + (ds.map (rawTerm n)).sum = massTerm n d + massAt n ds - evenCount (d :: ds)
    rw [ih ht, count_cons]
    have hne : n/d ≠ 1 := by omega
    by_cases he : d%2=0 <;> simp [rawTerm, massTerm, hne, he] <;> ring

theorem raw_multi {ds : List ℕ} (h : PositiveSides ds) (ha : 2 ≤ activeCount ds) :
    rawUpper ds = mass ds - evenCount ds :=
  raw_eq_mass_aux ds.prod ds (fun _ hd => multiplicity_gt_one h ha hd)

theorem optimum_high {ds : List ℕ} (h : PositiveSides ds) (ha : 3 ≤ activeCount ds) :
    optimumFormula ds = mass ds - evenCount ds -
       (if evenCount ds = 0 then 1 else (2 : ℤ)^(evenCount ds - 1) - 1) := by
  rw [optimumFormula, raw_multi h (by omega), gapFormula]
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le ha
  rw [hn, Nat.add_comm 3 n]

theorem optimum_one (d : ℕ) (hd : 1 < d) :
    optimumFormula [d] = mass [d] - 1 := by
  have hh : 0 < d := by omega
  by_cases he : d%2=0 <;>
    simp [optimumFormula, gapFormula, activeCount, hd, rawUpper, rawTerm, mass, massAt,
      massTerm, Nat.div_self hh, he, show ¬ d%2=0 → d%2=1 by omega]

theorem optimum_empty : optimumFormula [] = 0 := rfl

end Grid
