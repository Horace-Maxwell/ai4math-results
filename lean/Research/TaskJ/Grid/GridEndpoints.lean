import Research.TaskJ.Grid.GridMass
import Research.TaskJ.Grid.GridSigns
import Mathlib.Data.List.Nodup

namespace Grid

open Challenge

theorem vertices_nodup (ds : List ℕ) : (vertices ds).Nodup := by
  induction ds with
  | nil => simp [vertices]
  | cons d ds ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun a _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    apply (List.nodup_range (n := d)).imp
    intro a b hab x hx hy
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hy
    exact hab (List.cons.inj hv).1.symm

theorem manhattan_zero {x y : Point} (h : x.length = y.length) (hz : manhattan x y = 0) : x = y := by
  induction x generalizing y with
  | nil => simpa using h.symm
  | cons x xs ih =>
    cases y with
    | nil => simp at h
    | cons y ys =>
      rw [manhattan_cons] at hz
      have hxy := Nat.eq_of_dist_eq_zero (show Nat.dist x y = 0 by omega)
      have ht := ih (by simpa using h) (by omega)
      rw [hxy, ht]

theorem order_nonempty {ds : List ℕ} {p : List Point} (h : PositiveSides ds)
    (hp : Order ds p) : p ≠ [] := by
  have hl := hp.length_eq
  rw [length_vertices] at hl
  have hpos := List.prod_pos_iff_forall_pos_nat.mpr h
  intro he
  simp_all

theorem end_radius_ge_two {ds : List ℕ} {x : Point} {xs : List Point}
    (hp : Order ds (x :: xs)) (h₂ : 2 ≤ ds.prod) :
    2 ≤ radius ds x + radius ds (xs.getLastD x) := by
  have hh := hp.length_eq
  rw [length_vertices, List.length_cons] at hh
  cases xs with
  | nil => simp at hh; omega
  | cons y ys =>
    have hm : (y :: ys).getLastD x ∈ y :: ys := by
      simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (a := y) (l := ys))
    have hx := length_of_mem_vertices (hp.mem_iff.mp (List.mem_cons_self))
    have hy := length_of_mem_vertices (hp.mem_iff.mp (List.mem_cons_of_mem x hm))
    have hd := hp.nodup_iff.mpr (vertices_nodup ds)
    have hn : x ≠ (y :: ys).getLastD x := fun he => (List.nodup_cons.mp hd).1 (he ▸ hm)
    have hmpos : 0 < manhattan x ((y :: ys).getLastD x) := by
      by_contra! hz
      exact hn (manhattan_zero (hx.trans hy.symm) (by omega))
    have hdef := defect_nonneg hx hy
    unfold defect at hdef
    omega

theorem basic_bound {ds : List ℕ} {p : List Point} (h : PositiveSides ds)
    (hp : Order ds p) (h₂ : 2 ≤ ds.prod) :
    (pathLength p : ℤ) ≤ mass ds - 1 := by
  have hne := order_nonempty h hp
  cases p with
  | nil => contradiction
  | cons x xs =>
    have hh := identity ds x xs
    rw [order_radius_sum h hp] at hh
    have he := end_radius_ge_two hp h₂
    have hl := edgeLoss_nonneg (fun z hz => length_of_mem_vertices (hp.mem_iff.mp hz))
    omega

end Grid
