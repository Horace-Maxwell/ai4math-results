import Research.TaskJ.Grid.GridEndpoints
import Research.TaskJ.Grid.GridNormalize
import Mathlib.Data.List.Chain

namespace Grid.Narrow

open Challenge

private def shape (m : ℕ) : List ℕ := [2, 2*m+1]

private theorem valid {m : ℕ} {p : Point} (h : p ∈ vertices (shape m)) :
    ∃ a < 2, ∃ b ≤ 2*m, p = [a,b] := by
  rcases Transport.mem_cons_box.mp h with ⟨a, ha, xs, hx, rfl⟩
  rcases Transport.mem_cons_box.mp hx with ⟨b, hb, ys, hy, rfl⟩
  simp only [vertices, List.mem_singleton] at hy
  subst ys
  exact ⟨a,ha,b,by omega,rfl⟩

private theorem vertex (m a b : ℕ) (ha : a < 2) (hb : b ≤ 2*m) : [a,b] ∈ vertices (shape m) :=
  Transport.mem_cons_box.mpr ⟨a,ha,_,Transport.mem_cons_box.mpr ⟨b,by omega,[],by simp [vertices],rfl⟩,rfl⟩

private def middle (m : ℕ) (p : Point) : Prop := p[1]? = some m
private def shade (m : ℕ) (p : Point) : Prop :=
  (p[0]? = some 0 ∧ p[1]?.getD 0 < m) ∨ (p[0]? = some 1 ∧ m < p[1]?.getD 0)

private theorem negligible_end {m : ℕ} {p : Point} (hp : p ∈ vertices (shape m)) :
    1 ≤ radius (shape m) p ∧ (radius (shape m) p = 1 ↔ middle m p) := by
  obtain ⟨a, ha, b, _, rfl⟩ := valid hp
  change 1 ≤ axisRadius 2 a + (axisRadius (2*m+1) b + 0) ∧
    (axisRadius 2 a + (axisRadius (2*m+1) b + 0) = 1 ↔ some b = some m)
  simp [axisRadius, abs_eq_max_neg]
  omega

private theorem shade_step {m : ℕ} {p q : Point}
    (hp : p ∈ vertices (shape m)) (hq : q ∈ vertices (shape m))
    (hp' : ¬ middle m p) (hq' : ¬ middle m q) (h : defect (shape m) p q = 0) :
    shade m p ↔ shade m q := by
  obtain ⟨a,ha,b,_,rfl⟩ := valid hp
  obtain ⟨c,hc,d,_,rfl⟩ := valid hq
  simp [middle] at hp' hq'
  simp [shape, defect, radius, axisRadius, manhattan, Nat.dist, abs_eq_max_neg] at h
  simp [shade]
  omega

private theorem zero_chain {ds : List ℕ} :
    ∀ p : List Point, (∀ x ∈ p, x ∈ vertices ds) → edgeLoss ds p = 0 →
      p.IsChain (fun x y => defect ds x y = 0)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: xs, hall, h => by
    have ht : ∀ a ∈ y :: xs, a ∈ vertices ds := fun a ha => hall a (List.mem_cons_of_mem x ha)
    have hxy := defect_nonneg (length_of_mem_vertices (hall x (by simp)))
      (length_of_mem_vertices (ht y (by simp)))
    have hs := edgeLoss_nonneg (fun a ha => length_of_mem_vertices (ht a ha))
    change defect ds x y + edgeLoss ds (y :: xs) = 0 at h
    exact List.isChain_cons_cons.mpr ⟨by omega, zero_chain (y::xs) ht (by omega)⟩

private theorem uniform {α : Type*} (f : α → Prop) :
    ∀ (l : List α), l.IsChain (fun a b => (f a ↔ f b)) → ∀ a ∈ l, ∀ b ∈ l, f a ↔ f b
  | [], _ => by simp
  | [x], _ => by simp
  | x :: y :: xs, h => by
    have e := List.isChain_cons_cons.mp h
    have atSecond (z : α) (hz : z ∈ x :: y :: xs) : f z ↔ f y := by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact e.1
      · exact uniform f _ e.2 z hz y (by simp)
    exact fun a ha b hb => (atSecond a ha).trans (atSecond b hb).symm

private theorem center_point {m : ℕ} {p : Point} (hp : p ∈ vertices (shape m))
    (hc : middle m p) : p = [0,m] ∨ p = [1,m] := by
  obtain ⟨a,ha,b,_,rfl⟩ := valid hp
  have hb : b = m := by simpa [middle] using hc
  subst b
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> simp

private theorem cannot_saturate {m : ℕ} (hm : 0 < m) (x z : Point) (body : List Point)
    (hp : Order (shape m) (x :: (body ++ [z]))) (hx : middle m x) (hz : middle m z)
    (loss : edgeLoss (shape m) (x :: (body ++ [z])) = 0) : False := by
  have hall : ∀ a ∈ x :: (body ++ [z]), a ∈ vertices (shape m) := fun _ e => hp.mem_iff.mp e
  have inBody (v : Point) (hv : v ∈ body) : v ∈ vertices (shape m) := hall v (by simp [hv])
  have no := hp.nodup_iff.mpr (vertices_nodup _)
  have hxz : x ≠ z := by
    intro e; subst z; exact (List.nodup_cons.mp no).1 (by simp)
  have ox := center_point (hall x (by simp)) hx
  have oz := center_point (hall z (by simp)) hz
  have away (v : Point) (hv : v ∈ body) : ¬middle m v := by
    intro hc
    have ov := center_point (inBody v hv) hc
    have ex : v ≠ x := by rintro rfl; exact (List.nodup_cons.mp no).1 (by simp [hv])
    have ez : v ≠ z := by
      rintro rfl
      exact (List.nodup_append.mp (List.nodup_cons.mp no).2).2.2 v hv v (by simp) rfl
    grind
  have hc := zero_chain _ hall loss
  have midchain := (List.isChain_append.mp hc.tail).1
  have same := midchain.imp_of_mem_imp (fun v w hv hw h => shade_step (inBody v hv) (inBody w hw) (away v hv) (away w hw) h)
  have find (v : Point) (hv : v ∈ vertices (shape m)) (ha : ¬middle m v) : v ∈ body := by
    have hh := hp.mem_iff.mpr hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | hh | rfl
    · exact False.elim (ha hx)
    · exact hh
    · exact False.elim (ha hz)
  have a := find [0,0] (vertex m 0 0 (by decide) (by omega)) (by simp [middle]; omega)
  have b := find [1,0] (vertex m 1 0 (by decide) (by omega)) (by simp [middle]; omega)
  have eqv := uniform _ _ same _ a _ b
  simp [shade,hm] at eqv

/-- The two middle vertices cannot both be endpoints of a zero-loss traversal. -/
theorem bound (m : ℕ) (hm : 0 < m) {p : List Point} (hp : Order [2,2*m+1] p) :
    (pathLength p : ℤ) ≤ mass [2,2*m+1] - 2 := by
  have pos : PositiveSides (shape m) := by simp [PositiveSides,shape]
  change Order (shape m) p at hp
  change _ ≤ mass (shape m) - 2
  have hlen := hp.length_eq
  rw [length_vertices] at hlen
  simp [shape] at hlen
  cases p with
  | nil => simp at hlen
  | cons x xs =>
    rcases List.eq_nil_or_concat xs with rfl | ⟨body,z,rfl⟩
    · simp at hlen; omega
    · rw [List.concat_eq_append] at hp ⊢
      have hx := hp.mem_iff.mp (List.mem_cons_self)
      have hz := hp.mem_iff.mp (show z ∈ x :: (body ++ [z]) by simp)
      have ex := negligible_end hx
      have ez := negligible_end hz
      have hd := identity (shape m) x (body ++ [z])
      rw [order_radius_sum pos hp] at hd
      rw [List.getLastD_concat] at hd
      have he := edgeLoss_nonneg (fun v hv => length_of_mem_vertices (hp.mem_iff.mp hv))
      by_contra! hb
      exact cannot_saturate hm x z body hp (ex.2.mp (by omega)) (ez.2.mp (by omega)) (by omega)

end Grid.Narrow
