import Research.TaskP.RectangleDefect.IntervalPacking

namespace TaskP.RectangleDefect

open Set

structure Strip (T : Type*) (w : T → ℝ) (L : ℝ) where
  start : T → ℝ
  bounds : ∀ t, 0 ≤ start t ∧ start t + w t ≤ L
  apart : ∀ t u, t ≠ u → Disjoint (Ioo (start t) (start t+w t)) (Ioo (start u) (start u+w u))
  covers : 0 < L → ∀ y ∈ Icc 0 L, ∃ t, y ∈ Icc (start t) (start t+w t)

noncomputable def mkStrip {T : Type*} [Fintype T] (w : T → ℝ) (hw : ∀ t, 0 < w t)
    (L : ℝ) (eqn : ∑ t, w t = L) : Strip T w L := by
  classical
  exact Classical.choice (by
    obtain ⟨lo, bound, sep, fill⟩ := pack_intervals (Finset.univ : Finset T) w hw
    refine ⟨⟨lo, fun t => eqn ▸ bound t (Finset.mem_univ t),
      fun t u h => sep t (Finset.mem_univ _) u (Finset.mem_univ _) h, ?_⟩⟩
    intro hl y hy
    have nonempty : (Finset.univ : Finset T).Nonempty := by
      by_contra! he
      rw [he, Finset.sum_empty] at eqn
      linarith
    obtain ⟨t, _, ht⟩ := fill nonempty y (eqn.symm ▸ hy)
    exact ⟨t, ht⟩)

abbrev Placed (T B V : Type*) := (T ⊕ B) ⊕ V

def sizeOfPlace {T B V : Type*} (u : T → ℝ) (v : B → ℝ) : Placed T B V → ℝ × ℝ
  | .inl (.inl t) => (1, u t)
  | .inl (.inr t) => (1, v t)
  | .inr _ => (2,1)

def offsetOfPlace {T B V : Type*} {u : T → ℝ} {v : B → ℝ} {L F : ℝ}
    (top : Strip T u L) (bottom : Strip B v L) (vert : Strip V (fun _ => 1) F) :
    Placed T B V → ℝ × ℝ
  | .inl (.inl t) => (0,F+top.start t)
  | .inl (.inr t) => (1,F+bottom.start t)
  | .inr t => (0,vert.start t)

def placeClosed (p d : ℝ × ℝ) := Icc p.1 (p.1+d.1) ×ˢ Icc p.2 (p.2+d.2)
def placeOpen (p d : ℝ × ℝ) := Ioo p.1 (p.1+d.1) ×ˢ Ioo p.2 (p.2+d.2)

theorem layout_closed {T B V : Type*} {u : T → ℝ} {v : B → ℝ} {L F : ℝ}
    (top : Strip T u L) (bottom : Strip B v L) (vert : Strip V (fun _ => 1) F)
    (hL : 0 ≤ L) (hF : 0 ≤ F) (hpos : 0 < F+L) :
    (⋃ t, placeClosed (offsetOfPlace top bottom vert t) (sizeOfPlace u v t)) =
      Icc 0 2 ×ˢ Icc 0 (F+L) := by
  ext p
  rcases p with ⟨x,y⟩
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, ht⟩
    rcases t with (t | t) | t
    · obtain ⟨⟨hx,hx'⟩,hy,hy'⟩ := ht
      obtain ⟨ht₀,ht₁⟩ := top.bounds t
      change 0 ≤ x at hx
      change x ≤ 0 + 1 at hx'
      change F+top.start t ≤ y at hy
      change y ≤ F+top.start t+u t at hy'
      exact ⟨⟨hx, by linarith⟩, by linarith, by linarith⟩
    · obtain ⟨⟨hx,hx'⟩,hy,hy'⟩ := ht
      obtain ⟨ht₀,ht₁⟩ := bottom.bounds t
      change (1 : ℝ) ≤ x at hx
      change x ≤ 1 + 1 at hx'
      change F+bottom.start t ≤ y at hy
      change y ≤ F+bottom.start t+v t at hy'
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · obtain ⟨⟨hx,hx'⟩,hy,hy'⟩ := ht
      obtain ⟨ht₀,ht₁⟩ := vert.bounds t
      change 0 ≤ x at hx
      change x ≤ 0 + 2 at hx'
      change vert.start t ≤ y at hy
      change y ≤ vert.start t+1 at hy'
      exact ⟨⟨hx, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨hx,hx'⟩,hy,hy'⟩
    apply Set.mem_iUnion.mpr
    by_cases hv : y ≤ F ∧ 0 < F
    · obtain ⟨t,hl,hr⟩ := vert.covers hv.2 y ⟨hy,hv.1⟩
      exact ⟨.inr t,⟨⟨hx, by simpa [offsetOfPlace,sizeOfPlace] using hx'⟩,hl,hr⟩⟩
    · have hfy : F ≤ y := by by_contra! h; exact hv ⟨h.le,lt_of_le_of_lt hy h⟩
      have hl : 0 < L := by by_contra! h; exact hv ⟨by linarith,by linarith⟩
      have ht : y-F ∈ Icc 0 L := ⟨by linarith,by linarith⟩
      by_cases hs : x ≤ 1
      · obtain ⟨t,ha,hb⟩ := top.covers hl (y-F) ht
        refine ⟨.inl (.inl t),?_⟩
        change (0 ≤ x ∧ x ≤ 0+1) ∧ F+top.start t ≤ y ∧ y ≤ F+top.start t+u t
        exact ⟨⟨hx,by linarith⟩,by linarith,by linarith⟩
      · obtain ⟨t,ha,hb⟩ := bottom.covers hl (y-F) ht
        refine ⟨.inl (.inr t),?_⟩
        change (1 ≤ x ∧ x ≤ 1+1) ∧ F+bottom.start t ≤ y ∧ y ≤ F+bottom.start t+v t
        exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem layout_open {T B V : Type*} {u : T → ℝ} {v : B → ℝ} {L F : ℝ}
    (top : Strip T u L) (bottom : Strip B v L) (vert : Strip V (fun _ => 1) F)
    (s t : Placed T B V) (hne : s ≠ t) :
    Disjoint (placeOpen (offsetOfPlace top bottom vert s) (sizeOfPlace u v s))
      (placeOpen (offsetOfPlace top bottom vert t) (sizeOfPlace u v t)) := by
  apply Set.disjoint_left.mpr
  rintro ⟨x,y⟩ hs ht
  rcases s with (s | s) | s <;> rcases t with (t | t) | t <;>
    simp only [placeOpen,offsetOfPlace,sizeOfPlace,Set.mem_prod,Set.mem_Ioo,zero_add] at hs ht
  · apply (Set.disjoint_left.mp (top.apart s t (fun e => hne (e ▸ rfl)))) (a := y-F)
    · exact ⟨by linarith [hs.2.1],by linarith [hs.2.2]⟩
    · exact ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩
  · linarith [hs.1.2,ht.1.1]
  · linarith [hs.2.1,ht.2.2,(top.bounds s).1,(vert.bounds t).2]
  · linarith [hs.1.1,ht.1.2]
  · apply (Set.disjoint_left.mp (bottom.apart s t (fun e => hne (e ▸ rfl)))) (a := y-F)
    · exact ⟨by linarith [hs.2.1],by linarith [hs.2.2]⟩
    · exact ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩
  · linarith [hs.2.1,ht.2.2,(bottom.bounds s).1,(vert.bounds t).2]
  · linarith [ht.2.1,hs.2.2,(top.bounds t).1,(vert.bounds s).2]
  · linarith [ht.2.1,hs.2.2,(bottom.bounds t).1,(vert.bounds s).2]
  · exact Set.disjoint_left.mp (vert.apart s t (fun e => hne (e ▸ rfl))) hs.2 ht.2

end TaskP.RectangleDefect
