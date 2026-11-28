import Research.TaskV.Stanley.PeelLeaves

namespace StanleyContinuation
open SimpleGraph
open scoped Classical
noncomputable section
variable {V W : Type*} {J : SimpleGraph V} {K : SimpleGraph W} {w : V → ℕ} {z : W → ℕ}

private def fill (a : V) (b : W) (e : Away a ≃ Away b) (x : V) : W :=
  if h : x = a then b else (e ⟨x,h⟩).val

private theorem fill_at (a : V) (b : W) (e : Away a ≃ Away b) : fill a b e a = b := by
  simp [fill]

private theorem fill_away (a : V) (b : W) (e : Away a ≃ Away b) (x : Away a) :
    fill a b e x.val = (e x).val := by simp [fill,x.property]

private theorem fill_inverse (a : V) (b : W) (e : Away a ≃ Away b) (x : V) :
    fill b a e.symm (fill a b e x) = x := by
  by_cases h : x = a
  · rw [h,fill_at,fill_at]
  · let t : Away a := ⟨x,h⟩
    change fill b a e.symm (fill a b e t.val) = t.val
    rw [fill_away,fill_away,Equiv.symm_apply_apply]

private def fillEquiv (a : V) (b : W) (e : Away a ≃ Away b) : V ≃ W where
  toFun := fill a b e
  invFun := fill b a e.symm
  left_inv := fill_inverse a b e
  right_inv := fill_inverse b a e.symm

private theorem at_leaf {a v : V} (av : J.Adj a v) (leaf : ∀ x, J.Adj a x → x = v) (x : V) :
    J.Adj a x ↔ x = v := ⟨leaf x,fun h => h ▸ av⟩

/-- Extend the isomorphism of the pruned, recolored graphs across the two deleted leaves. -/
theorem reattach_tagged_leaf {a v : V} {b u : W} (av : J.Adj a v) (bu : K.Adj b u)
    (leaf : ∀ x, J.Adj a x → x = v) (leaf' : ∀ y, K.Adj b y → y = u)
    (ab : z b = w a) (unique' : ∀ y, z y = z b → y = b) (uv : z u = w v)
    (e : pruned J a ≃g pruned K b)
    (colors : ∀ x, retag (oldColors w a) ⟨v,av.ne.symm⟩ (w a) x =
      retag (oldColors z b) ⟨u,bu.ne.symm⟩ (w a) (e x)) :
    ∃ f : J ≃g K, ∀ x, w x = z (f x) := by
  classical
  let p : Away a := ⟨v,av.ne.symm⟩
  let q : Away b := ⟨u,bu.ne.symm⟩
  have fresh (x : Away b) : oldColors z b x ≠ w a := fun eq => x.property (unique' x.val (eq.trans ab.symm))
  have marked : e p = q := (retag_equal_iff _ q _ fresh (e p)).mp (by
    rw [← colors]; simp [p,retag])
  have at_p (x : Away a) : (e x).val = u ↔ x.val = v := by
    change (e x).val = q.val ↔ x.val = p.val
    rw [← Subtype.ext_iff,← Subtype.ext_iff,← marked]
    exact e.injective.eq_iff
  let f := fillEquiv a b e.toEquiv
  have fa : f a = b := fill_at .. 
  have away (x : Away a) : f x.val = (e x).val := fill_away a b e.toEquiv x
  have cross (x : Away a) : K.Adj (f a) (f x.val) ↔ J.Adj a x.val := by
    rw [fa,away,at_leaf bu leaf',at_leaf av leaf]
    exact at_p x
  let iso : J ≃g K := {
    toEquiv := f
    map_rel_iff' := by
      intro x y
      by_cases hx : x = a
      · subst x
        by_cases hy : y = a
        · subst y; simp
        · exact cross ⟨y,hy⟩
      by_cases hy : y = a
      · subst y
        exact (K.adj_comm _ _).trans ((cross ⟨x,hx⟩).trans (J.adj_comm _ _))
      let X : Away a := ⟨x,hx⟩
      let Y : Away a := ⟨y,hy⟩
      change K.Adj (f X.val) (f Y.val) ↔ J.Adj X.val Y.val
      rw [away,away]
      exact e.map_rel_iff }
  refine ⟨iso,?_⟩
  intro x
  change w x = z (f x)
  by_cases hx : x = a
  · rw [hx,fa,ab]
  let X : Away a := ⟨x,hx⟩
  change w X.val = z (f X.val)
  rw [away]
  by_cases xp : X = p
  · rw [xp,marked]; exact uv.symm
  have diff : e X ≠ q := fun h => xp (e.injective (h.trans marked.symm))
  simpa [retag,xp,diff,p,q] using colors X

end
end StanleyContinuation
