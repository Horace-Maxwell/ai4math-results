import Research.TaskT.HellyFive.PlanarObstructionCross
import Research.TaskT.HellyFive.UpperCharge

namespace TaskT.HellyFive.PlanarObstruction
open UpperFive

private theorem residue_of_same {n : ℕ} {a b : Grid n} (h : sameParity a b) : residue a=residue b := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr (h i)

/-- Opposite arms of a cross have the same residue; its center has another
residue if every residue of the five-point set has multiplicity at most two. -/
private theorem center_distinct {n : ℕ} {X : Finset (Grid n)} (c : Cross X)
    (bound : ∀ k, (fiber X k).card ≤ 2) {i j : Fin 5} (hi : i≠0) (hj : j≠0) (hij : i≠j)
    (hdiag : ∀ t, c.point i t+c.point j t=2*c.point 0 t) :
    ¬sameParity (c.point i) (c.point 0) := by
  intro h
  have h2 : sameParity (c.point j) (c.point 0) := by
    intro t; have := hdiag t; have := h t; omega
  let s : Finset (Grid n) := {c.point 0,c.point i,c.point j}
  have sub : s ⊆ fiber X (residue (c.point 0)) := by
    intro z hm
    simp only [s,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(c.covers _).2 ⟨0,rfl⟩,rfl⟩
    · exact Finset.mem_filter.mpr ⟨(c.covers _).2 ⟨i,rfl⟩,residue_of_same h⟩
    · exact Finset.mem_filter.mpr ⟨(c.covers _).2 ⟨j,rfl⟩,residue_of_same h2⟩
  have hcard : s.card=3 := by
    simp [s, c.injective.ne hi.symm, c.injective.ne hj.symm,c.injective.ne hij]
  have := (Finset.card_le_card sub).trans (bound _)
  omega

private theorem clash {n : ℕ} {X S : Finset (Grid n)} (c : Cross X) (incl : X ⊆ S)
    (bound : ∀ k, (fiber X k).card ≤ 2) (many : 3 ≤ (fiber S (residue (c.point 1))).card)
    (mid : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → sameParity a b → gridMid a b ∈ X) : False := by
  classical
  let p := c.point
  change 3 ≤ (fiber S (residue (p 1))).card at many
  have pa : sameParity (p 1) (p 2) := by
    intro i; have := c.diagonalA i; change p 1 i + p 2 i = 2*p 0 i at this; omega
  have pb : sameParity (p 3) (p 4) := by
    intro i; have := c.diagonalB i; change p 3 i + p 4 i = 2*p 0 i at this; omega
  have ha0 : ¬sameParity (p 1) (p 0) := center_distinct c bound (by decide) (by decide : (2:Fin 5)≠0) (by decide) c.diagonalA
  have hb0 : ¬sameParity (p 3) (p 0) := center_distinct c bound (by decide) (by decide : (4:Fin 5)≠0) (by decide) c.diagonalB
  obtain ⟨z,hz,h1,h2⟩ : ∃ z ∈ fiber S (residue (p 1)), z ≠ p 1 ∧ z ≠ p 2 := by
    by_contra! h
    have sub : fiber S (residue (p 1)) ⊆ {p 1,p 2} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases e : x = p 1
      · exact Or.inl e
      · exact Or.inr (h x hx e)
    have hc : ({p 1,p 2} : Finset _).card = 2 := by simp [p,c.injective.ne (show (1:Fin 5) ≠ 2 by decide)]
    have := Finset.card_le_card sub
    omega
  have hp1 : sameParity z (p 1) := same_of_residue (Finset.mem_filter.mp hz).2
  have hp2 : sameParity z (p 2) := fun i => (hp1 i).trans (pa i)
  let u := gridMid z (p 1)
  let v := gridMid z (p 2)
  have us : u ∈ X := mid _ (Finset.mem_filter.mp hz).1 _ (incl ((c.covers _).2 ⟨1,rfl⟩)) h1 hp1
  have vs : v ∈ X := mid _ (Finset.mem_filter.mp hz).1 _ (incl ((c.covers _).2 ⟨2,rfl⟩)) h2 hp2
  have ud (t : Fin n) : 2*u t=z t+p 1 t := double_gridMid hp1 t
  have vd (t : Fin n) : 2*v t=z t+p 2 t := double_gridMid hp2 t
  have dg (t : Fin n) : p 1 t + p 2 t = 2 * p 0 t := c.diagonalA t
  have diff (t : Fin n) : u t - v t = p 1 t - p 0 t := by have := ud t; have := vd t; have := dg t; omega
  have split {w : Grid n} (hw : w ∈ X) :
      w=p 0 ∨ sameParity w (p 1) ∨ sameParity w (p 3) := by
    obtain ⟨i,rfl⟩ := (c.covers w).1 hw
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (fun _ => rfl))
    · exact Or.inr (Or.inl (fun t => (pa t).symm))
    · exact Or.inr (Or.inr (fun _ => rfl))
    · exact Or.inr (Or.inr (fun t => (pb t).symm))
  rcases split us with eu | ua | ub
  · apply h2; funext t; have hh := ud t; have := dg t; rw [eu] at hh; omega
  all_goals rcases split vs with ev | va | vb
  all_goals first
    | apply h1; funext t; have hh := vd t; have := dg t; rw [ev] at hh; omega
    | apply ha0; intro t; have := diff t; have := ua t; have := va t; omega
    | apply hb0; intro t; have := diff t; have := ua t; have := vb t; omega
    | apply hb0; intro t; have := diff t; have := ub t; have := va t; omega
    | apply ha0; intro t; have := diff t; have := ub t; have := vb t; omega

theorem impossible {n : ℕ} {S X : Finset (Grid n)} (incl : X ⊆ S) (hX : X.card=5)
    (mid : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → sameParity a b → gridMid a b ∈ X)
    (smallX : ∀ k, (fiber X k).card ≤ 2) (largeS : ∀ k, 3 ≤ (fiber S k).card)
    (four : ∃ k, 4 ≤ (fiber S k).card) : False := by
  classical
  obtain ⟨r,hr⟩ := four
  obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq hr
  let e := (T.equivFinOfCardEq ht).symm
  let v (i : Fin 4) : Grid n := (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have mem (i : Fin 4) : v i ∈ fiber S r := hT (e i).property
  have hp (i j : Fin 4) : sameParity (v i) (v j) := same_of_residue
    ((Finset.mem_filter.mp (mem i)).2.trans (Finset.mem_filter.mp (mem j)).2.symm)
  have hm (i j : Fin 4) (h : i≠j) : gridMid (v i) (v j) ∈ X := mid _
    (Finset.mem_filter.mp (mem i)).1 _ (Finset.mem_filter.mp (mem j)).1 (hv.ne h) (hp i j)
  obtain ⟨w,hw,hwp,hwm,eq⟩ := balanced_four hX v hv hp hm
  obtain ⟨c⟩ := cross_of_balanced hX w hw hwp hwm eq
  exact clash c incl smallX (largeS _) mid

/-- The unachievable planar 2+2+1 distribution when all four occupied
classes have at least three points, one with at least four. -/
theorem obstruction {s X : Finset (Grid 2)} (hX : X ⊆ s) (hk : X.card = 5)
    (cl : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → sameParity a b → gridMid a b ∈ X)
    (h2 : ∀ r, (fiber X r).card ≤ 2) (h3 : ∀ r, 3 ≤ (fiber s r).card)
    (h4 : ∃ r, 4 ≤ (fiber s r).card) : False :=
  impossible hX hk cl h2 h3 h4

end TaskT.HellyFive.PlanarObstruction
