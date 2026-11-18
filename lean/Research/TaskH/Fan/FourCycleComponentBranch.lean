import Research.TaskH.Fan.FourCyclePrefixes
import Research.TaskH.Fan.ComponentBoundaryTorso

/-! Actual Section6 four-cycle component branch, with the standard smaller-card IH. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem fourCycle_component_boundary (G : SimpleGraph V) (x u a v y : V)
    (hy : y ∉ ({x, u, a, v} : Set V))
    (hu : ¬ ∃ c ∈ outsideComponent G {x, u, a, v} y hy, G.Adj u c)
    (hv : ¬ ∃ c ∈ outsideComponent G {x, u, a, v} y hy, G.Adj v c) :
    ∀ c ∈ outsideComponent G {x, u, a, v} y hy,
      ∀ z ∉ outsideComponent G {x, u, a, v} y hy,
        G.Adj c z → z = x ∨ z = a := by
  classical
  intro c hc z hz e
  by_cases hzQ : z ∈ ({x, u, a, v} : Set V)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzQ
    rcases hzQ with h | h | h | h
    · exact Or.inl h
    · exact False.elim (hu ⟨c, hc, h ▸ e.symm⟩)
    · exact Or.inr h
    · exact False.elim (hv ⟨c, hc, h ▸ e.symm⟩)
  · exact False.elim (hz (outsideComponent_closed G {x, u, a, v} y hy hc hzQ e))

theorem fourCycle_component_induction_branch [Fintype V] (G : SimpleGraph V)
    (x u a v y : V) (hG : TwoConnected G) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hxu : x ≠ u) (hxa : x ≠ a) (hxv : x ≠ v)
    (hua : u ≠ a) (huv : u ≠ v) (hav : a ≠ v)
    (exu : G.Adj x u) (eua : G.Adj u a) (eav : G.Adj a v) (evx : G.Adj v x)
    (hy : y ∉ ({x, u, a, v} : Set V))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  classical
  let Q : Set V := {x, u, a, v}
  let C := outsideComponent G Q y hy
  have hC : (G.induce C).Connected := outsideComponent_connected G Q y hy
  have hyC : y ∈ C := outsideComponent_root_mem G Q y hy
  have hout : ∀ z ∈ Q, z ∉ C := by
    intro z hz hc
    exact outsideComponent_not_mem G Q y hy hc hz
  have hxC : x ∉ C := hout x (by simp [Q])
  have huC : u ∉ C := hout u (by simp [Q])
  have haC : a ∉ C := hout a (by simp [Q])
  have hvC : v ∉ C := hout v (by simp [Q])
  by_cases hu : ∃ z ∈ C, G.Adj u z
  · obtain ⟨r, hr, hrl, hs⟩ := connectedSet_positive_tail G C hC u y huC hyC hu
    exact fourCycle_positive_tail G x u a v y hxu hxa hxv hua huv hav
      exu eua eav evx r hr hrl
      (fun w hw hwu => outsideComponent_not_mem G Q y hy (hs w hw hwu))
  · by_cases hv : ∃ z ∈ C, G.Adj v z
    · obtain ⟨r, hr, hrl, hs⟩ := connectedSet_positive_tail G C hC v y hvC hyC hv
      have hp := fourCycle_positive_tail G x v a u y hxv hxa hxu hav.symm huv.symm hua.symm
        evx.symm eav.symm eua.symm exu.symm r hr hrl
        (fun w hw hwv => by
          have hn := outsideComponent_not_mem G Q y hy (hs w hw hwv)
          simpa only [Q, Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm,
            or_assoc] using hn)
      exact hp
    · have hbound : ∀ c ∈ C, ∀ z ∉ C, G.Adj c z → z = x ∨ z = a :=
        fourCycle_component_boundary G x u a v y hy hu hv
      obtain ⟨_hxedge, haedge⟩ := twoBoundary_both_neighbors G C hG x a y u hyC
        hxC haC huC hxu.symm hua hbound
      let : Fintype {z : V // z ∉ C} := Fintype.ofFinite _
      let xr : {z : V // z ∉ C} := ⟨x, hxC⟩
      let ur : {z : V // z ∉ C} := ⟨u, huC⟩
      let ar : {z : V // z ∉ C} := ⟨a, haC⟩
      have hxu' : xr ≠ ur := fun he => hxu (congrArg Subtype.val he)
      have hxa' : xr ≠ ar := fun he => hxa (congrArg Subtype.val he)
      have hua' : ur ≠ ar := fun he => hua (congrArg Subtype.val he)
      have hcard : 3 ≤ Fintype.card {z : V // z ∉ C} := by
        have hc : 2 < Fintype.card {z : V // z ∉ C} := Fintype.two_lt_card_iff.mpr
          ⟨xr, ur, ar, hxu', hxa', hua'⟩
        omega
      exact component_complement_induction G C hC x a y hG hdeg hxC haC hyC hxa
        hcard hbound haedge ih

#print axioms fourCycle_component_boundary
#print axioms fourCycle_component_induction_branch
end TaskH.Fan
