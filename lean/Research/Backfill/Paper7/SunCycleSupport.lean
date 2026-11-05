import Research.Backfill.Paper7.SunGraphAdjacency

/-! A simple cycle in the actual generalized sun graph cannot enter an arm.
The proof uses a maximum depth on the finite support of the walk; no upper
bound or positivity assumption is imposed on the arm lengths. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

namespace Paper7SunMoments

theorem cycle_two_neighbors {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {u : V} (w : G.Walk u u) (hw : w.IsCycle) (x : V) (hx : x ∈ w.support) :
    ∃ y ∈ w.support, ∃ z ∈ w.support, G.Adj x y ∧ G.Adj x z ∧ y ≠ z := by
  let r := w.rotate x hx
  have hr : r.IsCycle := hw.rotate hx
  refine ⟨r.snd, ?_, r.penultimate, ?_, r.adj_snd hr.not_nil,
    (r.adj_penultimate hr.not_nil).symm, hr.snd_ne_penultimate⟩
  · exact (w.mem_support_rotate_iff x hx).mp (r.getVert_mem_support 1)
  · exact (w.mem_support_rotate_iff x hx).mp
      (r.getVert_mem_support (r.length - 1))

def sunDepth {b : ℕ} {L : Fin b → List ℕ} : SunV b L → ℕ
  | Sum.inl _ => 0
  | Sum.inr z => z.2.2.val + 1

theorem sun_arm_vertex_eq_of_coords {b : ℕ} {L : Fin b → List ℕ}
    {k k' : Fin b} {j : Fin (L k).length} {j' : Fin (L k').length}
    {a : Fin ((L k).get j)} {a' : Fin ((L k').get j')}
    (hk : k = k') (hj : j.val = j'.val) (ha : a.val = a'.val) :
    (Sum.inr ⟨k, j, a⟩ : SunV b L) = Sum.inr ⟨k', j', a'⟩ := by
  subst k'
  have hj' : j = j' := Fin.ext hj
  subst j'
  have ha' : a = a' := Fin.ext ha
  subst a'
  rfl

theorem sun_adj_depth_ne_of_pos {b : ℕ} {L : Fin b → List ℕ}
    {x y : SunV b L} (hx : 0 < sunDepth x) (hxy : (sunGraph b L).Adj x y) :
    sunDepth x ≠ sunDepth y := by
  cases x with
  | inl k => simp only [sunDepth] at hx; omega
  | inr x =>
    rcases x with ⟨k, j, a⟩
    cases y with
    | inl i => simp only [sunDepth]; omega
    | inr y =>
      rcases y with ⟨k', j', a'⟩
      have h := (Paper7Cleared.sun_arm_adj_iff b L k k' j j' a a').mp hxy
      simp only [sunDepth]
      rcases h.2.2 with h | h <;> omega

theorem sun_lower_neighbor_unique {b : ℕ} {L : Fin b → List ℕ}
    {x y z : SunV b L} (hxy : (sunGraph b L).Adj x y)
    (hxz : (sunGraph b L).Adj x z)
    (hy : sunDepth y < sunDepth x) (hz : sunDepth z < sunDepth x) : y = z := by
  cases x with
  | inl k => simp only [sunDepth] at hy; omega
  | inr x =>
    rcases x with ⟨k, j, a⟩
    cases y with
    | inl i =>
      have h1 := (Paper7Cleared.sun_arm_root_adj_iff b L i k j a).mp hxy
      cases z with
      | inl i' =>
        have h2 := (Paper7Cleared.sun_arm_root_adj_iff b L i' k j a).mp hxz
        exact congrArg Sum.inl (h1.1.symm.trans h2.1)
      | inr z =>
        rcases z with ⟨k', j', a'⟩
        have ha0 := h1.2
        simp only [sunDepth] at hz
        omega
    | inr y =>
      rcases y with ⟨ky, jy, ay⟩
      have h1 := (Paper7Cleared.sun_arm_adj_iff b L k ky j jy a ay).mp hxy
      cases z with
      | inl i =>
        have h2 := (Paper7Cleared.sun_arm_root_adj_iff b L i k j a).mp hxz
        have ha0 := h2.2
        simp only [sunDepth] at hy
        omega
      | inr z =>
        rcases z with ⟨kz, jz, az⟩
        have h2 := (Paper7Cleared.sun_arm_adj_iff b L k kz j jz a az).mp hxz
        apply sun_arm_vertex_eq_of_coords (h1.1.symm.trans h2.1)
          (h1.2.1.symm.trans h2.2.1)
        simp only [sunDepth] at hy hz
        rcases h1.2.2 with h1 | h1 <;> rcases h2.2.2 with h2 | h2 <;> omega

theorem sun_cycle_depth_zero {b : ℕ} {L : Fin b → List ℕ}
    {u : SunV b L} (w : (sunGraph b L).Walk u u) (hw : w.IsCycle)
    (v : SunV b L) (hv : v ∈ w.support) : sunDepth v = 0 := by
  let S := w.support.toFinset
  have hS : S.Nonempty := ⟨u, List.mem_toFinset.mpr w.start_mem_support⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image S sunDepth hS
  have hxw : x ∈ w.support := List.mem_toFinset.mp hx
  have hzero : sunDepth x = 0 := by
    by_contra hx0
    have hxpos : 0 < sunDepth x := Nat.pos_of_ne_zero hx0
    obtain ⟨y, hy, z, hz, hxy, hxz, hne⟩ := cycle_two_neighbors w hw x hxw
    have hym : sunDepth y ≤ sunDepth x := hmax y (List.mem_toFinset.mpr hy)
    have hzm : sunDepth z ≤ sunDepth x := hmax z (List.mem_toFinset.mpr hz)
    have hyn := sun_adj_depth_ne_of_pos hxpos hxy
    have hzn := sun_adj_depth_ne_of_pos hxpos hxz
    exact hne (sun_lower_neighbor_unique hxy hxz (by omega) (by omega))
  have hvm := hmax v (List.mem_toFinset.mpr hv)
  omega

theorem sun_cycle_support_root {b : ℕ} {L : Fin b → List ℕ}
    {u : SunV b L} (w : (sunGraph b L).Walk u u) (hw : w.IsCycle)
    (v : SunV b L) (hv : v ∈ w.support) : ∃ k : Fin b, v = Sum.inl k := by
  have hz := sun_cycle_depth_zero w hw v hv
  cases v with
  | inl k => exact ⟨k, rfl⟩
  | inr x => simp only [sunDepth] at hz; omega

end Paper7SunMoments

#print axioms Paper7SunMoments.cycle_two_neighbors
#print axioms Paper7SunMoments.sunDepth
#print axioms Paper7SunMoments.sun_arm_vertex_eq_of_coords
#print axioms Paper7SunMoments.sun_adj_depth_ne_of_pos
#print axioms Paper7SunMoments.sun_lower_neighbor_unique
#print axioms Paper7SunMoments.sun_cycle_depth_zero
#print axioms Paper7SunMoments.sun_cycle_support_root
