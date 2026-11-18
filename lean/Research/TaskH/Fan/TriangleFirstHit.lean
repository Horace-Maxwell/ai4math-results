import Research.TaskH.Fan.PathOperations

/-! Genuine first hit of two vertices in G-x, with an original-G positive tail. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem deleted_simple_avoiding_tail (G : SimpleGraph V) (x y p s : V)
    (hyx : y ≠ x) (hpx : p ≠ x) (hsx : s ≠ x) (hpy : p ≠ y)
    (q : (G.induce {w | w ≠ x}).Walk ⟨y, hyx⟩ ⟨p, hpx⟩) (hq : q.IsPath)
    (hs : (⟨s, hsx⟩ : {w : V // w ≠ x}) ∉ q.support) :
    ∃ r : G.Walk p y, r.IsPath ∧ 1 ≤ r.length ∧
      ∀ w, w ∈ r.support → w ≠ p → w ∉ ({x, p, s} : Set V) := by
  classical
  let q' : G.Walk y p := q.map (SimpleGraph.Embedding.induce {w | w ≠ x}).toHom
  have hmap : q'.IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hq
  let r : G.Walk p y := q'.reverse
  have hpos : 1 ≤ r.length := by
    by_contra hl
    have hz : r.length = 0 := by omega
    exact hpy (Walk.eq_of_length_eq_zero (p := r) hz)
  refine ⟨r, hmap.reverse, hpos, ?_⟩
  intro w hw hwp hwQ
  have hw' : w ∈ q'.support := by
    simpa only [r, Walk.support_reverse, List.mem_reverse] using hw
  change w ∈ (q.map (SimpleGraph.Embedding.induce {w | w ≠ x}).toHom).support at hw'
  rw [Walk.support_map] at hw'
  obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hw'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwQ
  rcases hwQ with he | he | he
  · exact z.2 (hzw.trans he)
  · exact hwp he
  · have hzs : z = (⟨s, hsx⟩ : {w : V // w ≠ x}) := Subtype.ext (hzw.trans he)
    exact hs (hzs ▸ hz)

theorem deleted_two_vertex_first_hit (G : SimpleGraph V) (x y u v : V)
    (hyx : y ≠ x) (hux : u ≠ x) (hvx : v ≠ x)
    (huy : u ≠ y) (hvy : v ≠ y) (huv : u ≠ v)
    (hconn : (G.induce {w | w ≠ x}).Connected) :
    ∃ p, (p = u ∨ p = v) ∧ ∃ r : G.Walk p y,
      r.IsPath ∧ 1 ≤ r.length ∧
        ∀ w, w ∈ r.support → w ≠ p → w ∉ ({x, u, v} : Set V) := by
  classical
  obtain ⟨q, hq⟩ := (hconn (⟨y, hyx⟩ : {w : V // w ≠ x}) ⟨u, hux⟩).exists_isPath
  by_cases hv : (⟨v, hvx⟩ : {w : V // w ≠ x}) ∈ q.support
  · have huv' : (⟨u, hux⟩ : {w : V // w ≠ x}) ≠ ⟨v, hvx⟩ :=
      fun he => huv (congrArg Subtype.val he)
    have hu : (⟨u, hux⟩ : {w : V // w ≠ x}) ∉
        (q.takeUntil ⟨v, hvx⟩ hv).support :=
      Walk.endpoint_notMem_support_takeUntil hq hv huv'
    obtain ⟨r, hr, hrl, hs⟩ := deleted_simple_avoiding_tail G x y v u hyx hvx hux hvy
      (q.takeUntil ⟨v, hvx⟩ hv) (hq.takeUntil hv) hu
    refine ⟨v, Or.inr rfl, r, hr, hrl, ?_⟩
    intro w hw hwv
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]
      using hs w hw hwv
  · obtain ⟨r, hr, hrl, hs⟩ := deleted_simple_avoiding_tail G x y u v hyx hux hvx huy q hq hv
    exact ⟨u, Or.inl rfl, r, hr, hrl, hs⟩

#print axioms deleted_simple_avoiding_tail
#print axioms deleted_two_vertex_first_hit
end TaskH.Fan
