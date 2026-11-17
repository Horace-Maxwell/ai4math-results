import Research.TaskH.Five.FiveLightEdgePathLengths

/-! The one color absent from the original five-cycle has a path of length
at least eight. The extra exclusion is a genuine ten-cycle, not a bound
imposed on the other noncommon colors. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

def lightOtherIndices : Fin 4 → Fin 5 := ![1, 2, 3, 4]

theorem lightOtherIndices_injective : Function.Injective lightOtherIndices := by
  decide +kernel

def lightPentagonOtherPath {f : Fin 5 → V} (hf : IsPentagon G f) :
    G.Walk (f 1) (f 0) :=
  .cons hf.2.2.1 (.cons hf.2.2.2.1 (.cons hf.2.2.2.2.1
    (.cons hf.2.2.2.2.2 .nil)))

theorem lightPentagonOtherPath_isPath {f : Fin 5 → V} (hf : IsPentagon G f) :
    (lightPentagonOtherPath hf).IsPath := by
  apply Walk.IsPath.mk'
  simp [lightPentagonOtherPath, Walk.support_cons, hf.1.eq_iff]

theorem lightPentagonOtherPath_length {f : Fin 5 → V} (hf : IsPentagon G f) :
    (lightPentagonOtherPath hf).length = 4 := rfl

theorem light_other_colors_injective (hr : RainbowFiveCycles G)
    {f : Fin 5 → V} (hf : IsPentagon G f)
    (c : (G.deleteEdges {s(f 0, f 1)}).Coloring (Fin 5)) :
    Function.Injective (fun j : Fin 4 => c (f (lightOtherIndices j))) := by
  let d := lightDeletedEdgeVertexColoring c
  let p := pentagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2
  have hp : p.IsCycle := pentagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2
  have hout : ∀ j : Fin 4, f (lightOtherIndices j) ≠ f 0 := by
    intro j
    apply hf.1.ne
    fin_cases j <;> decide
  have hmem : ∀ j : Fin 4, f (lightOtherIndices j) ∈ p.support := by
    intro j
    fin_cases j <;> simp [p, pentagonWalk, lightOtherIndices, Walk.support_cons]
  intro i j he
  apply lightOtherIndices_injective
  apply hf.1
  exact congrArg Subtype.val
    (hr (f 0) d p hp (by rfl)
      ⟨f (lightOtherIndices i), hout i⟩ ⟨f (lightOtherIndices j), hout j⟩
      (hmem i) (hmem j) he)

theorem light_exists_missing_color {f : Fin 5 → V}
    (c : (G.deleteEdges {s(f 0, f 1)}).Coloring (Fin 5))
    (he : c (f 0) = c (f 1)) :
    ∃ b : Fin 5, b ≠ c (f 0) ∧ ∀ j : Fin 5, c (f j) ≠ b := by
  classical
  let S : Finset (Fin 5) := Finset.univ.image
    (fun j : Fin 4 => c (f (lightOtherIndices j)))
  have hc : S.card ≤ 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
        (f := fun j => c (f (lightOtherIndices j))))
  have hlt : S.card < (Finset.univ : Finset (Fin 5)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hmiss : ∀ j : Fin 4, c (f (lightOtherIndices j)) ≠ b := by
    intro j hj
    apply hb
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have h0 : c (f 0) ≠ b := by
    intro h
    exact hmiss 0 (he.symm.trans h)
  refine ⟨b, h0.symm, ?_⟩
  intro j
  fin_cases j
  · exact h0
  · exact hmiss 0
  · exact hmiss 1
  · exact hmiss 2
  · exact hmiss 3

theorem light_path_start_not_mem_tail {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) : u ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

theorem light_swap_support_color {u v : V} (p : G.Walk u v)
    (c : V → Fin 5) (b : Fin 5) (hf : Follows p c (Equiv.swap (c u) b))
    (w : V) (hw : w ∈ p.support) : c w = c u ∨ c w = b := by
  obtain ⟨n, he, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hw
  have hc := light_swap_color_at p c b hf n hn
  rw [he] at hc
  by_cases hz : n % 2 = 0
  · exact Or.inl (by simpa only [ite_eq_left hz] using hc)
  · exact Or.inr (by simpa only [ite_eq_right hz] using hc)

theorem light_two_color_six_and_other_four_contradiction
    (hs : ShortFiveCycles G) {u v : V}
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (b : Fin 5)
    (p : (G.deleteEdges {s(u, v)}).Walk u v) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c u) b)) (hl : p.length = 6)
    (q : G.Walk v u) (hq : q.IsPath) (hql : q.length = 4)
    (hbeta : ∀ w ∈ q.support, c w ≠ b)
    (hbase : ∀ w ∈ q.support, c w = c u → w = u ∨ w = v) : False := by
  let r := p.mapLe (G.deleteEdges_le {s(u, v)})
  have hr : r.IsPath := hp.mapLe _
  have hd : r.support.tail.Disjoint q.support.tail := by
    apply List.disjoint_left.mpr
    intro w hwr hwq
    have hwp : w ∈ p.support := by
      have hwr' : w ∈ p.support.tail := by
        simpa only [r, Walk.support_mapLe_eq_support] using hwr
      exact List.mem_of_mem_tail hwr'
    have hwq' : w ∈ q.support := List.mem_of_mem_tail hwq
    have hc : c w = c u :=
      (light_swap_support_color p c b hf w hwp).resolve_right (hbeta w hwq')
    rcases hbase w hwq' hc with rfl | rfl
    · exact light_path_start_not_mem_tail hr hwr
    · exact light_path_start_not_mem_tail hq hwq
  have hc : (r.append q).IsCycle := hr.isCycle_append hq hd (Or.inr (by omega))
  have hlen : (r.append q).length = 10 := by
    simp only [r, Walk.length_append, Walk.length_mapLe, hl, hql]
  have hfive := hs (r.append q) hc (by rw [hlen]; decide)
  omega

theorem light_missing_color_other_path_constraints (hr : RainbowFiveCycles G)
    {f : Fin 5 → V} (hf : IsPentagon G f)
    (c : (G.deleteEdges {s(f 0, f 1)}).Coloring (Fin 5))
    (he : c (f 0) = c (f 1)) (b : Fin 5)
    (hmiss : ∀ j : Fin 5, c (f j) ≠ b) :
    (∀ w ∈ (lightPentagonOtherPath hf).support, c w ≠ b) ∧
    (∀ w ∈ (lightPentagonOtherPath hf).support,
      c w = c (f 0) → w = f 0 ∨ w = f 1) := by
  have hi := light_other_colors_injective hr hf c
  have hbase : ∀ j : Fin 4, c (f (lightOtherIndices j)) = c (f 0) → j = 0 := by
    intro j hj
    exact hi (hj.trans he)
  constructor
  · intro w hw
    simp only [lightPentagonOtherPath, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hmiss 1
    · exact hmiss 2
    · exact hmiss 3
    · exact hmiss 4
    · exact hmiss 0
  · intro w hw hc
    simp only [lightPentagonOtherPath, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr rfl
    · have hh := hbase 1 hc
      norm_num at hh
    · have hh := hbase 2 hc
      norm_num at hh
    · have hh := hbase 3 hc
      norm_num at hh
    · exact Or.inl rfl

theorem critical_exists_missing_color_path_eight
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) {f : Fin 5 → V} (hf : IsPentagon G f)
    (hlight : IsLightPentagonEdge G f 0)
    (c : (G.deleteEdges {s(f 0, f 1)}).Coloring (Fin 5)) :
    ∃ b : Fin 5, b ≠ c (f 0) ∧ (∀ j : Fin 5, c (f j) ≠ b) ∧
      ∃ p : (G.deleteEdges {s(f 0, f 1)}).Walk (f 0) (f 1),
        p.IsPath ∧ Follows p c (Equiv.swap (c (f 0)) b) ∧
        (∀ q : (G.deleteEdges {s(f 0, f 1)}).Walk (f 0) (f 1),
          Follows q c (Equiv.swap (c (f 0)) b) → p.length ≤ q.length) ∧
        8 ≤ p.length ∧ p.length % 2 = 0 := by
  have he := TaskH.deletedEdge_coloring_endpoints hcrit c
  obtain ⟨b, hb, hmiss⟩ := light_exists_missing_color c he
  have hno : ∀ w : V, G.Adj (f 0) w → G.Adj (f 1) w → c w ≠ b := by
    intro w hu hv
    obtain ⟨j, rfl⟩ := hlight.1 w hu hv
    exact hmiss j
  obtain ⟨p, hp, hfollow, hmin, hlen, heven⟩ :=
    critical_exists_long_noncommon_two_color_path hcrit hr hf.2.1 c b hb hno
  have hnot6 : p.length ≠ 6 := by
    intro hl
    have hc := light_missing_color_other_path_constraints hr hf c he b hmiss
    exact light_two_color_six_and_other_four_contradiction hs c b p hp hfollow hl
      (lightPentagonOtherPath hf) (lightPentagonOtherPath_isPath hf)
      (lightPentagonOtherPath_length hf) hc.1 hc.2
  exact ⟨b, hb, hmiss, p, hp, hfollow, hmin, by omega, heven⟩

end TaskH.Five

#print axioms TaskH.Five.lightOtherIndices
#print axioms TaskH.Five.lightOtherIndices_injective
#print axioms TaskH.Five.lightPentagonOtherPath
#print axioms TaskH.Five.lightPentagonOtherPath_isPath
#print axioms TaskH.Five.lightPentagonOtherPath_length
#print axioms TaskH.Five.light_other_colors_injective
#print axioms TaskH.Five.light_exists_missing_color
#print axioms TaskH.Five.light_path_start_not_mem_tail
#print axioms TaskH.Five.light_swap_support_color
#print axioms TaskH.Five.light_two_color_six_and_other_four_contradiction
#print axioms TaskH.Five.light_missing_color_other_path_constraints
#print axioms TaskH.Five.critical_exists_missing_color_path_eight
