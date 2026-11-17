import Research.TaskH.Six.EqualityShortCycles

/-!
Actual deleted-color injectivity for every genuine six-cycle. The proof
uses a saturated good witness, derives word injectivity, and transports
vertices along equality of actual unoriented edge sets. Rainbow is a proved
conclusion of the original equality hypotheses, never an extra premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six.GoodCycles

open SimpleGraph _root_.TaskH.ColorWords _root_.TaskH.Six.ColorWords

variable {V : Type u} {G : SimpleGraph V} {v : V}

theorem mem_support_exists_getVert_fin_six {x y : V}
    (p : G.Walk x x) (hlen : p.length = 6) (hy : y ∈ p.support) :
    ∃ i : Fin 6, p.getVert i.val = y := by
  obtain ⟨n, hn, hnb⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  by_cases hsmall : n < 6
  · exact ⟨⟨n, hsmall⟩, hn⟩
  · have hn5 : n = 6 := by omega
    refine ⟨0, ?_⟩
    have hend : p.getVert n = x := by
      rw [hn5, ← hlen]
      exact p.getVert_length
    change p.getVert (0 : ℕ) = y
    rw [Walk.getVert_zero]
    exact hend.symm.trans hn

theorem avoiding_word_color_eq {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk x x) (hv : v ∉ p.support) (a : {z : V // z ≠ v})
    (i : ℕ) (hi : p.getVert i = a.val) : avoidingCycleWord c p hv i = c a := by
  unfold avoidingCycleWord
  apply congrArg c
  exact Subtype.ext hi

theorem raw_good_avoiding_six_cycle_rainbow {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (π : Equiv.Perm (Fin 6))
    (p : G.Walk x x) (hlen : p.length = 6) (hv : v ∉ p.support)
    (hraw : 6 * rawDescents (orderColor c π) p ≤ p.length)
    (a b : {z : V // z ≠ v}) (ha : a.val ∈ p.support) (hb : b.val ∈ p.support)
    (he : c a = c b) : a = b := by
  let w := avoidingCycleWord c p hv
  have hne : ∀ i : ℕ, i < 6 → π (w i) ≠ π (w (i + 1)) := by
    intro i hi
    exact π.injective.ne (avoidingCycleWord_adj c p hv i (by omega))
  have hclosed : π (w 6) = π (w 0) := by
    apply congrArg π
    simpa only [hlen] using avoidingCycleWord_closed c p hv
  have hcount : descents (fun i => π (w i)) 6 ≤ 1 := by
    rw [rawDescents_eq_avoidingWord c π p hv, hlen] at hraw
    change 6 * descents (fun i => π (w i)) 6 ≤ 6 at hraw
    exact (by omega)
  have hsurj : Function.Surjective (fun i : Fin 6 => π (w i.val)) :=
    six_closed_prefix_surjective (fun i => π (w i)) 6 1 (by decide) (by decide)
      hne hclosed hcount
  have hinj : Function.Injective (fun i : Fin 6 => π (w i.val)) :=
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, rfl⟩).1
  obtain ⟨i, hi⟩ := mem_support_exists_getVert_fin_six p hlen ha
  obtain ⟨j, hj⟩ := mem_support_exists_getVert_fin_six p hlen hb
  have hia : w i.val = c a := avoiding_word_color_eq c p hv a i.val hi
  have hjb : w j.val = c b := avoiding_word_color_eq c p hv b j.val hj
  have hij : i = j := hinj (congrArg π (hia.trans (he.trans hjb.symm)))
  apply Subtype.ext
  exact hi.symm.trans ((congrArg (fun t : Fin 6 => p.getVert t.val) hij).trans hj)

theorem mem_deleted_support_exists_interior_index
    (p : G.Walk v v) (hlen : p.length = 6) (a : {z : V // z ≠ v})
    (ha : a.val ∈ p.support) : ∃ i : Fin 5, p.getVert (i.val + 1) = a.val := by
  obtain ⟨n, hn, hnb⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  have hn0 : n ≠ 0 := by
    intro hz
    apply a.property
    simpa only [hz, Walk.getVert_zero] using hn.symm
  have hn5 : n ≠ 6 := by
    intro hz
    apply a.property
    have hend : p.getVert n = v := by
      rw [hz, ← hlen]
      exact p.getVert_length
    exact hn.symm.trans hend
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  change p.getVert (n - 1 + 1) = a.val
  have hs : n - 1 + 1 = n := by omega
  simpa only [hs] using hn

theorem deleted_word_color_eq
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = 6)
    (a : {z : V // z ≠ v}) (i : Fin 5) (hi : p.getVert (i.val + 1) = a.val) :
    deletedCycleWord c p hp i.val = c a := by
  unfold deletedCycleWord
  have hib : i.val + 1 < p.length := by have := i.isLt; omega
  rw [dite_eq_left hib]
  apply congrArg c
  exact Subtype.ext hi

theorem raw_good_deleted_six_cycle_rainbow
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (π : Equiv.Perm (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = 6)
    (hraw : 6 * rawDescents (orderColor c π) p ≤ p.length)
    (a b : {z : V // z ≠ v}) (ha : a.val ∈ p.support) (hb : b.val ∈ p.support)
    (he : c a = c b) : a = b := by
  let w := deletedCycleWord c p hp
  have hne : ∀ i : ℕ, i < 4 → w i ≠ w (i + 1) := by
    intro i hi
    exact deletedCycleWord_adj c p hp i (by omega)
  have hcount : descents (fun i => π (w i)) 4 ≤ 0 := by
    rw [rawDescents_eq_deletedWord c π p hp, hlen] at hraw
    change 6 * (1 + descents (fun i => π (w i)) 4) ≤ 6 at hraw
    exact (by omega)
  have hinj : Function.Injective (fun i : Fin 5 => π (w i.val)) :=
    (ranked_prefix_strictMono (by decide) w π 4 0 (by decide) hne hcount).injective
  obtain ⟨i, hi⟩ := mem_deleted_support_exists_interior_index p hlen a ha
  obtain ⟨j, hj⟩ := mem_deleted_support_exists_interior_index p hlen b hb
  have hia : w i.val = c a := deleted_word_color_eq c p hp hlen a i hi
  have hjb : w j.val = c b := deleted_word_color_eq c p hp hlen b j hj
  have hij : i = j := hinj (congrArg π (hia.trans (he.trans hjb.symm)))
  apply Subtype.ext
  exact hi.symm.trans ((congrArg (fun t : Fin 5 => p.getVert (t.val + 1)) hij).trans hj)

theorem raw_good_six_cycle_rainbow {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (π : Equiv.Perm (Fin 6))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = 6)
    (hraw : 6 * rawDescents (orderColor c π) p ≤ p.length)
    (a b : {z : V // z ≠ v}) (ha : a.val ∈ p.support) (hb : b.val ∈ p.support)
    (he : c a = c b) : a = b := by
  classical
  by_cases hv : v ∈ p.support
  · let q := p.rotate v hv
    have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
    have hqlen : q.length = 6 := by simpa only [q, Walk.length_rotate] using hlen
    have hqraw : 6 * rawDescents (orderColor c π) q ≤ q.length := by
      simpa only [q, rawDescents_rotate, Walk.length_rotate] using hraw
    exact raw_good_deleted_six_cycle_rainbow c π q hq hqlen hqraw a b
      ((Walk.mem_support_rotate_iff p v hv).mpr ha)
      ((Walk.mem_support_rotate_iff p v hv).mpr hb) he
  · exact raw_good_avoiding_six_cycle_rainbow c π p hlen hv hraw a b ha hb he

theorem cycle_mem_support_of_edgeSet_eq {x y z : V} {p : G.Walk x x} {q : G.Walk y y}
    (hp : p.IsCycle) (hq : q.IsCycle) (he : p.edgeSet = q.edgeSet)
    (hz : z ∈ p.support) : z ∈ q.support := by
  have hsg := CycleOrientation.toSubgraph_eq_of_edgeSet_eq hp.not_nil hq.not_nil he
  apply q.mem_verts_toSubgraph.mp
  rw [← hsg]
  exact p.mem_verts_toSubgraph.mpr hz

end TaskH.Six.GoodCycles

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six.GoodCycles

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_rainbowSixCycles (hcrit : IsCriticalPlus 6 G)
    (hcount : modCycleCount 6 G = 420) : RainbowSixCycles G := by
  classical
  intro v c x p hp hlen a b ha hb he
  let s := p.edges.toFinset
  have hs : s ∈ ModCycleEdgeSets 6 G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr
      (by simpa only [hlen] using (dvd_refl 6))
  have hsat := equality_good_orders_saturated (critical_not_colorable hcrit) hcount c s hs
  have hpos : 0 < (goodCycleOrders c s).card := by omega
  obtain ⟨π, hπ⟩ := Finset.card_pos.mp hpos
  obtain ⟨y, q, hq, hqs, hd, hraw⟩ := (mem_goodCycleOrders c s π).mp hπ
  have hqlen : q.length = 6 := equality_shortSixCycles hcrit hcount q hq hd
  have hset : p.edgeSet = q.edgeSet := p.coe_edges_toFinset.symm.trans hqs.symm
  exact raw_good_six_cycle_rainbow c π q hq hqlen hraw a b
    (cycle_mem_support_of_edgeSet_eq hp hq hset ha)
    (cycle_mem_support_of_edgeSet_eq hp hq hset hb) he

end TaskH.Six

#print axioms TaskH.Six.GoodCycles.mem_support_exists_getVert_fin_six
#print axioms TaskH.Six.GoodCycles.avoiding_word_color_eq
#print axioms TaskH.Six.GoodCycles.raw_good_avoiding_six_cycle_rainbow
#print axioms TaskH.Six.GoodCycles.mem_deleted_support_exists_interior_index
#print axioms TaskH.Six.GoodCycles.deleted_word_color_eq
#print axioms TaskH.Six.GoodCycles.raw_good_deleted_six_cycle_rainbow
#print axioms TaskH.Six.GoodCycles.raw_good_six_cycle_rainbow
#print axioms TaskH.Six.GoodCycles.cycle_mem_support_of_edgeSet_eq
#print axioms TaskH.Six.equality_rainbowSixCycles
