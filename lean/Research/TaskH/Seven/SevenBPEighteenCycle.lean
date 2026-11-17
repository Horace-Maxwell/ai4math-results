import Research.TaskH.Seven.SevenBPShortCycleReduction

/-! Genuine eighteen-cycle coordinates and shortest-long transport under the
actual absence of fourteen- and sixteen-cycles. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def NoSixteenCycle (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → p.length ≠ 16

def IsCycleEighteen (G : SimpleGraph V) (u : Fin 18 → V) : Prop :=
  Function.Injective u ∧ ∀ i : Fin 18, G.Adj (u i) (u (i + 1))

def cycleEighteenWalk (G : SimpleGraph V) (u : Fin 18 → V)
    (ha : ∀ i : Fin 18, G.Adj (u i) (u (i + 1))) : G.Walk (u 0) (u 0) :=
  (.cons (ha 0) (.cons (ha 1) (.cons (ha 2) (.cons (ha 3) (.cons (ha 4) (.cons (ha 5) (.cons (ha 6) (.cons (ha 7) (.cons (ha 8) (.cons (ha 9) (.cons (ha 10) (.cons (ha 11) (.cons (ha 12) (.cons (ha 13) (.cons (ha 14) (.cons (ha 15) (.cons (ha 16) (.cons (ha 17) .nil))))))))))))))))))

theorem cycleEighteenWalk_isCycle (G : SimpleGraph V) (u : Fin 18 → V)
    (hu : Function.Injective u) (ha : ∀ i : Fin 18, G.Adj (u i) (u (i + 1))) :
    (cycleEighteenWalk G u ha).IsCycle := by
  rw [cycleEighteenWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hu.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, hu.eq_iff]

theorem cycleEighteenWalk_length (G : SimpleGraph V) (u : Fin 18 → V)
    (ha : ∀ i : Fin 18, G.Adj (u i) (u (i + 1))) :
    (cycleEighteenWalk G u ha).length = 18 := rfl

theorem cycleEighteenWalk_getVert (G : SimpleGraph V) (u : Fin 18 → V)
    (ha : ∀ i : Fin 18, G.Adj (u i) (u (i + 1))) (i : Fin 18) :
    (cycleEighteenWalk G u ha).getVert i.val = u i := by
  fin_cases i <;> rfl

theorem cycleEighteenWalk_support_range (G : SimpleGraph V) (u : Fin 18 → V)
    (ha : ∀ i : Fin 18, G.Adj (u i) (u (i + 1))) (x : V) :
    x ∈ (cycleEighteenWalk G u ha).support ↔ x ∈ Set.range u := by
  constructor
  · intro hx
    obtain ⟨n, he, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hle : n ≤ 18 := by simpa only [cycleEighteenWalk_length] using hn
    by_cases hlt : n < 18
    · change (cycleEighteenWalk G u ha).getVert (⟨n, hlt⟩ : Fin 18).val = x at he
      rw [cycleEighteenWalk_getVert] at he
      exact ⟨⟨n, hlt⟩, he⟩
    · have hn18 : n = 18 := by omega
      have hnL : n = (cycleEighteenWalk G u ha).length := by
        simpa only [cycleEighteenWalk_length] using hn18
      exact ⟨0, by simpa only [hnL, Walk.getVert_length] using he⟩
  · rintro ⟨i, rfl⟩
    have hh := (cycleEighteenWalk G u ha).getVert_mem_support i.val
    simpa only [cycleEighteenWalk_getVert] using hh

theorem cycle_eighteen_is_shortest_long (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) (hl : p.length = 18) : ShortestLongCycle p := by
  refine ⟨hp, by omega, ?_⟩
  intro b q hq hq14
  by_contra hnot
  have he := Nat.even_iff.mp (closed_walk_even hb q)
  have hn14 := h14 q hq
  have hn16 := h16 q hq
  omega

theorem cycleEighteenWalk_shortest (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    ShortestLongCycle (cycleEighteenWalk G u hu.2) :=
  cycle_eighteen_is_shortest_long hb h14 h16 _
    (cycleEighteenWalk_isCycle G u hu.1 hu.2) (cycleEighteenWalk_length G u hu.2)

def rotateEighteen (u : Fin 18 → V) (a : Fin 18) : Fin 18 → V := fun i => u (a + i)

theorem rotateEighteen_isCycle (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a : Fin 18) :
    IsCycleEighteen G (rotateEighteen u a) := by
  constructor
  · intro i j he
    exact add_left_cancel (hu.1 he)
  · intro i
    simpa only [rotateEighteen, add_assoc] using hu.2 (a + i)

theorem eighteen_noncycle_adj_positions (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (i j : Fin 18)
    (ha : G.Adj (u i) (u j)) (hn : j ≠ i + 1) (hp : i ≠ j + 1) :
    j = i + 7 ∨ i = j + 7 ∨ j = i + 9 := by
  let v := rotateEighteen u i
  have hv := rotateEighteen_isCycle u hu i
  let p := cycleEighteenWalk G v hv.2
  have hs : ShortestLongCycle p := cycleEighteenWalk_shortest hb h14 h16 v hv
  let d : Fin 18 := j - i
  have hdj : i + d = j := by
    change i + (j - i) = j
    rw [add_comm i (j - i), sub_add_cancel]
  have h0 : v 0 = u i := by simp only [v, rotateEighteen, add_zero]
  have hd : p.getVert d.val = u j := by
    rw [cycleEighteenWalk_getVert]
    exact congrArg u hdj
  have hadj : G.Adj (v 0) (p.getVert d.val) := by simpa only [h0, hd] using ha
  have hx := shortest_internal_neighbor_position hb p hs d.val
    (by change d.val < 18; exact d.isLt) hadj
  have hdcase : d.val = 1 ∨ d.val = 17 ∨ d.val = 7 ∨ d.val = 9 ∨ d.val = 11 := by
    have hlen : p.length = 18 := rfl
    omega
  have tab : ∀ i j : Fin 18,
      (j - i).val = 1 ∨ (j - i).val = 17 ∨ (j - i).val = 7 ∨
        (j - i).val = 9 ∨ (j - i).val = 11 →
      j ≠ i + 1 → i ≠ j + 1 → j = i + 7 ∨ i = j + 7 ∨ j = i + 9 := by decide +kernel
  exact tab i j hdcase hn hp

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.NoSixteenCycle
#print axioms TaskH.Seven.BP.IsCycleEighteen
#print axioms TaskH.Seven.BP.cycleEighteenWalk
#print axioms TaskH.Seven.BP.cycleEighteenWalk_isCycle
#print axioms TaskH.Seven.BP.cycleEighteenWalk_length
#print axioms TaskH.Seven.BP.cycleEighteenWalk_getVert
#print axioms TaskH.Seven.BP.cycleEighteenWalk_support_range
#print axioms TaskH.Seven.BP.cycle_eighteen_is_shortest_long
#print axioms TaskH.Seven.BP.cycleEighteenWalk_shortest
#print axioms TaskH.Seven.BP.rotateEighteen
#print axioms TaskH.Seven.BP.rotateEighteen_isCycle
#print axioms TaskH.Seven.BP.eighteen_noncycle_adj_positions
