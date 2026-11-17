import Research.TaskH.Basics

/-! Actual simple-cycle witnesses for the standalone bipartite lemma.
The closed fourteen-step walk is built from the supplied actual graph edges. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def NoFourteenCycle (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → p.length ≠ 14

def IsCycleSixteen (G : SimpleGraph V) (u : Fin 16 → V) : Prop :=
  Function.Injective u ∧ ∀ i : Fin 16, G.Adj (u i) (u (i + 1))

def cycleFourteenWalk (G : SimpleGraph V) (f : Fin 14 → V)
    (ha : ∀ i : Fin 14, G.Adj (f i) (f (i + 1))) : G.Walk (f 0) (f 0) :=
  .cons (ha 0) (.cons (ha 1) (.cons (ha 2) (.cons (ha 3) (.cons (ha 4) (.cons (ha 5) (.cons (ha 6) (.cons (ha 7) (.cons (ha 8) (.cons (ha 9) (.cons (ha 10) (.cons (ha 11) (.cons (ha 12) (.cons (ha 13) .nil)))))))))))))

theorem cycleFourteenWalk_isCycle (G : SimpleGraph V) (f : Fin 14 → V)
    (hf : Function.Injective f) (ha : ∀ i : Fin 14, G.Adj (f i) (f (i + 1))) :
    (cycleFourteenWalk G f ha).IsCycle := by
  rw [cycleFourteenWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hf.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hf.eq_iff]

theorem cycleFourteenWalk_length (G : SimpleGraph V) (f : Fin 14 → V)
    (ha : ∀ i : Fin 14, G.Adj (f i) (f (i + 1))) :
    (cycleFourteenWalk G f ha).length = 14 := rfl

theorem exists_fourteen_cycle_of_injective_adj (G : SimpleGraph V) (f : Fin 14 → V)
    (hf : Function.Injective f) (ha : ∀ i : Fin 14, G.Adj (f i) (f (i + 1))) :
    ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 14 :=
  ⟨f 0, cycleFourteenWalk G f ha, cycleFourteenWalk_isCycle G f hf ha,
    cycleFourteenWalk_length G f ha⟩

def cycleSixteenVertices {x : V} (p : G.Walk x x) : Fin 16 → V :=
  fun i => p.getVert i.val

theorem cycleSixteenVertices_isCycleSixteen {x : V} {p : G.Walk x x}
    (hp : p.IsCycle) (hl : p.length = 16) : IsCycleSixteen G (cycleSixteenVertices p) := by
  constructor
  · intro i j he
    apply Fin.ext
    exact hp.getVert_injOn'
      (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) he
  · intro i
    have h16 : p.getVert 16 = x := by simpa only [hl] using p.getVert_length
    fin_cases i
    · exact p.adj_getVert_succ (i := 0) (by omega)
    · exact p.adj_getVert_succ (i := 1) (by omega)
    · exact p.adj_getVert_succ (i := 2) (by omega)
    · exact p.adj_getVert_succ (i := 3) (by omega)
    · exact p.adj_getVert_succ (i := 4) (by omega)
    · exact p.adj_getVert_succ (i := 5) (by omega)
    · exact p.adj_getVert_succ (i := 6) (by omega)
    · exact p.adj_getVert_succ (i := 7) (by omega)
    · exact p.adj_getVert_succ (i := 8) (by omega)
    · exact p.adj_getVert_succ (i := 9) (by omega)
    · exact p.adj_getVert_succ (i := 10) (by omega)
    · exact p.adj_getVert_succ (i := 11) (by omega)
    · exact p.adj_getVert_succ (i := 12) (by omega)
    · exact p.adj_getVert_succ (i := 13) (by omega)
    · exact p.adj_getVert_succ (i := 14) (by omega)
    · change G.Adj (p.getVert 15) (p.getVert 0)
      have ha := p.adj_getVert_succ (i := 15) (by omega : 15 < p.length)
      change G.Adj (p.getVert 15) (p.getVert 16) at ha
      simpa only [h16, Walk.getVert_zero] using ha

def FiveChord (G : SimpleGraph V) (u : Fin 16 → V) (i : Fin 16) : Prop :=
  G.Adj (u i) (u (i + 5))

def SevenChord (G : SimpleGraph V) (u : Fin 16 → V) (i : Fin 16) : Prop :=
  G.Adj (u i) (u (i + 7))

theorem adj_of_rotated_edge_eq (u : Fin 16 → V) (i a b x y : Fin 16)
    (ha : G.Adj (u (i + a)) (u (i + b))) (he : s(x, y) = s(a, b)) :
    G.Adj (u (i + x)) (u (i + y)) := by
  have hp : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using he
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ha
  · exact ha.symm

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.NoFourteenCycle
#print axioms TaskH.Seven.BP.IsCycleSixteen
#print axioms TaskH.Seven.BP.cycleFourteenWalk
#print axioms TaskH.Seven.BP.cycleFourteenWalk_isCycle
#print axioms TaskH.Seven.BP.cycleFourteenWalk_length
#print axioms TaskH.Seven.BP.exists_fourteen_cycle_of_injective_adj
#print axioms TaskH.Seven.BP.cycleSixteenVertices
#print axioms TaskH.Seven.BP.cycleSixteenVertices_isCycleSixteen
#print axioms TaskH.Seven.BP.FiveChord
#print axioms TaskH.Seven.BP.SevenChord
#print axioms TaskH.Seven.BP.adj_of_rotated_edge_eq
