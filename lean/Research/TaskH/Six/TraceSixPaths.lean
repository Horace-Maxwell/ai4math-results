import Research.TaskH.Six.CycleSix

/-!
Actual simple three-edge paths.  A pair `(a,b)` denotes the path `u-a-b-v`;
the injectivity condition includes both endpoints.  The finite sets in this
module contain vertices of the original graph, not numerical substitutes.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def traceThreeWord (u a b v : V) : Fin 4 → V := ![u, a, b, v]

def IsTraceThreePath (G : SimpleGraph V) (u v : V) (p : V × V) : Prop :=
  Function.Injective (traceThreeWord u p.1 p.2 v) ∧
    G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v

theorem traceThreeWord_injective_iff (u a b v : V) :
    Function.Injective (traceThreeWord u a b v) ↔
      u ≠ a ∧ u ≠ b ∧ u ≠ v ∧ a ≠ b ∧ a ≠ v ∧ b ≠ v := by
  constructor
  · intro h
    exact ⟨h.ne (by decide : (0 : Fin 4) ≠ 1),
      h.ne (by decide : (0 : Fin 4) ≠ 2),
      h.ne (by decide : (0 : Fin 4) ≠ 3),
      h.ne (by decide : (1 : Fin 4) ≠ 2),
      h.ne (by decide : (1 : Fin 4) ≠ 3),
      h.ne (by decide : (2 : Fin 4) ≠ 3)⟩
  · rintro ⟨hua, hub, huv, hab, hav, hbv⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [traceThreeWord]

def traceThreeWalk (G : SimpleGraph V) (u a b v : V)
    (hua : G.Adj u a) (hab : G.Adj a b) (hbv : G.Adj b v) : G.Walk u v :=
  .cons hua (.cons hab (.cons hbv .nil))

theorem traceThreeWalk_isPath (u v : V) (p : V × V)
    (hp : IsTraceThreePath G u v p) :
    (traceThreeWalk G u p.1 p.2 v hp.2.1 hp.2.2.1 hp.2.2.2).IsPath := by
  rcases (traceThreeWord_injective_iff u p.1 p.2 v).mp hp.1 with
    ⟨hua, hub, huv, hab, hav, hbv⟩
  apply Walk.IsPath.mk'
  simp [traceThreeWalk, Walk.support_cons, hua, hub, huv, hab, hav, hbv]

theorem traceThreeWalk_length (u a b v : V)
    (hua : G.Adj u a) (hab : G.Adj a b) (hbv : G.Adj b v) :
    (traceThreeWalk G u a b v hua hab hbv).length = 3 := rfl

theorem traceThreeWalk_getVert_one (u a b v : V)
    (hua : G.Adj u a) (hab : G.Adj a b) (hbv : G.Adj b v) :
    (traceThreeWalk G u a b v hua hab hbv).getVert 1 = a := rfl

theorem traceThreeWalk_getVert_two (u a b v : V)
    (hua : G.Adj u a) (hab : G.Adj a b) (hbv : G.Adj b v) :
    (traceThreeWalk G u a b v hua hab hbv).getVert 2 = b := rfl

theorem traceThreePath_of_walk {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hl : p.length = 3) :
    IsTraceThreePath G u v (p.getVert 1, p.getVert 2) := by
  have hend : p.getVert 3 = v := by simpa only [hl] using p.getVert_length
  have hw : traceThreeWord u (p.getVert 1) (p.getVert 2) v =
      fun i : Fin 4 => p.getVert i.val := by
    funext i
    fin_cases i <;> simp [traceThreeWord, hend]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hw]
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) hij
  · simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · simpa only [hend] using p.adj_getVert_succ (i := 2) (by omega)

theorem traceThreePath_iff_exists_walk (u v : V) (q : V × V) :
    IsTraceThreePath G u v q ↔
      ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3 ∧
        p.getVert 1 = q.1 ∧ p.getVert 2 = q.2 := by
  constructor
  · intro hq
    exact ⟨traceThreeWalk G u q.1 q.2 v hq.2.1 hq.2.2.1 hq.2.2.2,
      traceThreeWalk_isPath u v q hq, rfl, rfl, rfl⟩
  · rintro ⟨p, hp, hl, h1, h2⟩
    simpa only [h1, h2, Prod.eta] using traceThreePath_of_walk p hp hl

noncomputable def traceThreePaths [Fintype V] (G : SimpleGraph V)
    (u v : V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (IsTraceThreePath G u v)

theorem mem_traceThreePaths_iff [Fintype V] (u v : V) (q : V × V) :
    q ∈ traceThreePaths G u v ↔ IsTraceThreePath G u v q := by
  classical
  simp [traceThreePaths]

theorem traceThreePaths_self [Fintype V] (u : V) :
    traceThreePaths G u u = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (traceThreeWord_injective_iff u q.1 q.2 u).mp
    ((mem_traceThreePaths_iff u u q).mp hq).1
  exact h.2.2.1 rfl

end TaskH.Six

#print axioms TaskH.Six.traceThreeWord_injective_iff
#print axioms TaskH.Six.traceThreeWalk_isPath
#print axioms TaskH.Six.traceThreeWalk_length
#print axioms TaskH.Six.traceThreeWalk_getVert_one
#print axioms TaskH.Six.traceThreeWalk_getVert_two
#print axioms TaskH.Six.traceThreePath_of_walk
#print axioms TaskH.Six.traceThreePath_iff_exists_walk
#print axioms TaskH.Six.mem_traceThreePaths_iff
#print axioms TaskH.Six.traceThreePaths_self
