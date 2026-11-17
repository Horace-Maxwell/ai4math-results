import Research.TaskH.Seven.SevenTwoColorPaths
import Research.TaskH.Seven.Definitions

/-! True original-graph closure of deleted-root paths.  The supplied walk is
not replaced by a numerical path-length premise: its edges and support are
mapped to G, and both actual root edges are used. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def twoColorDeletedHom (v : V) : G.induce {x | x ≠ v} →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

def twoColorDeletedLift (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b) : G.Walk a.val b.val :=
  p.map (twoColorDeletedHom v)

theorem twoColorDeletedLift_isPath (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath) :
    (twoColorDeletedLift v p).IsPath :=
  hp.map (show Function.Injective (twoColorDeletedHom (G := G) v) from Subtype.val_injective)

theorem twoColorDeletedLift_avoids_root (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b) :
    v ∉ (twoColorDeletedLift v p).support := by
  intro hv
  have hsupport : (twoColorDeletedLift v p).support = p.support.map Subtype.val :=
    Walk.support_map (twoColorDeletedHom v) p
  rw [hsupport, List.mem_map] at hv
  obtain ⟨z, _, he⟩ := hv
  exact z.property he

def twoColorRootClosure (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) : G.Walk v v :=
  .cons ha ((twoColorDeletedLift v p).concat hb.symm)

theorem twoColorRootClosure_isCycle (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) :
    (twoColorRootClosure v p ha hb).IsCycle := by
  have havb : a.val ≠ b.val := fun he => hab (Subtype.ext he)
  rw [twoColorRootClosure, Walk.cons_isCycle_iff]
  refine ⟨(twoColorDeletedLift_isPath v p hp).concat
    (twoColorDeletedLift_avoids_root v p) hb.symm, ?_⟩
  intro he
  rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · exact twoColorDeletedLift_avoids_root v p
      ((twoColorDeletedLift v p).fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨hvb, _⟩ | ⟨_, hab'⟩
    · exact b.property hvb.symm
    · exact havb hab'

theorem twoColorRootClosure_length (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) :
    (twoColorRootClosure v p ha hb).length = p.length + 2 := by
  have hlength : (twoColorDeletedLift v p).length = p.length :=
    Walk.length_map (twoColorDeletedHom v) p
  calc
    _ = (twoColorDeletedLift v p).length + 1 + 1 := by
      rw [twoColorRootClosure, Walk.length_cons, Walk.length_concat]
    _ = p.length + 2 := congrArg (fun k : ℕ => k + 1 + 1) hlength

theorem twoColorRootClosure_contains (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {x | x ≠ v}).Walk a b)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) (n : ℕ) (hn : n ≤ p.length) :
    (p.getVert n).val ∈ (twoColorRootClosure v p ha hb).support := by
  rw [twoColorRootClosure, Walk.support_cons]
  apply List.mem_cons_of_mem
  rw [Walk.support_concat, List.mem_append]
  left
  have hsupport : (twoColorDeletedLift v p).support = p.support.map Subtype.val :=
    Walk.support_map (twoColorDeletedHom v) p
  rw [hsupport, List.mem_map]
  exact ⟨p.getVert n, Walk.mem_support_iff_exists_getVert.mpr ⟨n, rfl, hn⟩, rfl⟩

theorem twoColor_path_length_ne_five (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b : {z : V // z ≠ v}}
    (ha : G.Adj v a.val) (hb : G.Adj v b.val)
    (beta : Fin 7) (hbeta : beta ≠ c a) (hend : c b = beta)
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c a) beta)) : p.length ≠ 5 := by
  intro hl
  have hab : a ≠ b := by
    intro he
    subst b
    exact hbeta hend.symm
  let q := twoColorRootClosure v p ha hb
  have hq : q.IsCycle := twoColorRootClosure_isCycle v p hp hab ha hb
  have hql : q.length = 7 := by rw [twoColorRootClosure_length, hl]
  have hc0 : c (p.getVert 0) = c a := by simp
  have hc2 : c (p.getVert 2) = c a := by
    simpa using twoColor_color_at p c beta hf 2 (by omega)
  have he := hr v c q hq hql (p.getVert 0) (p.getVert 2)
    (twoColorRootClosure_contains v p ha hb 0 (by omega))
    (twoColorRootClosure_contains v p ha hb 2 (by omega)) (hc0.trans hc2.symm)
  have hn := hp.getVert_injOn (by change 0 ≤ p.length; omega)
    (by change 2 ≤ p.length; omega) he
  omega

end TaskH.Seven
#print axioms TaskH.Seven.twoColorDeletedHom
#print axioms TaskH.Seven.twoColorDeletedLift
#print axioms TaskH.Seven.twoColorDeletedLift_isPath
#print axioms TaskH.Seven.twoColorDeletedLift_avoids_root
#print axioms TaskH.Seven.twoColorRootClosure
#print axioms TaskH.Seven.twoColorRootClosure_isCycle
#print axioms TaskH.Seven.twoColorRootClosure_length
#print axioms TaskH.Seven.twoColorRootClosure_contains
#print axioms TaskH.Seven.twoColor_path_length_ne_five
