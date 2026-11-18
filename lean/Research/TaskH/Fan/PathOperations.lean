import Research.TaskH.Fan.Challenge

/-!
Actual simple-path operations for the frozen rooted two-path statement.
No global TwoPathClaim or unconditional HasTwoPaths existence is assumed or asserted.
Prescribed lengths are retained by support-disjoint append, never by toPath.
-/
set_option autoImplicit false

universe u v

namespace TaskH.Fan

open SimpleGraph

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W} {x y z : V}

/-- Exact support intersection implies disjointness from the appended tail. -/
theorem tailDisjoint_of_support_intersection
    (p : G.Walk x y) (r : G.Walk y z) (hr : r.IsPath)
    (hi : ∀ a : V, a ∈ p.support → a ∈ r.support → a = y) :
    p.support.Disjoint r.support.tail := by
  have hn : (y :: r.support.tail).Nodup := by
    rw [Walk.cons_tail_support r]
    exact hr.support_nodup
  have hy : y ∉ r.support.tail := (List.nodup_cons.mp hn).1
  rw [List.disjoint_left]
  intro a hap har
  have har' : a ∈ r.support := by
    rw [← Walk.cons_tail_support r]
    exact List.mem_cons_of_mem y har
  have hay : a = y := hi a hap har'
  subst a
  exact hy har

/-- A genuine simple concatenation under actual tail-support disjointness. -/
theorem isPath_append_of_tailDisjoint
    (p : G.Walk x y) (r : G.Walk y z)
    (hp : p.IsPath) (hr : r.IsPath)
    (hd : p.support.Disjoint r.support.tail) :
    (p.append r).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append]
  exact hp.support_nodup.append hr.support_nodup.tail hd

/-- The same exact-length concatenation with a graph-support intersection premise. -/
theorem isPath_append_of_support_intersection
    (p : G.Walk x y) (r : G.Walk y z)
    (hp : p.IsPath) (hr : r.IsPath)
    (hi : ∀ a : V, a ∈ p.support → a ∈ r.support → a = y) :
    (p.append r).IsPath := by
  exact isPath_append_of_tailDisjoint p r hp hr
    (tailDisjoint_of_support_intersection p r hr hi)

/-- Reversing both actual walks retains the sorted length-gap witness. -/
theorem twoPathWitness_reverse (p q : G.Walk x y)
    (h : TwoPathWitness p q) : TwoPathWitness p.reverse q.reverse := by
  rcases h with ⟨hp, hq, hp2, hq2, hgap⟩
  refine ⟨hp.reverse, hq.reverse, ?_, ?_, ?_⟩
  · simpa only [Walk.length_reverse] using hp2
  · simpa only [Walk.length_reverse] using hq2
  · simpa only [Walk.length_reverse] using hgap

/-- Appending one actual fixed tail preserves each IsPath and the exact length gap. -/
theorem twoPathWitness_append (p q : G.Walk x y) (r : G.Walk y z)
    (h : TwoPathWitness p q) (hr : r.IsPath)
    (hpr : p.support.Disjoint r.support.tail)
    (hqr : q.support.Disjoint r.support.tail) :
    TwoPathWitness (p.append r) (q.append r) := by
  rcases h with ⟨hp, hq, hp2, hq2, hgap⟩
  refine ⟨isPath_append_of_tailDisjoint p r hp hr hpr,
    isPath_append_of_tailDisjoint q r hq hr hqr, ?_, ?_, ?_⟩
  · simp only [Walk.length_append]
    omega
  · simp only [Walk.length_append]
    omega
  · simp only [Walk.length_append]
    rcases hgap with hgap | hgap
    · left
      omega
    · right
      omega

/-- Fixed-tail witness transport from the exact common-endpoint intersection. -/
theorem twoPathWitness_append_of_support_intersection
    (p q : G.Walk x y) (r : G.Walk y z)
    (h : TwoPathWitness p q) (hr : r.IsPath)
    (hpr : ∀ a : V, a ∈ p.support → a ∈ r.support → a = y)
    (hqr : ∀ a : V, a ∈ q.support → a ∈ r.support → a = y) :
    TwoPathWitness (p.append r) (q.append r) := by
  exact twoPathWitness_append p q r h hr
    (tailDisjoint_of_support_intersection p r hr hpr)
    (tailDisjoint_of_support_intersection q r hr hqr)

/-- Actual injective graph maps preserve the full two-path witness, including lengths. -/
theorem twoPathWitness_map (f : G →g H) (hf : Function.Injective f)
    (p q : G.Walk x y) (h : TwoPathWitness p q) :
    TwoPathWitness (p.map f) (q.map f) := by
  rcases h with ⟨hp, hq, hp2, hq2, hgap⟩
  refine ⟨(Walk.isPath_map_iff_of_injective hf).mpr hp,
    (Walk.isPath_map_iff_of_injective hf).mpr hq, ?_, ?_, ?_⟩
  · simpa only [Walk.length_map] using hp2
  · simpa only [Walk.length_map] using hq2
  · simpa only [Walk.length_map] using hgap

/-- Existing witnesses at ordered roots can be reversed without any theorem oracle. -/
theorem hasTwoPaths_reverse (h : HasTwoPaths G x y) : HasTwoPaths G y x := by
  rcases h with ⟨p, q, hpq⟩
  exact ⟨p.reverse, q.reverse, twoPathWitness_reverse p q hpq⟩

#print axioms tailDisjoint_of_support_intersection
#print axioms isPath_append_of_tailDisjoint
#print axioms isPath_append_of_support_intersection
#print axioms twoPathWitness_reverse
#print axioms twoPathWitness_append
#print axioms twoPathWitness_append_of_support_intersection
#print axioms twoPathWitness_map
#print axioms hasTwoPaths_reverse

end TaskH.Fan
