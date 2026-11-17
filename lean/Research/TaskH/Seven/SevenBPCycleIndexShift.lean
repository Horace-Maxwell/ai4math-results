import Research.TaskH.Seven.SevenBPInternalCapacity

/-! Actual cyclic shifts retain the cycle and give the two-ear distance
bounds between arbitrary indexed cycle vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem cycle_append_comm {a b : V} (p : G.Walk a b) (q : G.Walk b a)
    (hp : (p.append q).IsCycle) : (q.append p).IsCycle := by
  have ht := (Walk.isTrail_append p q).mp hp.isTrail
  apply (Walk.isCycle_def (q.append p)).mpr
  refine ⟨(Walk.isTrail_append q p).mpr ⟨ht.2.1, ht.1, ht.2.2.symm⟩, ?_, ?_⟩
  · intro he
    have hz : (q.append p).length = 0 := congrArg (fun w : G.Walk b b => w.length) he
    have hl := hp.three_le_length
    simp only [Walk.length_append] at hz hl
    omega
  · have hn := hp.support_nodup
    rw [Walk.tail_support_append] at hn ⊢
    exact List.nodup_append_comm.mp hn

def indexShiftCycle {a : V} (p : G.Walk a a) (i : ℕ) : G.Walk (p.getVert i) (p.getVert i) :=
  (p.drop i).append (p.take i)

theorem indexShiftCycle_isCycle {a : V} (p : G.Walk a a) (hp : p.IsCycle) (i : ℕ) :
    (indexShiftCycle p i).IsCycle := by
  apply cycle_append_comm (p.take i) (p.drop i)
  simpa only [Walk.append_take_drop_eq] using hp

theorem indexShiftCycle_length {a : V} (p : G.Walk a a) (i : ℕ)
    (hi : i ≤ p.length) : (indexShiftCycle p i).length = p.length := by
  simp only [indexShiftCycle, Walk.length_append, Walk.drop_length, Walk.take_length,
    inf_eq_left.mpr hi]
  omega

theorem indexShiftCycle_getVert_forward {a : V} (p : G.Walk a a) (i j : ℕ)
    (hij : i ≤ j) (hj : j < p.length) :
    (indexShiftCycle p i).getVert (j - i) = p.getVert j := by
  have hlt : j - i < p.length - i := by omega
  simp only [indexShiftCycle, Walk.getVert_append, Walk.drop_length,
    ite_eq_left hlt, Walk.drop_getVert, show i + (j - i) = j by omega]

theorem indexShiftCycle_support_subset {a : V} (p : G.Walk a a) (i : ℕ) :
    ∀ x ∈ (indexShiftCycle p i).support, x ∈ p.support := by
  intro x hx
  rcases (Walk.mem_support_append_iff (p.drop i) (p.take i)).mp hx with hx | hx
  · exact (p.isSubwalk_drop i).support_subset hx
  · exact (p.isSubwalk_take i).support_subset hx

theorem shortestLongCycle_indexShift {a : V} (p : G.Walk a a)
    (hp : ShortestLongCycle p) (i : ℕ) (hi : i ≤ p.length) :
    ShortestLongCycle (indexShiftCycle p i) := by
  refine ⟨indexShiftCycle_isCycle p hp.1 i, ?_, ?_⟩
  · simpa only [indexShiftCycle_length p i hi] using hp.2.1
  · intro b q hq h14
    simpa only [indexShiftCycle_length p i hi] using hp.2.2 b q hq h14

theorem shortest_cycle_external_pair_distances (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) (hz : z ∉ p.support)
    (i j : ℕ) (hij : i ≤ j) (hj : j < p.length)
    (h4 : 4 ≤ j - i) (hfar : (j - i) + 4 ≤ p.length)
    (hiadj : G.Adj (p.getVert i) z) (hjadj : G.Adj (p.getVert j) z) :
    j - i ≤ 10 ∧ p.length - (j - i) ≤ 10 := by
  have hi : i ≤ p.length := by omega
  have hs := shortestLongCycle_indexShift p hp i hi
  have hzq : z ∉ (indexShiftCycle p i).support :=
    fun h => hz (indexShiftCycle_support_subset p i z h)
  have hh := shortest_cycle_external_ear_distances hb (indexShiftCycle p i) hs hzq
    (j - i) h4 (by simpa only [indexShiftCycle_length p i hi] using hfar)
    hiadj (by simpa only [indexShiftCycle_getVert_forward p i j hij hj] using hjadj)
  simpa only [indexShiftCycle_length p i hi] using hh

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.cycle_append_comm
#print axioms TaskH.Seven.BP.indexShiftCycle
#print axioms TaskH.Seven.BP.indexShiftCycle_isCycle
#print axioms TaskH.Seven.BP.indexShiftCycle_length
#print axioms TaskH.Seven.BP.indexShiftCycle_getVert_forward
#print axioms TaskH.Seven.BP.indexShiftCycle_support_subset
#print axioms TaskH.Seven.BP.shortestLongCycle_indexShift
#print axioms TaskH.Seven.BP.shortest_cycle_external_pair_distances
