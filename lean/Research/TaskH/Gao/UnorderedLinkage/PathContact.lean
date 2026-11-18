import Research.TaskH.Fan.PathOperations

/-! Actual connector surgeries for the ordinary two-fan proof.
Only unrestricted connectors are truncated; no admissible path family is changed. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V} {x y z : V}

def MeetsOnly {a b c d : V} (p : G.Walk a b) (q : G.Walk c d) (t : V) : Prop :=
  ∀ w : V, w ∈ p.support → w ∈ q.support → w = t

def HitsOnly {a b : V} (p : G.Walk a b) (S : Set V) (t : V) : Prop :=
  ∀ w : V, w ∈ p.support → w ∈ S → w = t

/-- A true simple connector to a set, using an actual first contact.
Minimum length is taken only among paths inside the already given connector support. -/
theorem first_contact (r : G.Walk x y) (hr : r.IsPath) (S : Set V) (hy : y ∈ S) :
    ∃ (t : V) (q : G.Walk x t), t ∈ S ∧ q.IsPath ∧
      q.support ⊆ r.support ∧ HitsOnly q S t := by
  classical
  let P : ℕ → Prop := fun n => ∃ (t : V) (q : G.Walk x t),
    t ∈ S ∧ q.IsPath ∧ q.length = n ∧ q.support ⊆ r.support
  have hex : ∃ n, P n := ⟨r.length, y, r, hy, hr, rfl, fun _ h => h⟩
  obtain ⟨t, q, ht, hq, hlen, hsub⟩ := Nat.find_spec hex
  refine ⟨t, q, ht, hq, hsub, ?_⟩
  intro w hw hwS
  by_contra hwt
  have hshort := q.length_takeUntil_lt_length hw hwt
  have hnew : P (q.takeUntil w hw).length := by
    refine ⟨w, q.takeUntil w hw, hwS, hq.takeUntil hw, rfl, ?_⟩
    intro z hz
    exact hsub (q.support_takeUntil_subset_support hw hz)
  have hmin := Nat.find_min' hex hnew
  omega

/-- Reverse a true first-contact connector to get a tail with only one old-set point. -/
theorem last_contact (r : G.Walk x y) (hr : r.IsPath) (S : Set V) (hx : x ∈ S) :
    ∃ (t : V) (q : G.Walk t y), t ∈ S ∧ q.IsPath ∧
      q.support ⊆ r.support ∧ HitsOnly q S t := by
  classical
  obtain ⟨t, p, ht, hp, hsub, hhit⟩ := first_contact r.reverse hr.reverse S hx
  refine ⟨t, p.reverse, ht, hp.reverse, ?_, ?_⟩
  · intro w hw
    have hwp : w ∈ p.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hw
    have hwr := hsub hwp
    simpa only [Walk.support_reverse, List.mem_reverse] using hwr
  · intro w hw hwS
    exact hhit w (by simpa only [Walk.support_reverse, List.mem_reverse] using hw) hwS

/-- The complete supports of a literal split of a simple path meet only at the split point. -/
theorem split_meets_only [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (hz : z ∈ p.support) : MeetsOnly (p.takeUntil z hz) (p.dropUntil z hz) z := by
  intro w hwL hwR
  by_contra hwz
  have happ : ((p.takeUntil z hz).append (p.dropUntil z hz)).IsPath := by
    rw [Walk.take_spec]
    exact hp
  exact (happ.ne_of_mem_support_of_append hwz hwL hwR) rfl

/-- The old first endpoint does not survive in a simple tail starting elsewhere. -/
theorem start_not_in_tail [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (hz : z ∈ p.support) (hzx : z ≠ x) : x ∉ (p.dropUntil z hz).support := by
  intro hx
  have he := split_meets_only p hp hz x (p.takeUntil z hz).start_mem_support hx
  exact hzx he.symm

/-- The actual induced deletion graph gives an actual original path avoiding the deleted point. -/
theorem deleted_connected_path (hconn : (G.induce {w | w ≠ z}).Connected)
    (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : G.Walk x y, p.IsPath ∧ ∀ w ∈ p.support, w ≠ z := by
  classical
  obtain ⟨r, hr⟩ := hconn.exists_isPath ⟨x, hx⟩ ⟨y, hy⟩
  let f : (G.induce {w | w ≠ z}) →g G :=
    (SimpleGraph.Embedding.induce {w | w ≠ z}).toHom
  refine ⟨r.map f, (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hr, ?_⟩
  intro w hw
  have hm : (r.map f).support = r.support.map f := Walk.support_map f r
  have hw' : w ∈ r.support.map f :=
    Eq.mp (congrArg (fun L : List V => w ∈ L) hm) hw
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hw'
  change a.val = w at ha
  exact fun he => a.property (ha.trans he)
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.MeetsOnly
#print axioms TaskH.Gao.UnorderedLinkage.HitsOnly
#print axioms TaskH.Gao.UnorderedLinkage.first_contact
#print axioms TaskH.Gao.UnorderedLinkage.last_contact
#print axioms TaskH.Gao.UnorderedLinkage.split_meets_only
#print axioms TaskH.Gao.UnorderedLinkage.start_not_in_tail
#print axioms TaskH.Gao.UnorderedLinkage.deleted_connected_path
