import Research.Backfill.Paper4.Proof.GridInterval

/-! Complete monotone-walk criterion for the frozen GridA definition.
The proof compares arbitrary walk lengths with L1 before deriving the graph distance formula.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace GridMonotone

/-- Normalize the list-level coercion inserted in the frozen coordinate-map expression. -/
theorem coordinate_map_normalization {k : ℕ} {S : Finset (Fin k → ℤ)}
    (l : List S) (i : Fin k) :
    List.map (fun x : Fin k → ℤ => x i)
      (l >>= fun x : S => pure (x : Fin k → ℤ)) =
      l.map (fun x : S => x.val i) := by
  rw [bind_pure_comp]
  change (l.map (fun x : S => x.val)).map (fun x : Fin k → ℤ => x i) =
    l.map (fun x : S => x.val i)
  simp only [List.map_map, Function.comp_def]

theorem monotone_iff_coordinates {k : ℕ} {S : Finset (Fin k → ℤ)} {u v : S}
    (p : (Challenge.gridGraph S).Walk u v) :
    Challenge.IsMonotoneWalk p ↔
      ∀ i, Challenge.MonotoneList (p.support.map (fun x : S => x.val i)) := by
  unfold Challenge.IsMonotoneWalk
  simp only [coordinate_map_normalization]

theorem pairwise_walk_endpoints {V : Type*} {G : SimpleGraph V}
    (R : ℤ → ℤ → Prop) (hR : ∀ a, R a a) (f : V → ℤ)
    {u v : V} (p : G.Walk u v) (hp : (p.support.map f).Pairwise R) : R (f u) (f v) := by
  cases p with
  | nil => exact hR _
  | @cons u w v huw p =>
    change (f u :: p.support.map f).Pairwise R at hp
    exact (List.pairwise_cons.mp hp).1 (f v)
      (List.mem_map.mpr ⟨v, p.end_mem_support, rfl⟩)

theorem monotone_tail {k : ℕ} {S : Finset (Fin k → ℤ)} {u v w : S}
    (huv : (Challenge.gridGraph S).Adj u v) (p : (Challenge.gridGraph S).Walk v w)
    (hp : Challenge.IsMonotoneWalk (.cons huv p)) : Challenge.IsMonotoneWalk p := by
  have hcoords := (monotone_iff_coordinates (.cons huv p)).mp hp
  apply (monotone_iff_coordinates p).mpr
  intro i
  rcases hcoords i with hinc | hdec
  · left
    change (u.val i :: p.support.map (fun x : S => x.val i)).Pairwise (· ≤ ·) at hinc
    exact (List.pairwise_cons.mp hinc).2
  · right
    change (u.val i :: p.support.map (fun x : S => x.val i)).Pairwise (· ≥ ·) at hdec
    exact (List.pairwise_cons.mp hdec).2

theorem next_between_endpoints {k : ℕ} {S : Finset (Fin k → ℤ)} {u v w : S}
    (huv : (Challenge.gridGraph S).Adj u v) (p : (Challenge.gridGraph S).Walk v w)
    (hp : Challenge.IsMonotoneWalk (.cons huv p)) :
    ∀ i, min (u.val i) (w.val i) ≤ v.val i ∧ v.val i ≤ max (u.val i) (w.val i) := by
  have hcoords := (monotone_iff_coordinates (.cons huv p)).mp hp
  intro i
  rcases hcoords i with hinc | hdec
  · change (u.val i :: p.support.map (fun x : S => x.val i)).Pairwise (· ≤ ·) at hinc
    have huv' : u.val i ≤ v.val i :=
      (List.pairwise_cons.mp hinc).1 (v.val i)
        (List.mem_map.mpr ⟨v, p.start_mem_support, rfl⟩)
    have hvw' : v.val i ≤ w.val i :=
      pairwise_walk_endpoints (· ≤ ·) (fun _ => le_rfl) (fun x : S => x.val i)
        p (List.pairwise_cons.mp hinc).2
    exact ⟨(min_le_left _ _).trans huv', hvw'.trans (le_max_right _ _)⟩
  · change (u.val i :: p.support.map (fun x : S => x.val i)).Pairwise (· ≥ ·) at hdec
    have huv' : v.val i ≤ u.val i :=
      (List.pairwise_cons.mp hdec).1 (v.val i)
        (List.mem_map.mpr ⟨v, p.start_mem_support, rfl⟩)
    have hvw' : w.val i ≤ v.val i :=
      pairwise_walk_endpoints (· ≥ ·) (fun _ => le_rfl) (fun x : S => x.val i)
        p (List.pairwise_cons.mp hdec).2
    exact ⟨(min_le_right _ _).trans hvw', huv'.trans (le_max_left _ _)⟩

theorem l1_le_walk_length {k : ℕ} {S : Finset (Fin k → ℤ)} {u v : S}
    (p : (Challenge.gridGraph S).Walk u v) : Challenge.l1 u.val v.val ≤ p.length := by
  induction p with
  | nil => simp [Challenge.l1]
  | @cons u v w huv p ih =>
    have htri := GridInterval.l1_triangle u.val w.val v.val
    have hedge : Challenge.l1 u.val v.val = 1 := huv
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem monotone_length_eq_l1 {k : ℕ} {S : Finset (Fin k → ℤ)} {u v : S}
    (p : (Challenge.gridGraph S).Walk u v) :
    Challenge.IsMonotoneWalk p → p.length = Challenge.l1 u.val v.val := by
  induction p with
  | nil =>
    intro _
    simp [Challenge.l1]
  | @cons u v w huv p ih =>
    intro hp
    have htail := ih (monotone_tail huv p hp)
    have hadd := (GridInterval.l1_interval_iff u.val w.val v.val).mpr
      (next_between_endpoints huv p hp)
    have hedge : Challenge.l1 u.val v.val = 1 := huv
    simp only [SimpleGraph.Walk.length_cons]
    omega

end GridMonotone

theorem check_Sec3_monotonePath : Challenge.Sec3_monotonePath := by
  intro k S hpath u v
  obtain ⟨p, hp⟩ := hpath u v
  apply le_antisymm
  · calc
      (Challenge.gridGraph S).dist u v ≤ p.length := SimpleGraph.dist_le p
      _ = Challenge.l1 u.val v.val := GridMonotone.monotone_length_eq_l1 p hp
  · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    calc
      Challenge.l1 u.val v.val ≤ q.length := GridMonotone.l1_le_walk_length q
      _ = (Challenge.gridGraph S).dist u v := hq

#print axioms check_Sec3_monotonePath
end CodexPaper4
