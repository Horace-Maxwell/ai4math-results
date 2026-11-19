import Research.TaskJ.Grid.GridPadding
import Research.TaskJ.Grid.GridNormalize
import Research.TaskJ.Grid.GridFormula

namespace Grid.Canonical

open Challenge Pad

/-- In a mixed rectangle a wide even side uses the four-layer seed. -/
def evenBase (ds : List ℕ) : ℕ :=
  if ds.length = 2 ∧ evenCount ds = 1 ∧ (∀ d ∈ ds, d%2 = 0 → 4 ≤ d) then 4 else 2

private def base (b d : ℕ) : ℕ := if d%2 = 0 then b else 3
private def pad (b d : ℕ) : ℕ × ℕ := (base b d, (d-base b d)/2)

theorem evenBase_cases (ds : List ℕ) : evenBase ds = 2 ∨ evenBase ds = 4 := by
  unfold evenBase
  split <;> simp

private theorem base_ok {ds : List ℕ} (wide : ∀ d ∈ ds, 1 < d) {d : ℕ} (hd : d ∈ ds) :
    2 ≤ base (evenBase ds) d ∧ base (evenBase ds) d + 2*((d-base (evenBase ds) d)/2) = d := by
  have h := wide d hd
  unfold base evenBase
  split_ifs with he hb
  all_goals first | (have := hb.2.2 d hd he; omega) | omega

private theorem seed_perm (b : ℕ) (ds : List ℕ) :
    (ds.map (base b)).Perm (List.replicate (evenCount ds) b ++
      List.replicate (ds.length - evenCount ds) 3) := by
  induction ds with
  | nil => simp [evenCount]
  | cons d ds ih =>
    have hle : evenCount ds ≤ ds.length := List.length_filter_le ..
    rw [count_cons]
    by_cases he : d%2 = 0
    · simp only [he, ite_true, List.length_cons, List.map_cons, base, List.replicate_succ,
        List.cons_append, Nat.add_sub_add_right]
      exact ih.cons b
    · have hq : ds.length + 1 - evenCount ds = (ds.length - evenCount ds) + 1 := by omega
      simp only [he, reduceIte, List.length_cons, List.map_cons, base, hq, List.replicate_succ]
      exact (ih.cons 3).trans (List.perm_middle ..).symm

private theorem lift_order {α β : Type*} [DecidableEq α] (f : α → β) (l : List α) (t : List β)
    (h : (l.map f).Perm t) : ∃ s, l.Perm s ∧ s.map f = t := by
  induction t generalizing l with
  | nil =>
    have : l = [] := by have eq := h.length_eq; simpa using eq
    subst l; exact ⟨[],.nil,rfl⟩
  | cons b bs ih =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (h.mem_iff.mpr List.mem_cons_self)
    have p := List.perm_cons_erase ha
    have tail : ((l.erase a).map f).Perm bs := ((p.map f).symm.trans h).cons_inv
    obtain ⟨s,hs,ht⟩ := ih _ tail
    exact ⟨a::s,p.trans (hs.cons a),by simp [ht]⟩

/-- Any desired ordering of the canonical two/three/four-layer seed can be used. -/
theorem prepare (ds core : List ℕ) (wide : ∀ d ∈ ds, 1 < d)
    (h : (List.replicate (evenCount ds) (evenBase ds) ++
      List.replicate (ds.length-evenCount ds) 3).Perm core) :
    ∃ pads : Padding, Wide pads ∧ inner pads = core ∧ (outer pads).Perm ds := by
  let ls := ds.map (pad (evenBase ds))
  have hins : (ls.map Prod.fst).Perm core := by
    simpa [ls, List.map_map, Function.comp_def, pad] using (seed_perm (evenBase ds) ds).trans h
  obtain ⟨pads, hp, hc⟩ := lift_order Prod.fst ls core hins
  refine ⟨pads, ?_,hc,?_⟩
  · intro t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (hp.mem_iff.mpr ht)
    exact (base_ok wide hd).1
  · have hout : outer ls = ds := by
      dsimp [ls,outer]
      rw [List.map_map]
      exact (List.map_congr_left (g := id) (fun d hd => (base_ok wide hd).2)).trans (List.map_id ds)
    rw [← hout]
    exact (hp.map (fun t : ℕ × ℕ => t.1 + 2*t.2)).symm

/-- Move one even seed axis past the initial odd axes to the mixed seed. -/
theorem mixed_perm (k q : ℕ) :
    (List.replicate (k+1) 2 ++ List.replicate (q+2) 3).Perm
      (List.replicate k 2 ++ (List.replicate q 3 ++ [2,3,3])) := by
  have hk : List.replicate (k+1) 2 = List.replicate k 2 ++ [2] := List.replicate_succ'
  have hq : List.replicate (q+2) 3 = List.replicate (q+1) 3 ++ [3] := List.replicate_succ'
  have ht : List.replicate (q+1) 3 = List.replicate q 3 ++ [3] := List.replicate_succ'
  rw [hk,hq,ht]
  simp only [List.append_assoc, List.singleton_append]
  exact (List.perm_middle ..).symm.append_left _

end Grid.Canonical
