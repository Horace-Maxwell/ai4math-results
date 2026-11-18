import Research.TaskH.Gao.CarrierDeletedConnectivity

/-! The actual support of a genuine cycle satisfies the complete original
ordinary TwoConnected predicate, including order and every vertex deletion. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem actual_walk_support_connected (G : SimpleGraph V) (a b : V)
    (p : G.Walk a b) : (G.induce {v | v ∈ p.support}).Connected := by
  classical
  let S : Set V := {v | v ∈ p.support}
  let ar : S := ⟨a, p.start_mem_support⟩
  refine { preconnected := ?_, nonempty := ⟨ar⟩ }
  intro v w
  let q := p.takeUntil v.1 v.2
  let r := p.takeUntil w.1 w.2
  have hq : ∀ t ∈ q.support, t ∈ S := p.support_takeUntil_subset_support v.2
  have hr : ∀ t ∈ r.support, t ∈ S := p.support_takeUntil_subset_support w.2
  exact ⟨(q.induce S hq).reverse.append (r.induce S hr)⟩

theorem actual_cycle_support_delete_connected (G : SimpleGraph V) (a : V)
    (c : G.Walk a a) (hc : c.IsCycle) (z : V) (hz : z ∈ c.support) :
    (G.induce ({v | v ∈ c.support} \ {z})).Connected := by
  classical
  let r := c.rotate z hz
  have hr : r.IsCycle := hc.rotate hz
  let D := r.dropLast
  let q := D.tail
  have hD : D.IsPath := hr.isPath_dropLast
  have hDpos : 0 < D.length := by
    change 0 < r.dropLast.length
    rw [Walk.length_dropLast]
    have hh := hr.three_le_length
    omega
  have hDnot : ¬D.Nil := (Walk.not_nil_iff_lt_length).mpr hDpos
  have hDcons : z :: q.support = D.support := Walk.cons_support_tail hDnot
  have hrEnd : D.support ++ [z] = r.support := Walk.support_dropLast_concat hr.not_nil
  have havoid : z ∉ q.support := by
    have hn := hD.support_nodup
    rw [← hDcons] at hn
    exact hn.notMem
  have hrcover : ∀ v, v ∈ r.support ↔ v = z ∨ v ∈ q.support := by
    intro v
    rw [← hrEnd, ← hDcons]
    simp only [List.mem_append, List.mem_cons]
    tauto
  have hcover : ∀ v, v ∈ c.support ↔ v = z ∨ v ∈ q.support := by
    intro v
    exact (Walk.mem_support_rotate_iff c z hz).symm.trans (hrcover v)
  have hset : {v | v ∈ q.support} = ({v | v ∈ c.support} \ {z} : Set V) := by
    ext v
    constructor
    · intro hv
      exact ⟨(hcover v).mpr (Or.inr hv), fun he => havoid
        (Eq.mp (congrArg (fun v : V => v ∈ q.support) he) hv)⟩
    · rintro ⟨hvC, hvz⟩
      exact ((hcover v).mp hvC).resolve_left hvz
  have hconn := actual_walk_support_connected G _ _ q
  rw [hset] at hconn
  exact hconn

theorem actual_cycle_support_twoConnected [Fintype V] (G : SimpleGraph V)
    (z : V) (c : G.Walk z z) (hc : c.IsCycle) :
    ∃ iS : Fintype {v | v ∈ c.support},
      @TwoConnected {v | v ∈ c.support} iS (G.induce {v | v ∈ c.support}) := by
  classical
  let S : Set V := {v | v ∈ c.support}
  let : Fintype S := Fintype.ofFinite _
  have hl := hc.three_le_length
  let a : S := ⟨c.getVert 0, c.getVert_mem_support 0⟩
  let b : S := ⟨c.getVert 1, c.getVert_mem_support 1⟩
  let d : S := ⟨c.getVert 2, c.getVert_mem_support 2⟩
  have hab : a ≠ b := by
    intro he
    have hi := hc.getVert_injOn' (by change 0 ≤ c.length - 1; omega)
      (by change 1 ≤ c.length - 1; omega) (congrArg Subtype.val he)
    omega
  have had : a ≠ d := by
    intro he
    have hi := hc.getVert_injOn' (by change 0 ≤ c.length - 1; omega)
      (by change 2 ≤ c.length - 1; omega) (congrArg Subtype.val he)
    omega
  have hbd : b ≠ d := by
    intro he
    have hi := hc.getVert_injOn' (by change 1 ≤ c.length - 1; omega)
      (by change 2 ≤ c.length - 1; omega) (congrArg Subtype.val he)
    omega
  have hcard : 3 ≤ Fintype.card S := by
    have hh : 2 < Fintype.card S := Fintype.two_lt_card_iff.mpr ⟨a, b, d, hab, had, hbd⟩
    omega
  refine ⟨inferInstance, hcard, actual_walk_support_connected G z z c, ?_⟩
  intro v
  exact (carrierDeleteGraphIso G S v).connected_iff.mpr
    (actual_cycle_support_delete_connected G z c hc v.1 v.2)

#print axioms actual_walk_support_connected
#print axioms actual_cycle_support_delete_connected
#print axioms actual_cycle_support_twoConnected
end TaskH.Gao
