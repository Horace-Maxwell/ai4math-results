import Research.Backfill.Paper5.Proof.StackGeometry

set_option autoImplicit false

namespace CodexPaper5.DiagramProduct

open BackfillPaper5

theorem mem_ptList {n : ℕ} (p : Challenge.Pt n) : p ∈ Challenge.ptList n := by
  cases p <;> simp [Challenge.ptList]

/-- If the actual search has no eligible partner, its specified default is the point itself. -/
theorem dmul_eq_self_of_no_partner {n : ℕ}
    (x y : Challenge.Pt n → Challenge.Pt n) (p : Challenge.Pt n)
    (h : ∀ q, q ≠ p →
      ¬ (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q)) :
    Challenge.dmul x y p = p := by
  have hn : (Challenge.ptList n).find?
      (fun q => decide (q ≠ p ∧
        (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q))) = none := by
    apply List.find?_eq_none.mpr
    intro q _hq hq
    have he : q ≠ p ∧
        (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q) :=
      of_decide_eq_true hq
    exact h q he.1 he.2
  change ((Challenge.ptList n).find? _).getD p = p
  rw [hn]
  rfl

/-- A real reachable nontrivial partner, when unique, is exactly the frozen list search result. -/
theorem dmul_eq_of_partner {n : ℕ}
    (x y : Challenge.Pt n → Challenge.Pt n) (p q : Challenge.Pt n)
    (hne : q ≠ p)
    (hr : (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q))
    (hu : ∀ z, z ≠ p →
      (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer z) → z = q) :
    Challenge.dmul x y p = q := by
  let pred : Challenge.Pt n → Bool := fun z => decide (z ≠ p ∧
    (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer z))
  have hq : pred q := decide_eq_true ⟨hne, hr⟩
  have hsome : (Challenge.ptList n).find? pred ≠ none := by
    intro hn
    exact (List.find?_eq_none.mp hn q (mem_ptList q)) hq
  cases hf : (Challenge.ptList n).find? pred with
  | none => exact (hsome hf).elim
  | some z =>
    have hz : z ≠ p ∧
        (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer z) :=
      of_decide_eq_true (List.find?_some (p := pred) hf)
    have hzq : z = q := hu z hz.1 hz.2
    change ((Challenge.ptList n).find? pred).getD p = q
    rw [hf]
    exact hzq

/-- The frozen product either takes its default or an actual nontrivial reachable outer point. -/
theorem dmul_spec {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) :
    Challenge.dmul x y p = p ∨
      (Challenge.dmul x y p ≠ p ∧ (Challenge.stackGraph x y).Reachable
        (Challenge.outer p) (Challenge.outer (Challenge.dmul x y p))) := by
  let pred : Challenge.Pt n → Bool := fun q => decide (q ≠ p ∧
    (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q))
  change ((Challenge.ptList n).find? pred).getD p = p ∨
    (((Challenge.ptList n).find? pred).getD p ≠ p ∧
      (Challenge.stackGraph x y).Reachable (Challenge.outer p)
        (Challenge.outer (((Challenge.ptList n).find? pred).getD p)))
  cases hf : (Challenge.ptList n).find? pred with
  | none => exact Or.inl rfl
  | some q =>
    exact Or.inr (of_decide_eq_true (List.find?_some (p := pred) hf))

/-- Actual outer-partner uniqueness and undirected reachability make the product involutive. -/
theorem dmul_isPB {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    Challenge.IsPB (Challenge.dmul x y) := by
  intro p
  rcases dmul_spec x y p with hp | hp
  · exact (congrArg (Challenge.dmul x y) hp).trans hp
  · apply dmul_eq_of_partner x y (Challenge.dmul x y p) p (Ne.symm hp.1) hp.2.symm
    intro z hz hpath
    exact StackGeometry.outer_partner_unique hx hy hz (Ne.symm hp.1) hpath hp.2.symm

/-- In the fixed-point-free case a different outer endpoint exists, so the default is never used. -/
theorem dmul_mem_B {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.B n) (hy : y ∈ Challenge.B n) :
    Challenge.dmul x y ∈ Challenge.B n := by
  refine ⟨dmul_isPB hx.1 hy.1, ?_⟩
  intro p
  obtain ⟨q, hne, hr⟩ := StackGeometry.exists_outer_partner_of_B hx hy p
  have heq : Challenge.dmul x y p = q := by
    apply dmul_eq_of_partner x y p q hne hr
    intro z hz hpath
    exact StackGeometry.outer_partner_unique hx.1 hy.1 hz hne hpath hr
  exact fun hp => hne (heq.symm.trans hp)

#print axioms CodexPaper5.DiagramProduct.mem_ptList
#print axioms CodexPaper5.DiagramProduct.dmul_eq_self_of_no_partner
#print axioms CodexPaper5.DiagramProduct.dmul_eq_of_partner
#print axioms CodexPaper5.DiagramProduct.dmul_spec
#print axioms CodexPaper5.DiagramProduct.dmul_isPB
#print axioms CodexPaper5.DiagramProduct.dmul_mem_B

end CodexPaper5.DiagramProduct
