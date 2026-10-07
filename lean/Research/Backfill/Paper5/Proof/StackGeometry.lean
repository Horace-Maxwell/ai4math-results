import Research.Backfill.Paper5.Challenge
import Research.Backfill.Paper5.Proof.InvolutionEndpointCount

set_option autoImplicit false

namespace CodexPaper5.StackGeometry

open BackfillPaper5 Function

/-- Extend the upper diagram to the actual three rows, fixing row 2. -/
def upperMap {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (u : Challenge.SPt n) : Challenge.SPt n :=
  if u.1 = 0 then Challenge.upper (x (Sum.inl u.2))
  else if u.1 = 1 then Challenge.upper (x (Sum.inr u.2)) else u

/-- Extend the lower diagram to the actual three rows, fixing row 0. -/
def lowerMap {n : ℕ} (y : Challenge.Pt n → Challenge.Pt n)
    (u : Challenge.SPt n) : Challenge.SPt n :=
  if u.1 = 1 then Challenge.lower (y (Sum.inl u.2))
  else if u.1 = 2 then Challenge.lower (y (Sum.inr u.2)) else u

theorem upper_injective {n : ℕ} : Injective (@Challenge.upper n) := by
  intro p q h
  cases p <;> cases q <;> simp_all [Challenge.upper]

theorem lower_injective {n : ℕ} : Injective (@Challenge.lower n) := by
  intro p q h
  cases p <;> cases q <;> simp_all [Challenge.lower]

theorem outer_injective {n : ℕ} : Injective (@Challenge.outer n) := by
  intro p q h
  cases p <;> cases q <;> simp_all [Challenge.outer]

@[simp] theorem upperMap_upper {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) : upperMap x (Challenge.upper p) = Challenge.upper (x p) := by
  cases p <;> simp [upperMap, Challenge.upper]

@[simp] theorem lowerMap_lower {n : ℕ} (y : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) : lowerMap y (Challenge.lower p) = Challenge.lower (y p) := by
  cases p <;> simp [lowerMap, Challenge.lower]

theorem upperMap_involutive {n : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) : Involutive (upperMap x) := by
  rintro ⟨row, a⟩
  fin_cases row
  · change upperMap x (Challenge.upper (x (Sum.inl a))) = Challenge.upper (Sum.inl a)
    rw [upperMap_upper]
    exact congrArg Challenge.upper (hx (Sum.inl a))
  · change upperMap x (Challenge.upper (x (Sum.inr a))) = Challenge.upper (Sum.inr a)
    rw [upperMap_upper]
    exact congrArg Challenge.upper (hx (Sum.inr a))
  · rfl

theorem lowerMap_involutive {n : ℕ} {y : Challenge.Pt n → Challenge.Pt n}
    (hy : Challenge.IsPB y) : Involutive (lowerMap y) := by
  rintro ⟨row, a⟩
  fin_cases row
  · rfl
  · change lowerMap y (Challenge.lower (y (Sum.inl a))) = Challenge.lower (Sum.inl a)
    rw [lowerMap_lower]
    exact congrArg Challenge.lower (hy (Sum.inl a))
  · change lowerMap y (Challenge.lower (y (Sum.inr a))) = Challenge.lower (Sum.inr a)
    rw [lowerMap_lower]
    exact congrArg Challenge.lower (hy (Sum.inr a))

def upperPerm {n : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) : Equiv.Perm (Challenge.SPt n) where
  toFun := upperMap x
  invFun := upperMap x
  left_inv := upperMap_involutive hx
  right_inv := upperMap_involutive hx

def lowerPerm {n : ℕ} {y : Challenge.Pt n → Challenge.Pt n}
    (hy : Challenge.IsPB y) : Equiv.Perm (Challenge.SPt n) where
  toFun := lowerMap y
  invFun := lowerMap y
  left_inv := lowerMap_involutive hy
  right_inv := lowerMap_involutive hy

/-- Away from loops, the actual stack edges are exactly the two extension edges.
The extensions only add loops on their unused outer row. -/
theorem stackEdge_iff_of_ne {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {u v : Challenge.SPt n} (hne : u ≠ v) :
    Challenge.stackEdge x y u v ↔ upperMap x u = v ∨ lowerMap y u = v := by
  constructor
  · rintro (⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩)
    · exact Or.inl (upperMap_upper x p)
    · exact Or.inr (lowerMap_lower y p)
  · rintro (h | h)
    · rcases u with ⟨row, a⟩
      fin_cases row
      · exact Or.inl ⟨Sum.inl a, rfl, h.symm⟩
      · exact Or.inl ⟨Sum.inr a, rfl, h.symm⟩
      · exact (hne h).elim
    · rcases u with ⟨row, a⟩
      fin_cases row
      · exact (hne h).elim
      · exact Or.inr ⟨Sum.inl a, rfl, h.symm⟩
      · exact Or.inr ⟨Sum.inr a, rfl, h.symm⟩

/-- The genuine frozen stack graph, including removal of singleton loops and merging
of coincident upper/lower edges, is the moving graph of the actual extensions. -/
theorem stackGraph_eq_movingGraph {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    Challenge.stackGraph x y =
      InvolutionEndpoints.movingGraph (upperPerm hx) (lowerPerm hy) := by
  ext u v
  change
    (u ≠ v ∧ (Challenge.stackEdge x y u v ∨ Challenge.stackEdge x y v u)) ↔
    (u ≠ v ∧ ((upperMap x u = v ∨ lowerMap y u = v) ∨
      (upperMap x v = u ∨ lowerMap y v = u)))
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, h.imp (stackEdge_iff_of_ne x y hne).mp
      (stackEdge_iff_of_ne x y hne.symm).mp⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, h.imp (stackEdge_iff_of_ne x y hne).mpr
      (stackEdge_iff_of_ne x y hne.symm).mpr⟩

/-- Every outer point is fixed by the extension that omits its row. -/
theorem outer_fixed {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) (p : Challenge.Pt n) :
    upperPerm hx (Challenge.outer p) = Challenge.outer p ∨
      lowerPerm hy (Challenge.outer p) = Challenge.outer p := by
  cases p with
  | inl a => exact Or.inr rfl
  | inr a => exact Or.inl rfl

/-- A component has at most two outer vertices: the actual unique partner property
needed by the frozen list-search definition of dmul. -/
theorem outer_partner_unique {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {p q s : Challenge.Pt n}
    (hqp : q ≠ p) (hsp : s ≠ p)
    (hpq : (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q))
    (hps : (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer s)) :
    q = s := by
  rw [stackGraph_eq_movingGraph hx hy] at hpq hps
  have h := InvolutionEndpointCount.endpoints_at_most_two
    (upperPerm hx) (lowerPerm hy) (upperMap_involutive hx) (lowerMap_involutive hy)
    (outer_fixed hx hy p) (outer_fixed hx hy q) (outer_fixed hx hy s) hpq hps
  rcases h with hpq | hps | hqs
  · exact (hqp (outer_injective hpq).symm).elim
  · exact (hsp (outer_injective hps).symm).elim
  · exact outer_injective hqs

theorem upper_not_fixed_upper_of_B {n : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.B n) (p : Challenge.Pt n) :
    upperPerm hx.1 (Challenge.upper p) ≠ Challenge.upper p := by
  intro h
  change upperMap x (Challenge.upper p) = Challenge.upper p at h
  rw [upperMap_upper] at h
  exact hx.2 p (upper_injective h)

theorem lower_not_fixed_lower_of_B {n : ℕ} {y : Challenge.Pt n → Challenge.Pt n}
    (hy : y ∈ Challenge.B n) (p : Challenge.Pt n) :
    lowerPerm hy.1 (Challenge.lower p) ≠ Challenge.lower p := by
  intro h
  change lowerMap y (Challenge.lower p) = Challenge.lower p at h
  rw [lowerMap_lower] at h
  exact hy.2 p (lower_injective h)

theorem outer_row_ne_one {n : ℕ} (p : Challenge.Pt n) : (Challenge.outer p).1 ≠ 1 := by
  cases p with
  | inl a =>
    change (0 : Fin 3) ≠ 1
    decide
  | inr a =>
    change (2 : Fin 3) ≠ 1
    decide

/-- In the Brauer case the union of the two actual fixed-point sets is exactly
the outer rows. Middle vertices are fixed by neither extension. -/
theorem fixed_iff_outer_of_B {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.B n) (hy : y ∈ Challenge.B n) (u : Challenge.SPt n) :
    (upperPerm hx.1 u = u ∨ lowerPerm hy.1 u = u) ↔
      ∃ p : Challenge.Pt n, Challenge.outer p = u := by
  rcases u with ⟨row, a⟩
  fin_cases row
  · constructor
    · intro _h
      exact ⟨Sum.inl a, rfl⟩
    · intro _h
      exact Or.inr rfl
  · constructor
    · rintro (h | h)
      · exact (upper_not_fixed_upper_of_B hx (Sum.inr a) h).elim
      · exact (lower_not_fixed_lower_of_B hy (Sum.inl a) h).elim
    · rintro ⟨p, hp⟩
      exact (outer_row_ne_one p (congrArg Prod.fst hp)).elim
  · constructor
    · intro _h
      exact ⟨Sum.inr a, rfl⟩
    · intro _h
      exact Or.inl rfl

theorem no_common_fixed_of_B {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.B n) (hy : y ∈ Challenge.B n) :
    ∀ u : Challenge.SPt n, ¬ (upperPerm hx.1 u = u ∧ lowerPerm hy.1 u = u) := by
  rintro ⟨row, a⟩ h
  fin_cases row
  · exact upper_not_fixed_upper_of_B hx (Sum.inl a) h.1
  · exact upper_not_fixed_upper_of_B hx (Sum.inr a) h.1
  · exact lower_not_fixed_lower_of_B hy (Sum.inr a) h.2

/-- Finite Brauer stacks have a second outer endpoint in every outer component.
There is no positive-n premise; n=0 is covered by the empty point type. -/
theorem exists_outer_partner_of_B {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.B n) (hy : y ∈ Challenge.B n) (p : Challenge.Pt n) :
    ∃ q : Challenge.Pt n, q ≠ p ∧
      (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q) := by
  obtain ⟨u, hup, hreach, hfixed⟩ := InvolutionEndpointCount.exists_other_endpoint
    (upperPerm hx.1) (lowerPerm hy.1)
    (upperMap_involutive hx.1) (lowerMap_involutive hy.1)
    (outer_fixed hx.1 hy.1 p) (no_common_fixed_of_B hx hy)
  obtain ⟨q, hq⟩ := (fixed_iff_outer_of_B hx hy u).mp hfixed
  refine ⟨q, ?_, ?_⟩
  · intro hqp
    exact hup (hq.symm.trans (congrArg Challenge.outer hqp))
  · rw [hq, stackGraph_eq_movingGraph hx.1 hy.1]
    exact hreach

#print axioms CodexPaper5.StackGeometry.upper_injective
#print axioms CodexPaper5.StackGeometry.lower_injective
#print axioms CodexPaper5.StackGeometry.outer_injective
#print axioms CodexPaper5.StackGeometry.upperMap_involutive
#print axioms CodexPaper5.StackGeometry.lowerMap_involutive
#print axioms CodexPaper5.StackGeometry.stackEdge_iff_of_ne
#print axioms CodexPaper5.StackGeometry.stackGraph_eq_movingGraph
#print axioms CodexPaper5.StackGeometry.outer_fixed
#print axioms CodexPaper5.StackGeometry.outer_partner_unique
#print axioms CodexPaper5.StackGeometry.fixed_iff_outer_of_B
#print axioms CodexPaper5.StackGeometry.no_common_fixed_of_B
#print axioms CodexPaper5.StackGeometry.exists_outer_partner_of_B

end CodexPaper5.StackGeometry
