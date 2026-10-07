import Research.Backfill.Paper5.Proof.DiagramProduct

set_option autoImplicit false

namespace CodexPaper5.DiagramUnits

open BackfillPaper5 Function

/-- Collapse the identity's upper two rows to the top row of its right factor. -/
def foldLeft {n : ℕ} (v : Challenge.SPt n) : Challenge.Pt n :=
  if v.1 = 2 then Sum.inr v.2 else Sum.inl v.2

/-- Collapse the identity's lower two rows to the bottom row of its left factor. -/
def foldRight {n : ℕ} (v : Challenge.SPt n) : Challenge.Pt n :=
  if v.1 = 0 then Sum.inl v.2 else Sum.inr v.2

@[simp] theorem foldLeft_outer {n : ℕ} (p : Challenge.Pt n) :
    foldLeft (Challenge.outer p) = p := by
  cases p <;> simp [foldLeft, Challenge.outer]

@[simp] theorem foldLeft_lower {n : ℕ} (p : Challenge.Pt n) :
    foldLeft (Challenge.lower p) = p := by
  cases p <;> simp [foldLeft, Challenge.lower]

@[simp] theorem foldRight_outer {n : ℕ} (p : Challenge.Pt n) :
    foldRight (Challenge.outer p) = p := by
  cases p <;> simp [foldRight, Challenge.outer]

@[simp] theorem foldRight_upper {n : ℕ} (p : Challenge.Pt n) :
    foldRight (Challenge.upper p) = p := by
  cases p <;> simp [foldRight, Challenge.upper]

/-- The relation whose classes are exactly the singleton or two-point blocks of an involution. -/
theorem block_reverse {V : Type*} {x : V → V} (hx : Involutive x) {a b : V}
    (h : b = a ∨ b = x a) : a = b ∨ a = x b := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr ((congrArg x h).trans (hx a)).symm

/-- A graph path stays inside an actual involution block when each edge does. -/
theorem projection_of_reachable {V W : Type*} (G : SimpleGraph V) (f : V → W)
    (x : W → W) (hx : Involutive x)
    (hstep : ∀ {u v : V}, G.Adj u v → f v = f u ∨ f v = x (f u))
    {u v : V} (h : G.Reachable u v) : f v = f u ∨ f v = x (f u) := by
  have hr := (G.reachable_iff_reflTransGen u v).mp h
  clear h
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ huv ih =>
    rcases hstep huv with heq | hmove
    · simpa only [heq] using ih
    · rcases ih with heq | hmove'
      · exact Or.inr (hmove.trans (congrArg x heq))
      · exact Or.inl (hmove.trans ((congrArg x hmove').trans (hx _)))

/-- A raw block edge is reachable even when it is a singleton loop removed by `fromRel`. -/
theorem reachable_of_stackEdge {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {u v : Challenge.SPt n} (h : Challenge.stackEdge x y u v) :
    (Challenge.stackGraph x y).Reachable u v := by
  by_cases heq : u = v
  · subst v
    exact SimpleGraph.Reachable.rfl
  · have hadj : (Challenge.stackGraph x y).Adj u v := by
      change u ≠ v ∧ (Challenge.stackEdge x y u v ∨ Challenge.stackEdge x y v u)
      exact ⟨heq, Or.inl h⟩
    exact hadj.reachable

/-- A left-unit stack edge projects to an equality or one edge of the actual right factor. -/
theorem foldLeft_stackEdge {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    {u v : Challenge.SPt n} (h : Challenge.stackEdge (Challenge.idD n) x u v) :
    foldLeft v = foldLeft u ∨ foldLeft v = x (foldLeft u) := by
  rcases h with ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩
  · left
    cases p <;> simp [foldLeft, Challenge.upper, Challenge.idD]
  · right
    simp only [foldLeft_lower]

/-- A right-unit stack edge projects to an equality or one edge of the actual left factor. -/
theorem foldRight_stackEdge {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    {u v : Challenge.SPt n} (h : Challenge.stackEdge x (Challenge.idD n) u v) :
    foldRight v = foldRight u ∨ foldRight v = x (foldRight u) := by
  rcases h with ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩
  · right
    simp only [foldRight_upper]
  · left
    cases p <;> simp [foldRight, Challenge.lower, Challenge.idD]

theorem foldLeft_adj {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) {u v : Challenge.SPt n}
    (h : (Challenge.stackGraph (Challenge.idD n) x).Adj u v) :
    foldLeft v = foldLeft u ∨ foldLeft v = x (foldLeft u) := by
  change u ≠ v ∧ (Challenge.stackEdge (Challenge.idD n) x u v ∨
    Challenge.stackEdge (Challenge.idD n) x v u) at h
  rcases h.2 with h | h
  · exact foldLeft_stackEdge x h
  · exact block_reverse hx (foldLeft_stackEdge x h)

theorem foldRight_adj {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) {u v : Challenge.SPt n}
    (h : (Challenge.stackGraph x (Challenge.idD n)).Adj u v) :
    foldRight v = foldRight u ∨ foldRight v = x (foldRight u) := by
  change u ≠ v ∧ (Challenge.stackEdge x (Challenge.idD n) u v ∨
    Challenge.stackEdge x (Challenge.idD n) v u) at h
  rcases h.2 with h | h
  · exact foldRight_stackEdge x h
  · exact block_reverse hx (foldRight_stackEdge x h)

/-- Move from an outer endpoint through the actual left identity edge when needed. -/
theorem outer_to_lower {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) :
    (Challenge.stackGraph (Challenge.idD n) x).Reachable
      (Challenge.outer p) (Challenge.lower p) := by
  cases p with
  | inl a =>
    apply reachable_of_stackEdge
    exact Or.inl ⟨Sum.inl a, rfl, rfl⟩
  | inr a => exact SimpleGraph.Reachable.rfl

/-- Move from an outer endpoint through the actual right identity edge when needed. -/
theorem outer_to_upper {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) :
    (Challenge.stackGraph x (Challenge.idD n)).Reachable
      (Challenge.outer p) (Challenge.upper p) := by
  cases p with
  | inl a => exact SimpleGraph.Reachable.rfl
  | inr a =>
    apply reachable_of_stackEdge
    exact Or.inr ⟨Sum.inr a, rfl, rfl⟩

/-- The partner path uses at most two identity edges and one actual diagram edge. -/
theorem reachable_id_left_partner {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) :
    (Challenge.stackGraph (Challenge.idD n) x).Reachable
      (Challenge.outer p) (Challenge.outer (x p)) := by
  have hmid : (Challenge.stackGraph (Challenge.idD n) x).Reachable
      (Challenge.lower p) (Challenge.lower (x p)) :=
    reachable_of_stackEdge _ _ (Or.inr ⟨p, rfl, rfl⟩)
  exact (outer_to_lower x p).trans (hmid.trans (outer_to_lower x (x p)).symm)

theorem reachable_id_right_partner {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (p : Challenge.Pt n) :
    (Challenge.stackGraph x (Challenge.idD n)).Reachable
      (Challenge.outer p) (Challenge.outer (x p)) := by
  have hmid : (Challenge.stackGraph x (Challenge.idD n)).Reachable
      (Challenge.upper p) (Challenge.upper (x p)) :=
    reachable_of_stackEdge _ _ (Or.inl ⟨p, rfl, rfl⟩)
  exact (outer_to_upper x p).trans (hmid.trans (outer_to_upper x (x p)).symm)

/-- Exact outer connectivity of the left-unit stack, including singleton blocks. -/
theorem reachable_id_left_iff {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (p q : Challenge.Pt n) :
    (Challenge.stackGraph (Challenge.idD n) x).Reachable
      (Challenge.outer p) (Challenge.outer q) ↔ q = p ∨ q = x p := by
  constructor
  · intro h
    simpa only [foldLeft_outer] using
      projection_of_reachable _ foldLeft x hx (foldLeft_adj x hx) h
  · rintro (rfl | rfl)
    · exact SimpleGraph.Reachable.rfl
    · exact reachable_id_left_partner x p

/-- Exact outer connectivity of the right-unit stack, including singleton blocks. -/
theorem reachable_id_right_iff {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (p q : Challenge.Pt n) :
    (Challenge.stackGraph x (Challenge.idD n)).Reachable
      (Challenge.outer p) (Challenge.outer q) ↔ q = p ∨ q = x p := by
  constructor
  · intro h
    simpa only [foldRight_outer] using
      projection_of_reachable _ foldRight x hx (foldRight_adj x hx) h
  · rintro (rfl | rfl)
    · exact SimpleGraph.Reachable.rfl
    · exact reachable_id_right_partner x p

/-- The frozen first-partner search for a left identity returns exactly the original partner. -/
theorem dmul_id_left {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) : Challenge.dmul (Challenge.idD n) x = x := by
  funext p
  by_cases hfix : x p = p
  · rw [hfix]
    apply DiagramProduct.dmul_eq_self_of_no_partner
    intro q hqp hreach
    rcases (reachable_id_left_iff x hx p q).mp hreach with h | h
    · exact hqp h
    · exact hqp (h.trans hfix)
  · apply DiagramProduct.dmul_eq_of_partner _ _ p (x p) hfix
      (reachable_id_left_partner x p)
    intro q hqp hreach
    exact ((reachable_id_left_iff x hx p q).mp hreach).resolve_left hqp

/-- The frozen first-partner search for a right identity returns exactly the original partner. -/
theorem dmul_id_right {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) : Challenge.dmul x (Challenge.idD n) = x := by
  funext p
  by_cases hfix : x p = p
  · rw [hfix]
    apply DiagramProduct.dmul_eq_self_of_no_partner
    intro q hqp hreach
    rcases (reachable_id_right_iff x hx p q).mp hreach with h | h
    · exact hqp h
    · exact hqp (h.trans hfix)
  · apply DiagramProduct.dmul_eq_of_partner _ _ p (x p) hfix
      (reachable_id_right_partner x p)
    intro q hqp hreach
    exact ((reachable_id_right_iff x hx p q).mp hreach).resolve_left hqp

theorem idD_mem_B (n : ℕ) : Challenge.idD n ∈ Challenge.B n := by
  constructor
  · intro p
    cases p <;> rfl
  · intro p
    cases p <;> simp [Challenge.idD]

theorem idD_mem_PB (n : ℕ) : Challenge.idD n ∈ Challenge.PB n :=
  (idD_mem_B n).1

#print axioms CodexPaper5.DiagramUnits.projection_of_reachable
#print axioms CodexPaper5.DiagramUnits.reachable_id_left_iff
#print axioms CodexPaper5.DiagramUnits.reachable_id_right_iff
#print axioms CodexPaper5.DiagramUnits.dmul_id_left
#print axioms CodexPaper5.DiagramUnits.dmul_id_right
#print axioms CodexPaper5.DiagramUnits.idD_mem_B
#print axioms CodexPaper5.DiagramUnits.idD_mem_PB

end CodexPaper5.DiagramUnits
