import Research.Backfill.Paper5.Proof.DiagramUnits

set_option autoImplicit false

namespace CodexPaper5.StackGammaProjection

open BackfillPaper5 Function

/-- Project genuine through endpoints to their middle-row partners. Outer horizontal
blocks and singletons map to none; no default element of Fin n is chosen. -/
def collapse {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (v : Challenge.SPt n) : Option (Fin n) :=
  if v.1 = 0 then
    match x (Sum.inl v.2) with
    | Sum.inl _ => none
    | Sum.inr b => some b
  else if v.1 = 1 then some v.2
  else
    match y (Sum.inr v.2) with
    | Sum.inl a => some a
    | Sum.inr _ => none

theorem collapse_top {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n) (a : Fin n) :
    collapse x y (0, a) =
      (match x (Sum.inl a) with | Sum.inl _ => none | Sum.inr b => some b) := rfl

theorem collapse_middle {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n) (a : Fin n) :
    collapse x y (1, a) = some a := rfl

theorem collapse_bottom {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n) (b : Fin n) :
    collapse x y (2, b) =
      (match y (Sum.inr b) with | Sum.inl a => some a | Sum.inr _ => none) := rfl

/-- Lift actual gamma reachability to Option. The none class is separate from every
some class, but may merge different outer components; only forward preservation is claimed. -/
def middleRel {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n) :
    Option (Fin n) → Option (Fin n) → Prop
  | none, none => True
  | some a, some b => (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a b
  | _, _ => False

theorem middleRel_refl {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (a : Option (Fin n)) : middleRel x y a a := by
  cases a with
  | none => trivial
  | some a => exact SimpleGraph.Reachable.rfl

theorem middleRel_symm {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Option (Fin n)} (h : middleRel x y a b) : middleRel x y b a := by
  cases a <;> cases b
  · trivial
  · exact h.elim
  · exact h.elim
  · exact SimpleGraph.Reachable.symm h

theorem middleRel_trans {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b c : Option (Fin n)} (hab : middleRel x y a b) (hbc : middleRel x y b c) :
    middleRel x y a c := by
  cases a <;> cases b <;> cases c
  · trivial
  · exact hbc.elim
  · exact hab.elim
  · exact hab.elim
  · exact hab.elim
  · exact hab.elim
  · exact hbc.elim
  · exact SimpleGraph.Reachable.trans hab hbc

/-- A genuine horizontal middle block of x is gamma-reachable, including a singleton. -/
theorem gamma_reachable_bot {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Fin n} (hxa : x (Sum.inr a) = Sum.inr b) :
    (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a b := by
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    change a ≠ b ∧ (Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) a b ∨
      Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) b a)
    refine ⟨hab, Or.inl (Or.inl ⟨?_, Ne.symm hab⟩)⟩
    simp only [Challenge.botHalf, hxa]

/-- A genuine horizontal middle block of y is gamma-reachable, including a singleton. -/
theorem gamma_reachable_top {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Fin n} (hya : y (Sum.inl a) = Sum.inl b) :
    (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a b := by
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    change a ≠ b ∧ (Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) a b ∨
      Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) b a)
    refine ⟨hab, Or.inl (Or.inr ⟨?_, Ne.symm hab⟩)⟩
    simp only [Challenge.topHalf, hya]

/-- Each actual upper block projects to middleRel; the inverse block handles the second endpoint. -/
theorem collapse_upper_edge {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (p : Challenge.Pt n) :
    middleRel x y (collapse x y (Challenge.upper p))
      (collapse x y (Challenge.upper (x p))) := by
  cases p with
  | inl a =>
    cases hxa : x (Sum.inl a) with
    | inl b =>
      have hxb : x (Sum.inl b) = Sum.inl a := by
        simpa only [hxa] using hx (Sum.inl a)
      simp only [Challenge.upper, collapse_top, hxa, hxb, middleRel]
    | inr b =>
      simpa only [Challenge.upper, collapse_top, collapse_middle, hxa, middleRel] using
        (SimpleGraph.Reachable.rfl :
          (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable b b)
  | inr a =>
    cases hxa : x (Sum.inr a) with
    | inl b =>
      have hxb : x (Sum.inl b) = Sum.inr a := by
        simpa only [hxa] using hx (Sum.inr a)
      simpa only [Challenge.upper, collapse_top, collapse_middle, hxa, hxb, middleRel] using
        (SimpleGraph.Reachable.rfl :
          (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a a)
    | inr b =>
      simpa only [Challenge.upper, collapse_middle, hxa, middleRel] using
        gamma_reachable_bot x y hxa

/-- Each actual lower block projects to middleRel, in the original multiplication order. -/
theorem collapse_lower_edge {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (hy : Challenge.IsPB y) (p : Challenge.Pt n) :
    middleRel x y (collapse x y (Challenge.lower p))
      (collapse x y (Challenge.lower (y p))) := by
  cases p with
  | inl a =>
    cases hya : y (Sum.inl a) with
    | inl b =>
      simpa only [Challenge.lower, collapse_middle, hya, middleRel] using
        gamma_reachable_top x y hya
    | inr b =>
      have hyb : y (Sum.inr b) = Sum.inl a := by
        simpa only [hya] using hy (Sum.inl a)
      simpa only [Challenge.lower, collapse_middle, collapse_bottom, hya, hyb, middleRel] using
        (SimpleGraph.Reachable.rfl :
          (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a a)
  | inr a =>
    cases hya : y (Sum.inr a) with
    | inl b =>
      simpa only [Challenge.lower, collapse_middle, collapse_bottom, hya, middleRel] using
        (SimpleGraph.Reachable.rfl :
          (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable b b)
    | inr b =>
      have hyb : y (Sum.inr b) = Sum.inr a := by
        simpa only [hya] using hy (Sum.inr a)
      simp only [Challenge.lower, collapse_bottom, hya, hyb, middleRel]

theorem collapse_stackEdge {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {u v : Challenge.SPt n}
    (h : Challenge.stackEdge x y u v) : middleRel x y (collapse x y u) (collapse x y v) := by
  rcases h with ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩
  · exact collapse_upper_edge x y hx p
  · exact collapse_lower_edge x y hy p

theorem collapse_adj {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {u v : Challenge.SPt n}
    (h : (Challenge.stackGraph x y).Adj u v) :
    middleRel x y (collapse x y u) (collapse x y v) := by
  change u ≠ v ∧ (Challenge.stackEdge x y u v ∨ Challenge.stackEdge x y v u) at h
  rcases h.2 with h | h
  · exact collapse_stackEdge hx hy h
  · exact middleRel_symm x y (collapse_stackEdge hx hy h)

/-- Only forward preservation: this does not identify distinct none-components. -/
theorem collapse_reachable {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {u v : Challenge.SPt n}
    (h : (Challenge.stackGraph x y).Reachable u v) :
    middleRel x y (collapse x y u) (collapse x y v) := by
  have hp := ((Challenge.stackGraph x y).reachable_iff_reflTransGen u v).mp h
  clear h
  induction hp with
  | refl => exact middleRel_refl x y _
  | tail _ huv ih => exact middleRel_trans x y ih (collapse_adj hx hy huv)

/-- Every nontrivial actual half-arc is a real middle-row block of x or y. -/
theorem middle_reachable_of_gammaEdge {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Fin n} (h : Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) a b) :
    (Challenge.stackGraph x y).Reachable (1, a) (1, b) := by
  rcases h with ⟨hxb, hne⟩ | ⟨hyb, hne⟩
  · cases hxa : x (Sum.inr a) with
    | inl c =>
      have hab : a = b := by simpa only [Challenge.botHalf, hxa] using hxb
      exact (hne hab.symm).elim
    | inr c =>
      have hcb : c = b := by simpa only [Challenge.botHalf, hxa] using hxb
      apply DiagramUnits.reachable_of_stackEdge x y
      exact Or.inl ⟨Sum.inr a, rfl, by simp only [hxa, Challenge.upper, hcb]⟩
  · cases hya : y (Sum.inl a) with
    | inl c =>
      have hcb : c = b := by simpa only [Challenge.topHalf, hya] using hyb
      apply DiagramUnits.reachable_of_stackEdge x y
      exact Or.inr ⟨Sum.inl a, rfl, by simp only [hya, Challenge.lower, hcb]⟩
    | inr c =>
      have hab : a = b := by simpa only [Challenge.topHalf, hya] using hyb
      exact (hne hab.symm).elim

theorem middle_reachable_of_gammaAdj {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Fin n} (h : (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Adj a b) :
    (Challenge.stackGraph x y).Reachable (1, a) (1, b) := by
  change a ≠ b ∧ (Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) a b ∨
    Challenge.GammaEdge (Challenge.botHalf x) (Challenge.topHalf y) b a) at h
  rcases h.2 with h | h
  · exact middle_reachable_of_gammaEdge x y h
  · exact (middle_reachable_of_gammaEdge x y h).symm

/-- Lift genuine gamma paths only between actual middle vertices. No none inverse is asserted. -/
theorem middle_reachable_of_gamma {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a b : Fin n}
    (h : (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable a b) :
    (Challenge.stackGraph x y).Reachable (1, a) (1, b) := by
  have hp := ((Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).reachable_iff_reflTransGen a b).mp h
  clear h
  induction hp with
  | refl => exact SimpleGraph.Reachable.rfl
  | tail _ huv ih => exact ih.trans (middle_reachable_of_gammaAdj x y huv)

theorem top_through_reachable {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {a u : Fin n} (hxa : x (Sum.inl a) = Sum.inr u) :
    (Challenge.stackGraph x y).Reachable (Challenge.outer (Sum.inl a)) (1, u) := by
  apply DiagramUnits.reachable_of_stackEdge x y
  exact Or.inl ⟨Sum.inl a, rfl, by simp only [hxa, Challenge.upper]⟩

theorem bot_through_reachable {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    {e b : Fin n} (hye : y (Sum.inl e) = Sum.inr b) :
    (Challenge.stackGraph x y).Reachable (1, e) (Challenge.outer (Sum.inr b)) := by
  apply DiagramUnits.reachable_of_stackEdge x y
  exact Or.inr ⟨Sum.inl e, rfl, by simp only [hye, Challenge.lower, Challenge.outer]⟩

/-- The genuine outer through-endpoint bridge, with both endpoint through blocks specified. -/
theorem outer_through_reachable_iff {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {a u e b : Fin n}
    (hxa : x (Sum.inl a) = Sum.inr u) (hye : y (Sum.inl e) = Sum.inr b) :
    (Challenge.stackGraph x y).Reachable (Challenge.outer (Sum.inl a))
      (Challenge.outer (Sum.inr b)) ↔
    (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable u e := by
  constructor
  · intro h
    have hyb : y (Sum.inr b) = Sum.inl e := by simpa only [hye] using hy (Sum.inl e)
    have hr := collapse_reachable hx hy h
    simpa only [Challenge.outer, collapse_top, collapse_bottom, hxa, hyb, middleRel] using hr
  · intro h
    exact (top_through_reachable x y hxa).trans
      ((middle_reachable_of_gamma x y h).trans (bot_through_reachable x y hye))

/-- The exact requested product bridge for every n, using the frozen list-search product.
There is no extra rank, compatibility, nonzero-size or preselected-path hypothesis. -/
theorem dmul_through_iff {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {a u e b : Fin n}
    (hxa : x (Sum.inl a) = Sum.inr u) (hye : y (Sum.inl e) = Sum.inr b) :
    Challenge.dmul x y (Sum.inl a) = Sum.inr b ↔
    (Challenge.gammaGraph (Challenge.botHalf x) (Challenge.topHalf y)).Reachable u e := by
  have hne : (Sum.inr b : Challenge.Pt n) ≠ Sum.inl a := Sum.inr_ne_inl
  constructor
  · intro hprod
    have hreach : (Challenge.stackGraph x y).Reachable
        (Challenge.outer (Sum.inl a)) (Challenge.outer (Sum.inr b)) := by
      rcases DiagramProduct.dmul_spec x y (Sum.inl a) with hdefault | ⟨_hne, hpath⟩
      · exact (hne (hprod.symm.trans hdefault)).elim
      · simpa only [hprod] using hpath
    exact (outer_through_reachable_iff hx hy hxa hye).mp hreach
  · intro hgamma
    have hreach := (outer_through_reachable_iff hx hy hxa hye).mpr hgamma
    apply DiagramProduct.dmul_eq_of_partner x y (Sum.inl a) (Sum.inr b) hne hreach
    intro q hq hpath
    exact StackGeometry.outer_partner_unique hx hy hq hne hpath hreach

#print axioms CodexPaper5.StackGammaProjection.collapse_upper_edge
#print axioms CodexPaper5.StackGammaProjection.collapse_lower_edge
#print axioms CodexPaper5.StackGammaProjection.collapse_stackEdge
#print axioms CodexPaper5.StackGammaProjection.collapse_adj
#print axioms CodexPaper5.StackGammaProjection.collapse_reachable
#print axioms CodexPaper5.StackGammaProjection.middle_reachable_of_gammaEdge
#print axioms CodexPaper5.StackGammaProjection.middle_reachable_of_gammaAdj
#print axioms CodexPaper5.StackGammaProjection.middle_reachable_of_gamma
#print axioms CodexPaper5.StackGammaProjection.top_through_reachable
#print axioms CodexPaper5.StackGammaProjection.bot_through_reachable
#print axioms CodexPaper5.StackGammaProjection.outer_through_reachable_iff
#print axioms CodexPaper5.StackGammaProjection.dmul_through_iff

end CodexPaper5.StackGammaProjection
