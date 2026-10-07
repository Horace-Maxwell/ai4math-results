import Research.Backfill.Paper5.Proof.DiagramCoordinates
import Research.Backfill.Paper5.Proof.DiagramProductCoordinates

set_option autoImplicit false

namespace CodexPaper5.DiagramPrincipalFactor

open BackfillPaper5

section Proofs

open Classical

/-- The actual typed upper half, permutation and lower half coordinates. -/
abbrev Coord (D : Challenge.Fam) (n r : ℕ) :=
  Challenge.HSub D n r × Challenge.Sym r × Challenge.HSub D n r

noncomputable def coordTuple (D : Challenge.Fam) (n r : ℕ)
    (x : Challenge.Jr D n r) : Coord D n r :=
  (⟨Challenge.topHalf x.val, DiagramExtraction.topHalf_mem_hr x.property⟩,
    Challenge.gCoord r x.val,
    ⟨Challenge.botHalf x.val, DiagramExtraction.botHalf_mem_hr x.property⟩)

def eraseCoord (D : Challenge.Fam) (n r : ℕ) (t : Coord D n r) :
    Challenge.Half n × Challenge.Sym r × Challenge.Half n :=
  (t.1.val, t.2.1, t.2.2.val)

/-- The frozen raw-coordinate bijection induces the same bijection on genuine subtypes. -/
theorem coordTuple_bijective (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) : Function.Bijective (coordTuple D n r) := by
  have hb := DiagramCoordinates.check_Prop31a D n r hocc
  constructor
  · intro x y h
    apply Subtype.ext
    apply hb.injOn x.property y.property
    exact congrArg (eraseCoord D n r) h
  · intro t
    have ht : eraseCoord D n r t ∈
        Challenge.Hr D n r ×ˢ (Set.univ ×ˢ Challenge.Hr D n r) :=
      ⟨t.1.property, Set.mem_univ _, t.2.2.property⟩
    obtain ⟨x, hx, heq⟩ := hb.surjOn ht
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · apply Prod.ext
      · exact congrArg (fun z => z.2.1) heq
      · apply Subtype.ext
        exact congrArg (fun z => z.2.2) heq

noncomputable def coordEquiv (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) : Challenge.Jr D n r ≃ Coord D n r :=
  Equiv.ofBijective (coordTuple D n r) (coordTuple_bijective D n r hocc)

noncomputable def principalEquiv (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) :
    Option (Challenge.Jr D n r) ≃ Option (Coord D n r) :=
  Equiv.optionCongr (coordEquiv D n r hocc)

theorem principalEquiv_none (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) : principalEquiv D n r hocc none = none := rfl

theorem principalEquiv_some (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) (x : Challenge.Jr D n r) :
    principalEquiv D n r hocc (some x) = some (coordTuple D n r x) := rfl

/-- Nonzero principal-factor products are exactly actual compatible middle half-diagrams. -/
theorem dmul_mem_Jr_iff_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r) :
    Challenge.dmul x y ∈ Challenge.Jr D n r ↔
      Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y) := by
  constructor
  · intro hxy
    exact (DiagramMultiplication.rank_dmul_eq_iff_compat hx hy).mp hxy.2
  · exact DiagramMultiplication.dmul_mem_Jr_of_compat hx hy

theorem sandSub_eq_some_of_compat {D : Challenge.Fam} {n r : ℕ}
    (l i : Challenge.HSub D n r) (hc : Challenge.Compat l.val i.val) :
    Challenge.sandSub D n r l i = some (Challenge.pSand r l.val i.val) := by
  simp only [Challenge.sandSub, Challenge.sand, ite_eq_left hc]

theorem sandSub_eq_none_of_not_compat {D : Challenge.Fam} {n r : ℕ}
    (l i : Challenge.HSub D n r) (hc : ¬ Challenge.Compat l.val i.val) :
    Challenge.sandSub D n r l i = none := by
  simp only [Challenge.sandSub, Challenge.sand, ite_eq_right hc]

/-- All three typed coordinates of the actual nonzero product, with proof fields erased by ext. -/
theorem coordTuple_dmul_of_compat (D : Challenge.Fam) (n r : ℕ)
    (x y : Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x.val) (Challenge.topHalf y.val)) :
    coordTuple D n r
      ⟨Challenge.dmul x.val y.val,
        DiagramMultiplication.dmul_mem_Jr_of_compat x.property y.property hc⟩ =
      ((coordTuple D n r x).1,
        (coordTuple D n r x).2.1 *
          Challenge.pSand r (Challenge.botHalf x.val) (Challenge.topHalf y.val) *
          (coordTuple D n r y).2.1,
        (coordTuple D n r y).2.2) := by
  apply Prod.ext
  · apply Subtype.ext
    exact DiagramMultiplication.topHalf_dmul_of_compat x.property y.property hc
  · apply Prod.ext
    · exact DiagramProductCoordinates.gCoord_dmul_of_compat x.property y.property hc
    · apply Subtype.ext
      exact DiagramMultiplication.botHalf_dmul_of_compat x.property y.property hc

/-- The same equivalence preserves the two frozen binary operations, including every zero case. -/
theorem principalEquiv_mul (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) (u v : Option (Challenge.Jr D n r)) :
    principalEquiv D n r hocc (Challenge.pfMul Challenge.dmul (Challenge.Jr D n r) u v) =
      Challenge.rees0Mul (Challenge.sandSub D n r)
        (principalEquiv D n r hocc u) (principalEquiv D n r hocc v) := by
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some y => rfl
  | some x =>
    cases v with
    | none => rfl
    | some y =>
      by_cases hc : Challenge.Compat (Challenge.botHalf x.val) (Challenge.topHalf y.val)
      · have hm := DiagramMultiplication.dmul_mem_Jr_of_compat x.property y.property hc
        rw [Challenge.pfMul, dite_eq_left hm, principalEquiv_some,
          principalEquiv_some, principalEquiv_some]
        change some (coordTuple D n r ⟨Challenge.dmul x.val y.val, hm⟩) =
          (Challenge.sandSub D n r (coordTuple D n r x).2.2 (coordTuple D n r y).1).map
            (fun p => ((coordTuple D n r x).1,
              (coordTuple D n r x).2.1 * p * (coordTuple D n r y).2.1,
              (coordTuple D n r y).2.2))
        rw [sandSub_eq_some_of_compat _ _ hc, Option.map_some]
        exact congrArg some (coordTuple_dmul_of_compat D n r x y hc)
      · have hm : Challenge.dmul x.val y.val ∉ Challenge.Jr D n r :=
          fun h => hc ((dmul_mem_Jr_iff_compat x.property y.property).mp h)
        rw [Challenge.pfMul, dite_eq_right hm, principalEquiv_none,
          principalEquiv_some, principalEquiv_some]
        change none =
          (Challenge.sandSub D n r (coordTuple D n r x).2.2 (coordTuple D n r y).1).map
            (fun p => ((coordTuple D n r x).1,
              (coordTuple D n r x).2.1 * p * (coordTuple D n r y).2.1,
              (coordTuple D n r y).2.2))
        rw [sandSub_eq_none_of_not_compat _ _ hc, Option.map_none]

/-- The concrete coordinate clause belongs to the same equivalence used in the product law. -/
theorem principalEquiv_coords (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) (x : Challenge.Jr D n r) (t : Coord D n r)
    (h : principalEquiv D n r hocc (some x) = some t) :
    t.1.val = Challenge.topHalf x.val ∧ t.2.1 = Challenge.gCoord r x.val ∧
      t.2.2.val = Challenge.botHalf x.val := by
  have ht : coordTuple D n r x = t :=
    Option.some.inj ((principalEquiv_some D n r hocc x).symm.trans h)
  subst t
  exact ⟨rfl, rfl, rfl⟩

theorem check_Prop31iso : Challenge.Prop31iso := by
  intro D n r hocc
  exact ⟨principalEquiv D n r hocc, principalEquiv_none D n r hocc,
    principalEquiv_coords D n r hocc, principalEquiv_mul D n r hocc⟩

end Proofs

#print axioms CodexPaper5.DiagramPrincipalFactor.coordTuple_bijective
#print axioms CodexPaper5.DiagramPrincipalFactor.principalEquiv_none
#print axioms CodexPaper5.DiagramPrincipalFactor.principalEquiv_some
#print axioms CodexPaper5.DiagramPrincipalFactor.dmul_mem_Jr_iff_compat
#print axioms CodexPaper5.DiagramPrincipalFactor.sandSub_eq_some_of_compat
#print axioms CodexPaper5.DiagramPrincipalFactor.sandSub_eq_none_of_not_compat
#print axioms CodexPaper5.DiagramPrincipalFactor.coordTuple_dmul_of_compat
#print axioms CodexPaper5.DiagramPrincipalFactor.principalEquiv_mul
#print axioms CodexPaper5.DiagramPrincipalFactor.principalEquiv_coords
#print axioms CodexPaper5.DiagramPrincipalFactor.check_Prop31iso

end CodexPaper5.DiagramPrincipalFactor
