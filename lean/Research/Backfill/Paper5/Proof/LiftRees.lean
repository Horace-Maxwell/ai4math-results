import Research.Backfill.Paper5.Proof.ReesBasic
import Research.Backfill.Paper5.Proof.CycleRemarks

set_option autoImplicit false

namespace CodexPaper5.LiftRees

open BackfillPaper5 Function

variable {r : ℕ} {H : Type}

/-- The actual parity quotient of the nonzero Rees coordinates, extended by zero. -/
def project : Challenge.Rees0 (Challenge.Sym r) H H → Option (H × ZMod 2 × H)
  | none => none
  | some (i, g, l) => some (i, Challenge.sgn g, l)

/-- The even residual in the left-coset decomposition `g = rep (sgn g) * residual`. -/
def residual (rep : ZMod 2 → Challenge.Sym r) (g : Challenge.Sym r) : Challenge.Sym r :=
  (rep (Challenge.sgn g))⁻¹ * g

/-- Explicit lifting of the paper's formula. The two `none` branches are ruled out on
nonzero inputs once the quotient map is assumed to be a complete mapping. -/
def liftMap (P : H → H → Option (Challenge.Sym r)) (rep : ZMod 2 → Challenge.Sym r)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H)) :
    Challenge.Rees0 (Challenge.Sym r) H H → Challenge.Rees0 (Challenge.Sym r) H H
  | none => none
  | some (i, g, l) =>
      match f (some (i, Challenge.sgn g, l)) with
      | none => none
      | some (j, v, m) =>
          (P l j).map (fun p => (j, p⁻¹ * residual rep g * p * rep v, m))

theorem residual_sgn (rep : ZMod 2 → Challenge.Sym r)
    (hrep : ∀ u, Challenge.sgn (rep u) = u) (g : Challenge.Sym r) :
    Challenge.sgn (residual rep g) = 0 := by
  rw [residual, CycleRemarks.sgn_mul, CycleRemarks.sgn_inv, hrep]
  exact CharTwo.add_self_eq_zero _

theorem quotient_fix_zero (P : H → H → Option (Challenge.Sym r))
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f) :
    f none = none := by
  exact CodexPaper5.check_ZeroFixed _ _ none (by
    intro x
    cases x <;> exact ⟨rfl, rfl⟩) f hf

/-- Quotient completeness forces both the image triple and its sandwich entry to be nonzero. -/
theorem quotient_data (P : H → H → Option (Challenge.Sym r))
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f)
    (i : H) (u : ZMod 2) (l : H) :
    ∃ (j : H) (v : ZMod 2) (m : H) (p : Challenge.Sym r),
      f (some (i, u, l)) = some (j, v, m) ∧ P l j = some p := by
  have hn : f (some (i, u, l)) ≠ none := by
    intro he
    have hb := hf.1.1 (he.trans (quotient_fix_zero P f hf).symm)
    cases hb
  obtain ⟨⟨j, v, m⟩, hq⟩ := Option.ne_none_iff_exists'.mp hn
  have hpne : P l j ≠ none := by
    intro hp
    have hz : Challenge.mulZ2 (Challenge.sgnMat P) (some (i, u, l))
        (f (some (i, u, l))) =
        Challenge.mulZ2 (Challenge.sgnMat P) none (f none) := by
      simp [Challenge.mulZ2, Challenge.sgnMat, hq, hp]
    have hb := hf.2.1 hz
    cases hb
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hpne
  exact ⟨j, v, m, p, hq, hp⟩

/-- This is a homomorphism for the actual frozen Rees products, including all zero branches. -/
theorem project_mul (P : H → H → Option (Challenge.Sym r))
    (x y : Challenge.Rees0 (Challenge.Sym r) H H) :
    project (Challenge.rees0Mul P x y) =
      Challenge.mulZ2 (Challenge.sgnMat P) (project x) (project y) := by
  rcases x with _ | ⟨i, g, l⟩ <;> rcases y with _ | ⟨j, h, m⟩
  · rfl
  · rfl
  · rfl
  · cases hp : P l j with
    | none => simp [Challenge.rees0Mul, Challenge.mulZ2, Challenge.sgnMat, project, hp]
    | some p =>
        simp [Challenge.rees0Mul, Challenge.mulZ2, Challenge.sgnMat, project, hp,
          CycleRemarks.sgn_mul]

theorem liftMap_some (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (i j l m : H) (g p : Challenge.Sym r) (v : ZMod 2)
    (hq : f (some (i, Challenge.sgn g, l)) = some (j, v, m)) (hp : P l j = some p) :
    liftMap P rep f (some (i, g, l)) =
      some (j, p⁻¹ * residual rep g * p * rep v, m) := by
  simp only [liftMap, hq, hp, Option.map_some]

theorem project_liftMap (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r) (hrep : ∀ u, Challenge.sgn (rep u) = u)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f)
    (x : Challenge.Rees0 (Challenge.Sym r) H H) :
    project (liftMap P rep f x) = f (project x) := by
  rcases x with _ | ⟨i, g, l⟩
  · exact (quotient_fix_zero P f hf).symm
  · obtain ⟨j, v, m, p, hq, hp⟩ := quotient_data P f hf i (Challenge.sgn g) l
    have hs : Challenge.sgn (p⁻¹ * residual rep g * p * rep v) = v := by
      rw [CycleRemarks.sgn_mul, CycleRemarks.sgn_mul, CycleRemarks.sgn_mul,
        CycleRemarks.sgn_inv, residual_sgn rep hrep, hrep]
      simp only [add_zero, CharTwo.add_self_eq_zero, zero_add]
    rw [liftMap_some P rep f i j l m g p v hq hp]
    simpa only [project, hs] using hq.symm

theorem project_product_liftMap (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r) (hrep : ∀ u, Challenge.sgn (rep u) = u)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f)
    (x : Challenge.Rees0 (Challenge.Sym r) H H) :
    project (Challenge.rees0Mul P x (liftMap P rep f x)) =
      Challenge.mulZ2 (Challenge.sgnMat P) (project x) (f (project x)) := by
  rw [project_mul, project_liftMap P rep hrep f hf]

/-- The group computation retains the paper's noncommutative factor order. -/
theorem product_liftMap_some (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (i j l m : H) (g p : Challenge.Sym r) (v : ZMod 2)
    (hq : f (some (i, Challenge.sgn g, l)) = some (j, v, m)) (hp : P l j = some p) :
    Challenge.rees0Mul P (some (i, g, l)) (liftMap P rep f (some (i, g, l))) =
      some (i, rep (Challenge.sgn g) * (residual rep g * residual rep g) * p * rep v, m) := by
  rw [liftMap_some P rep f i j l m g p v hq hp]
  simp only [Challenge.rees0Mul, hp, Option.map_some]
  apply congrArg (fun k : Challenge.Sym r => some (i, k, m))
  dsimp only [residual]
  group

theorem liftMap_injective (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r) (hrep : ∀ u, Challenge.sgn (rep u) = u)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f) :
    Injective (liftMap P rep f) := by
  intro x y hxy
  have hbase : project x = project y := hf.1.1 (by
    calc
      f (project x) = project (liftMap P rep f x) := (project_liftMap P rep hrep f hf x).symm
      _ = project (liftMap P rep f y) := congrArg project hxy
      _ = f (project y) := project_liftMap P rep hrep f hf y)
  rcases x with _ | ⟨i, g, l⟩ <;> rcases y with _ | ⟨j, h, m⟩
  · rfl
  · cases hbase
  · cases hbase
  · simp only [project, Option.some.injEq, Prod.mk.injEq] at hbase
    rcases hbase with ⟨hi, hs, hl⟩
    cases hi
    cases hl
    obtain ⟨k, v, n, p, hq, hp⟩ := quotient_data P f hf i (Challenge.sgn g) l
    have hq' : f (some (i, Challenge.sgn h, l)) = some (k, v, n) := by
      simpa only [← hs] using hq
    rw [liftMap_some P rep f i k l n g p v hq hp,
      liftMap_some P rep f i k l n h p v hq' hp] at hxy
    have heq : p⁻¹ * residual rep g * p * rep v = p⁻¹ * residual rep h * p * rep v :=
      congrArg (fun t : H × Challenge.Sym r × H => t.2.1) (Option.some.inj hxy)
    have hres : residual rep g = residual rep h :=
      mul_left_cancel (mul_right_cancel (mul_right_cancel heq))
    dsimp only [residual] at hres
    rw [← hs] at hres
    have hgh : g = h := mul_left_cancel hres
    cases hgh
    rfl

theorem product_liftMap_injective (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r) (hrep : ∀ u, Challenge.sgn (rep u) = u)
    (hsq : ∀ a b : Challenge.Sym r, Challenge.sgn a = 0 → Challenge.sgn b = 0 →
      a * a = b * b → a = b)
    (f : Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H))
    (hf : Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f) :
    Injective (fun x => Challenge.rees0Mul P x (liftMap P rep f x)) := by
  intro x y hxy
  change Challenge.rees0Mul P x (liftMap P rep f x) =
    Challenge.rees0Mul P y (liftMap P rep f y) at hxy
  have hbase : project x = project y := hf.2.1 (by
    change Challenge.mulZ2 (Challenge.sgnMat P) (project x) (f (project x)) =
      Challenge.mulZ2 (Challenge.sgnMat P) (project y) (f (project y))
    calc
      _ = project (Challenge.rees0Mul P x (liftMap P rep f x)) :=
        (project_product_liftMap P rep hrep f hf x).symm
      _ = project (Challenge.rees0Mul P y (liftMap P rep f y)) := congrArg project hxy
      _ = _ := project_product_liftMap P rep hrep f hf y)
  rcases x with _ | ⟨i, g, l⟩ <;> rcases y with _ | ⟨j, h, m⟩
  · rfl
  · cases hbase
  · cases hbase
  · simp only [project, Option.some.injEq, Prod.mk.injEq] at hbase
    rcases hbase with ⟨hi, hs, hl⟩
    cases hi
    cases hl
    obtain ⟨k, v, n, p, hq, hp⟩ := quotient_data P f hf i (Challenge.sgn g) l
    have hq' : f (some (i, Challenge.sgn h, l)) = some (k, v, n) := by
      simpa only [← hs] using hq
    rw [product_liftMap_some P rep f i k l n g p v hq hp,
      product_liftMap_some P rep f i k l n h p v hq' hp] at hxy
    have heq : rep (Challenge.sgn g) * (residual rep g * residual rep g) * p * rep v =
        rep (Challenge.sgn h) * (residual rep h * residual rep h) * p * rep v :=
      congrArg (fun t : H × Challenge.Sym r × H => t.2.1) (Option.some.inj hxy)
    rw [← hs] at heq
    have heq2 : residual rep g * residual rep g = residual rep h * residual rep h :=
      mul_left_cancel (mul_right_cancel (mul_right_cancel heq))
    have hres := hsq (residual rep g) (residual rep h)
      (residual_sgn rep hrep g) (residual_sgn rep hrep h) heq2
    dsimp only [residual] at hres
    rw [← hs] at hres
    have hgh : g = h := mul_left_cancel hres
    cases hgh
    rfl

/-- A proved construction on the actual Rees semigroups. Instantiating its two small-group
hypotheses for ranks 2 and 3 gives the frozen Lemma 4.2. -/
theorem hasCM_lift [Finite H] (P : H → H → Option (Challenge.Sym r))
    (rep : ZMod 2 → Challenge.Sym r) (hrep : ∀ u, Challenge.sgn (rep u) = u)
    (hsq : ∀ a b : Challenge.Sym r, Challenge.sgn a = 0 → Challenge.sgn b = 0 →
      a * a = b * b → a = b)
    (hq : ∃ f, Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) f) :
    ∃ f, Challenge.IsCompleteMapping (Challenge.rees0Mul P) f := by
  let : Finite (Challenge.Sym r) := Finite.of_injective
    (MulOpposite.unop : Challenge.Sym r → Equiv.Perm (Fin r)) MulOpposite.unop_injective
  obtain ⟨f, hf⟩ := hq
  exact ⟨liftMap P rep f, (liftMap_injective P rep hrep f hf).bijective_of_finite,
    (product_liftMap_injective P rep hrep hsq f hf).bijective_of_finite⟩

#print axioms CodexPaper5.LiftRees.quotient_data
#print axioms CodexPaper5.LiftRees.project_mul
#print axioms CodexPaper5.LiftRees.liftMap_injective
#print axioms CodexPaper5.LiftRees.product_liftMap_injective
#print axioms CodexPaper5.LiftRees.hasCM_lift

end CodexPaper5.LiftRees
