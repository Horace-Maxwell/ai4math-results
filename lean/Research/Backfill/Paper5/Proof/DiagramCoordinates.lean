import Research.Backfill.Paper5.Proof.HalfDiagonal
import Research.Backfill.Paper5.Proof.DiagramExtraction

set_option autoImplicit false

namespace CodexPaper5.DiagramCoordinates

open BackfillPaper5

/-- Join the actual free points by e and preserve every nonfree half-diagram arc or singleton. -/
def glue {n : ℕ} (l i : Challenge.Half n) (e : l.1 ≃ i.1) : Challenge.Pt n → Challenge.Pt n
  | .inl a => if ha : a ∈ l.1 then .inr (e ⟨a, ha⟩).val else .inl (l.2 a)
  | .inr b => if hb : b ∈ i.1 then .inl (e.symm ⟨b, hb⟩).val else .inr (i.2 b)

theorem glue_inl_mem {n : ℕ} {l i : Challenge.Half n} (e : l.1 ≃ i.1)
    {a : Fin n} (ha : a ∈ l.1) : glue l i e (.inl a) = .inr (e ⟨a, ha⟩).val := by
  simp only [glue, dite_eq_left ha]

theorem glue_inl_not_mem {n : ℕ} {l i : Challenge.Half n} (e : l.1 ≃ i.1)
    {a : Fin n} (ha : a ∉ l.1) : glue l i e (.inl a) = .inl (l.2 a) := by
  simp only [glue, dite_eq_right ha]

theorem glue_inr_mem {n : ℕ} {l i : Challenge.Half n} (e : l.1 ≃ i.1)
    {b : Fin n} (hb : b ∈ i.1) : glue l i e (.inr b) = .inl (e.symm ⟨b, hb⟩).val := by
  simp only [glue, dite_eq_left hb]

theorem glue_inr_not_mem {n : ℕ} {l i : Challenge.Half n} (e : l.1 ≃ i.1)
    {b : Fin n} (hb : b ∉ i.1) : glue l i e (.inr b) = .inr (i.2 b) := by
  simp only [glue, dite_eq_right hb]

/-- An involution fixing the free points cannot carry a nonfree point into the free set. -/
theorem half_maps_nonfree {D : Challenge.Fam} {n r : ℕ} {h : Challenge.Half n}
    (hh : Challenge.IsHalf D n r h) {a : Fin n} (ha : a ∉ h.1) : h.2 a ∉ h.1 := by
  intro hma
  have heq : h.2 a = a := (hh.2.2.1 (h.2 a) hma).symm.trans (hh.2.1 a)
  exact ha (heq ▸ hma)

theorem glue_isPB {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf D n r l) (hi : Challenge.IsHalf D n r i) (e : l.1 ≃ i.1) :
    Challenge.IsPB (glue l i e) := by
  intro p
  cases p with
  | inl a =>
    by_cases ha : a ∈ l.1
    · rw [glue_inl_mem e ha, glue_inr_mem e (e ⟨a, ha⟩).property]
      change Sum.inl (e.symm (e ⟨a, ha⟩)).val = Sum.inl a
      rw [e.symm_apply_apply]
    · rw [glue_inl_not_mem e ha, glue_inl_not_mem e (half_maps_nonfree hl ha)]
      exact congrArg Sum.inl (hl.2.1 a)
  | inr b =>
    by_cases hb : b ∈ i.1
    · rw [glue_inr_mem e hb, glue_inl_mem e (e.symm ⟨b, hb⟩).property]
      change Sum.inr (e (e.symm ⟨b, hb⟩)).val = Sum.inr b
      rw [e.apply_symm_apply]
    · rw [glue_inr_not_mem e hb, glue_inr_not_mem e (half_maps_nonfree hi hb)]
      exact congrArg Sum.inr (hi.2.1 b)

theorem topHalf_glue {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf D n r l) (e : l.1 ≃ i.1) : Challenge.topHalf (glue l i e) = l := by
  apply Prod.ext
  · apply Finset.ext
    intro a
    change (a ∈ Finset.univ.filter (fun a => (glue l i e (.inl a)).isRight)) ↔ a ∈ l.1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : a ∈ l.1
    · rw [glue_inl_mem e ha]
      simpa using ha
    · rw [glue_inl_not_mem e ha]
      simpa using ha
  · funext a
    by_cases ha : a ∈ l.1
    · simp [Challenge.topHalf, glue, ha, hl.2.2.1 a ha]
    · simp [Challenge.topHalf, glue, ha]

theorem botHalf_glue {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hi : Challenge.IsHalf D n r i) (e : l.1 ≃ i.1) : Challenge.botHalf (glue l i e) = i := by
  apply Prod.ext
  · apply Finset.ext
    intro b
    change (b ∈ Finset.univ.filter (fun b => (glue l i e (.inr b)).isLeft)) ↔ b ∈ i.1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hb : b ∈ i.1
    · rw [glue_inr_mem e hb]
      simpa using hb
    · rw [glue_inr_not_mem e hb]
      simpa using hb
  · funext b
    by_cases hb : b ∈ i.1
    · simp [Challenge.botHalf, glue, hb, hi.2.2.1 b hb]
    · simp [Challenge.botHalf, glue, hb]

theorem glue_no_fixed {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf .B n r l) (hi : Challenge.IsHalf .B n r i) (e : l.1 ≃ i.1) :
    ∀ p, glue l i e p ≠ p := by
  intro p
  cases p with
  | inl a =>
    by_cases ha : a ∈ l.1
    · rw [glue_inl_mem e ha]
      exact Sum.inr_ne_inl
    · rw [glue_inl_not_mem e ha]
      intro h
      exact hl.2.2.2 rfl a ha (Sum.inl.inj h)
  | inr b =>
    by_cases hb : b ∈ i.1
    · rw [glue_inr_mem e hb]
      exact Sum.inl_ne_inr
    · rw [glue_inr_not_mem e hb]
      intro h
      exact hi.2.2.2 rfl b hb (Sum.inr.inj h)

theorem glue_mem_Jr {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf D n r l) (hi : Challenge.IsHalf D n r i) (e : l.1 ≃ i.1) :
    glue l i e ∈ Challenge.Jr D n r := by
  constructor
  · cases D with
    | B => exact ⟨glue_isPB hl hi e, glue_no_fixed hl hi e⟩
    | PB => exact glue_isPB hl hi e
  · change (Challenge.topHalf (glue l i e)).1.card = r
    rw [topHalf_glue hl e]
    exact hl.1

/-- Increasing source coordinates, then the genuine permutation, then increasing target coordinates. -/
noncomputable def orderedLink {n r : ℕ} (l i : Challenge.Half n)
    (hL : l.1.card = r) (hI : i.1.card = r) (g : Challenge.Sym r) : l.1 ≃ i.1 :=
  (((l.1.orderIsoOfFin hL).toEquiv.symm).trans (MulOpposite.unop g)).trans
    (i.1.orderIsoOfFin hI).toEquiv

noncomputable def assemble {n r : ℕ} (l i : Challenge.Half n)
    (hL : l.1.card = r) (hI : i.1.card = r) (g : Challenge.Sym r) : Challenge.Pt n → Challenge.Pt n :=
  glue l i (orderedLink l i hL hI g)

theorem assemble_repG {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf D n r l) (hi : Challenge.IsHalf D n r i) (g : Challenge.Sym r) :
    Challenge.RepG r (assemble l i hl.1 hi.1 g) g := by
  intro k a b hx hk
  have ha : a ∈ l.1 := by
    by_contra ha
    rw [assemble, glue_inl_not_mem _ ha] at hx
    exact Sum.inl_ne_inr hx
  have hb : (orderedLink l i hl.1 hi.1 g ⟨a, ha⟩).val = b := by
    rw [assemble, glue_inl_mem _ ha] at hx
    exact Sum.inr.inj hx
  have hk' : Challenge.pos l.1 a = k.val := by
    simpa only [assemble, topHalf_glue hl] using hk
  have hk'' : (l.1.orderIsoOfFin hl.1).symm ⟨a, ha⟩ = k := by
    apply Fin.ext
    exact (HalfDiagonal.pos_orderIsoOfFin_symm l.1 hl.1 ⟨a, ha⟩).symm.trans hk'
  rw [show Challenge.botHalf (assemble l i hl.1 hi.1 g) = i from
    botHalf_glue hi (orderedLink l i hl.1 hi.1 g), ← hb]
  change ((MulOpposite.unop g) k).val =
    Challenge.pos i.1 (i.1.orderIsoOfFin hi.1
      ((MulOpposite.unop g) ((l.1.orderIsoOfFin hl.1).symm ⟨a, ha⟩))).val
  rw [HalfDiagonal.pos_orderIsoOfFin, hk'']

/-- Every free source index is realized, so a representing permutation is unique. -/
theorem repG_unique {n r : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hc : (Challenge.topHalf x).1.card = r) {g h : Challenge.Sym r}
    (hg : Challenge.RepG r x g) (hh : Challenge.RepG r x h) : g = h := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro k
  apply Fin.ext
  obtain ⟨a, ha, hk⟩ := HalfDiagonal.exists_mem_pos_eq (Challenge.topHalf x).1 hc k
  cases hxa : x (.inl a) with
  | inl b => simp [Challenge.topHalf, hxa] at ha
  | inr b => exact (hg k a b hxa hk).trans (hh k a b hxa hk).symm

theorem assemble_gCoord {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : Challenge.IsHalf D n r l) (hi : Challenge.IsHalf D n r i) (g : Challenge.Sym r) :
    Challenge.gCoord r (assemble l i hl.1 hi.1 g) = g := by
  classical
  have hex : ∃ p, Challenge.RepG r (assemble l i hl.1 hi.1 g) p := ⟨g, assemble_repG hl hi g⟩
  rw [Challenge.gCoord, dite_eq_left hex]
  apply repG_unique (g := hex.choose) (h := g) _ hex.choose_spec (assemble_repG hl hi g)
  rw [show Challenge.topHalf (assemble l i hl.1 hi.1 g) = l from
    topHalf_glue hl (orderedLink l i hl.1 hi.1 g)]
  exact hl.1

/-- Equal frozen positions distinguish actual members of any finite ordered free set. -/
theorem eq_of_pos_eq {n r : ℕ} (F : Finset (Fin n)) (hc : F.card = r)
    {a b : Fin n} (ha : a ∈ F) (hb : b ∈ F) (hab : Challenge.pos F a = Challenge.pos F b) : a = b := by
  let e := F.orderIsoOfFin hc
  have heq : e.symm ⟨a, ha⟩ = e.symm ⟨b, hb⟩ := by
    apply Fin.ext
    exact (HalfDiagonal.pos_orderIsoOfFin_symm F hc ⟨a, ha⟩).symm.trans
      (hab.trans (HalfDiagonal.pos_orderIsoOfFin_symm F hc ⟨b, hb⟩))
  exact congrArg Subtype.val (e.symm.injective heq)

/-- An involution is determined by its actual top images and its bottom half-diagram. -/
theorem eq_of_top_action_bot {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y)
    (htop : ∀ a, x (.inl a) = y (.inl a))
    (hbot : Challenge.botHalf x = Challenge.botHalf y) : x = y := by
  funext p
  cases p with
  | inl a => exact htop a
  | inr b =>
    cases hxb : x (.inr b) with
    | inl a =>
      have hxa : x (.inl a) = .inr b := by simpa only [hxb] using hx (.inr b)
      have hya : y (.inl a) = .inr b := (htop a).symm.trans hxa
      have hyb : y (.inr b) = .inl a := by simpa only [hya] using hy (.inl a)
      exact hyb.symm
    | inr c =>
      cases hyb : y (.inr b) with
      | inl a =>
        have hya : y (.inl a) = .inr b := by simpa only [hyb] using hy (.inr b)
        have hxa : x (.inl a) = .inr b := (htop a).trans hya
        have hxb' : x (.inr b) = .inl a := by simpa only [hxa] using hx (.inl a)
        exact False.elim (Sum.inr_ne_inl (hxb.symm.trans hxb'))
      | inr d =>
        have hcd : c = d := by
          have heq := congrArg (fun h : Challenge.Half n => h.2 b) hbot
          simpa only [Challenge.botHalf, hxb, hyb] using heq
        exact congrArg Sum.inr hcd

/-- Reassemble every actual diagram from its frozen coordinates. -/
theorem assemble_of_mem_Jr {D : Challenge.Fam} {n r : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) :
    x = assemble (Challenge.topHalf x) (Challenge.botHalf x)
      (DiagramExtraction.topHalf_mem_hr hx).1 (DiagramExtraction.botHalf_mem_hr hx).1
      (Challenge.gCoord r x) := by
  let l := Challenge.topHalf x
  let i := Challenge.botHalf x
  have hl : Challenge.IsHalf D n r l := DiagramExtraction.topHalf_mem_hr hx
  have hi : Challenge.IsHalf D n r i := DiagramExtraction.botHalf_mem_hr hx
  let g := Challenge.gCoord r x
  let e := orderedLink l i hl.1 hi.1 g
  have hxinv : Challenge.IsPB x := DiagramExtraction.isPB_of_mem_Jr hx
  have hrep : Challenge.RepG r x g := DiagramExtraction.repG_gCoord_of_mem_Jr hx
  change x = glue l i e
  apply eq_of_top_action_bot hxinv (glue_isPB hl hi e)
  · intro a
    cases hxa : x (.inl a) with
    | inl b =>
      have ha : a ∉ l.1 := by simp [l, Challenge.topHalf, hxa]
      rw [glue_inl_not_mem _ ha]
      change Sum.inl b = Sum.inl (l.2 a)
      simp only [l, Challenge.topHalf, hxa]
    | inr b =>
      have ha : a ∈ l.1 := by simp [l, Challenge.topHalf, hxa]
      have hxb : x (.inr b) = .inl a := by simpa only [hxa] using hxinv (.inl a)
      have hb : b ∈ i.1 := by simp [i, Challenge.botHalf, hxb]
      rw [glue_inl_mem _ ha]
      apply congrArg Sum.inr
      apply eq_of_pos_eq i.1 hi.1 hb (e ⟨a, ha⟩).property
      let k := (l.1.orderIsoOfFin hl.1).symm ⟨a, ha⟩
      have hk : Challenge.pos l.1 a = k.val := HalfDiagonal.pos_orderIsoOfFin_symm l.1 hl.1 ⟨a, ha⟩
      calc
        Challenge.pos i.1 b = ((MulOpposite.unop g) k).val := (hrep k a b hxa hk).symm
        _ = Challenge.pos i.1 (e ⟨a, ha⟩).val :=
          (HalfDiagonal.pos_orderIsoOfFin i.1 hi.1 ((MulOpposite.unop g) k)).symm
  · exact (botHalf_glue hi e).symm

/-- Coordinate equality respects the dependent cardinality witnesses by proof irrelevance. -/
theorem assemble_congr {n r : ℕ} {l₁ l₂ i₁ i₂ : Challenge.Half n}
    {hL₁ : l₁.1.card = r} {hL₂ : l₂.1.card = r}
    {hI₁ : i₁.1.card = r} {hI₂ : i₂.1.card = r} {g₁ g₂ : Challenge.Sym r}
    (hl : l₁ = l₂) (hi : i₁ = i₂) (hg : g₁ = g₂) :
    assemble l₁ i₁ hL₁ hI₁ g₁ = assemble l₂ i₂ hL₂ hI₂ g₂ := by
  cases hl
  cases hi
  cases hg
  rfl

/-- The full frozen coordinate bijection uses the actual inverse above. -/
theorem check_Prop31a : Challenge.Prop31a := by
  intro D n r _hocc
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨DiagramExtraction.topHalf_mem_hr hx, Set.mem_univ _, DiagramExtraction.botHalf_mem_hr hx⟩
  · intro x hx y hy heq
    have ht : Challenge.topHalf x = Challenge.topHalf y := congrArg Prod.fst heq
    have hg : Challenge.gCoord r x = Challenge.gCoord r y := congrArg (fun t => t.2.1) heq
    have hb : Challenge.botHalf x = Challenge.botHalf y := congrArg (fun t => t.2.2) heq
    exact (assemble_of_mem_Jr hx).trans
      ((assemble_congr
        (hL₁ := (DiagramExtraction.topHalf_mem_hr hx).1)
        (hL₂ := (DiagramExtraction.topHalf_mem_hr hy).1)
        (hI₁ := (DiagramExtraction.botHalf_mem_hr hx).1)
        (hI₂ := (DiagramExtraction.botHalf_mem_hr hy).1) ht hb hg).trans
          (assemble_of_mem_Jr hy).symm)
  · rintro ⟨l, g, i⟩ ⟨hl, _hg, hi⟩
    refine ⟨assemble l i hl.1 hi.1 g, glue_mem_Jr hl hi (orderedLink l i hl.1 hi.1 g), ?_⟩
    exact Prod.ext (topHalf_glue hl _) (Prod.ext (assemble_gCoord hl hi g) (botHalf_glue hi _))

#print axioms CodexPaper5.DiagramCoordinates.glue_isPB
#print axioms CodexPaper5.DiagramCoordinates.topHalf_glue
#print axioms CodexPaper5.DiagramCoordinates.botHalf_glue
#print axioms CodexPaper5.DiagramCoordinates.glue_mem_Jr
#print axioms CodexPaper5.DiagramCoordinates.assemble_repG
#print axioms CodexPaper5.DiagramCoordinates.repG_unique
#print axioms CodexPaper5.DiagramCoordinates.assemble_gCoord
#print axioms CodexPaper5.DiagramCoordinates.eq_of_pos_eq
#print axioms CodexPaper5.DiagramCoordinates.eq_of_top_action_bot
#print axioms CodexPaper5.DiagramCoordinates.assemble_of_mem_Jr
#print axioms CodexPaper5.DiagramCoordinates.check_Prop31a

end CodexPaper5.DiagramCoordinates
