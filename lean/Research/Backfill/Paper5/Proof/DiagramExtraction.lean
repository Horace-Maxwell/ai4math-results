import Research.Backfill.Paper5.Proof.HalfDiagonal

set_option autoImplicit false

namespace CodexPaper5.DiagramExtraction

open BackfillPaper5 Function

abbrev TopFree {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n) :=
  {a : Fin n // a ∈ (Challenge.topHalf x).1}

abbrev BotFree {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n) :=
  {b : Fin n // b ∈ (Challenge.botHalf x).1}

theorem mem_topFree_iff {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n) (a : Fin n) :
    a ∈ (Challenge.topHalf x).1 ↔ (x (Sum.inl a)).isRight := by
  simp [Challenge.topHalf]

theorem mem_botFree_iff {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n) (b : Fin n) :
    b ∈ (Challenge.botHalf x).1 ↔ (x (Sum.inr b)).isLeft := by
  simp [Challenge.botHalf]

theorem isPB_of_mem_Jr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Challenge.IsPB x := by
  cases D with
  | B => exact hx.1.1
  | PB => exact hx.1

/-- Follow an actual through block from its top endpoint to its bottom endpoint. -/
def throughToBot {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) (a : TopFree x) : BotFree x := by
  let hright := (mem_topFree_iff x a.val).mp a.property
  let b := (x (Sum.inl a.val)).getRight hright
  have hb : Sum.inr b = x (Sum.inl a.val) := Sum.inr_getRight _ _
  refine ⟨b, (mem_botFree_iff x b).mpr ?_⟩
  rw [hb, hx]
  rfl

/-- Follow an actual through block in the reverse direction. -/
def throughToTop {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) (b : BotFree x) : TopFree x := by
  let hleft := (mem_botFree_iff x b.val).mp b.property
  let a := (x (Sum.inr b.val)).getLeft hleft
  have ha : Sum.inl a = x (Sum.inr b.val) := Sum.inl_getLeft _ _
  refine ⟨a, (mem_topFree_iff x a).mpr ?_⟩
  rw [ha, hx]
  rfl

theorem throughToBot_apply {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) (a : TopFree x) :
    x (Sum.inl a.val) = Sum.inr (throughToBot x hx a).val :=
  (Sum.inr_getRight _ _).symm

theorem throughToTop_apply {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) (b : BotFree x) :
    x (Sum.inr b.val) = Sum.inl (throughToTop x hx b).val :=
  (Sum.inl_getLeft _ _).symm

/-- The diagram involution gives a genuine equivalence between its two sets of through endpoints. -/
def throughEquiv {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) : TopFree x ≃ BotFree x where
  toFun := throughToBot x hx
  invFun := throughToTop x hx
  left_inv a := by
    apply Subtype.ext
    apply Sum.inl.inj
    calc
      Sum.inl (throughToTop x hx (throughToBot x hx a)).val =
          x (Sum.inr (throughToBot x hx a).val) :=
        (throughToTop_apply x hx (throughToBot x hx a)).symm
      _ = x (x (Sum.inl a.val)) := congrArg x (throughToBot_apply x hx a).symm
      _ = Sum.inl a.val := hx _
  right_inv b := by
    apply Subtype.ext
    apply Sum.inr.inj
    calc
      Sum.inr (throughToBot x hx (throughToTop x hx b)).val =
          x (Sum.inl (throughToTop x hx b).val) :=
        (throughToBot_apply x hx (throughToTop x hx b)).symm
      _ = x (x (Sum.inr b.val)) := congrArg x (throughToTop_apply x hx b).symm
      _ = Sum.inr b.val := hx _

theorem throughEquiv_apply {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) (a : TopFree x) :
    x (Sum.inl a.val) = Sum.inr (throughEquiv x hx a).val :=
  throughToBot_apply x hx a

theorem top_bot_free_card {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) : (Challenge.topHalf x).1.card = (Challenge.botHalf x).1.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (throughEquiv x hx)

theorem topHalf_involutive {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) : Involutive (Challenge.topHalf x).2 := by
  intro a
  cases he : x (Sum.inl a) with
  | inl b =>
    have hb : x (Sum.inl b) = Sum.inl a := by simpa only [he] using hx (Sum.inl a)
    simp only [Challenge.topHalf, he, hb]
  | inr b => simp only [Challenge.topHalf, he]

theorem botHalf_involutive {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (hx : Involutive x) : Involutive (Challenge.botHalf x).2 := by
  intro b
  cases he : x (Sum.inr b) with
  | inl a => simp only [Challenge.botHalf, he]
  | inr a =>
    have ha : x (Sum.inr a) = Sum.inr b := by simpa only [he] using hx (Sum.inr b)
    simp only [Challenge.botHalf, he, ha]

theorem topHalf_fixes_free {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (a : Fin n) (ha : a ∈ (Challenge.topHalf x).1) : (Challenge.topHalf x).2 a = a := by
  obtain ⟨b, hb⟩ := Sum.isRight_iff.mp ((mem_topFree_iff x a).mp ha)
  simp only [Challenge.topHalf, hb]

theorem botHalf_fixes_free {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n)
    (b : Fin n) (hb : b ∈ (Challenge.botHalf x).1) : (Challenge.botHalf x).2 b = b := by
  obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp ((mem_botFree_iff x b).mp hb)
  simp only [Challenge.botHalf, ha]

/-- The top coordinates of any actual rank-r diagram are a lawful half-diagram. -/
theorem topHalf_mem_hr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Challenge.topHalf x ∈ Challenge.Hr D n r := by
  refine ⟨hx.2, topHalf_involutive x (isPB_of_mem_Jr hx), topHalf_fixes_free x, ?_⟩
  intro hD a ha hfixed
  subst D
  have hnofix := hx.1.2 (Sum.inl a)
  cases he : x (Sum.inl a) with
  | inl b =>
    have hba : b = a := by simpa only [Challenge.topHalf, he] using hfixed
    apply hnofix
    simpa only [hba] using he
  | inr b =>
    exact ha ((mem_topFree_iff x a).mpr (by simp only [he, Sum.isRight_inr]))

/-- Bottom free points have the same cardinality, by the actual through-block equivalence. -/
theorem botHalf_mem_hr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Challenge.botHalf x ∈ Challenge.Hr D n r := by
  have hcard : (Challenge.botHalf x).1.card = r :=
    (top_bot_free_card x (isPB_of_mem_Jr hx)).symm.trans hx.2
  refine ⟨hcard, botHalf_involutive x (isPB_of_mem_Jr hx), botHalf_fixes_free x, ?_⟩
  intro hD b hb hfixed
  subst D
  have hnofix := hx.1.2 (Sum.inr b)
  cases he : x (Sum.inr b) with
  | inl a =>
    exact hb ((mem_botFree_iff x b).mpr (by simp only [he, Sum.isLeft_inl]))
  | inr a =>
    have hab : a = b := by simpa only [Challenge.botHalf, he] using hfixed
    apply hnofix
    simpa only [hab] using he

/-- The through permutation is the concrete endpoint equivalence, in increasing coordinates. -/
noncomputable def extractedPerm {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Equiv.Perm (Fin r) :=
  (((Challenge.topHalf x).1.orderIsoOfFin (topHalf_mem_hr hx).1).toEquiv.trans
    (throughEquiv x (isPB_of_mem_Jr hx))).trans
      ((Challenge.botHalf x).1.orderIsoOfFin (botHalf_mem_hr hx).1).toEquiv.symm

noncomputable def extractedSym {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) : Challenge.Sym r :=
  MulOpposite.op (extractedPerm hx)

/-- The constructed permutation represents the actual diagram, with the frozen right-action convention. -/
theorem repG_extractedSym {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Challenge.RepG r x (extractedSym hx) := by
  intro k a b hab hk
  have ha : a ∈ (Challenge.topHalf x).1 :=
    (mem_topFree_iff x a).mpr (by simp only [hab, Sum.isRight_inr])
  have hba : x (Sum.inr b) = Sum.inl a := by
    simpa only [hab] using isPB_of_mem_Jr hx (Sum.inl a)
  have hb : b ∈ (Challenge.botHalf x).1 :=
    (mem_botFree_iff x b).mpr (by simp only [hba, Sum.isLeft_inl])
  let aTop : TopFree x := ⟨a, ha⟩
  let bBot : BotFree x := ⟨b, hb⟩
  let et := (Challenge.topHalf x).1.orderIsoOfFin (topHalf_mem_hr hx).1
  let eb := (Challenge.botHalf x).1.orderIsoOfFin (botHalf_mem_hr hx).1
  have hidx : et.symm aTop = k := by
    apply Fin.ext
    exact (HalfDiagonal.pos_orderIsoOfFin_symm (Challenge.topHalf x).1
      (topHalf_mem_hr hx).1 aTop).symm.trans hk
  have het : et k = aTop := by
    rw [← hidx, et.apply_symm_apply]
  have hthrough : throughEquiv x (isPB_of_mem_Jr hx) aTop = bBot := by
    apply Subtype.ext
    apply Sum.inr.inj
    exact (throughEquiv_apply x (isPB_of_mem_Jr hx) aTop).symm.trans hab
  change (eb.symm (throughEquiv x (isPB_of_mem_Jr hx) (et k))).val =
    Challenge.pos (Challenge.botHalf x).1 b
  rw [het, hthrough]
  exact (HalfDiagonal.pos_orderIsoOfFin_symm (Challenge.botHalf x).1
    (botHalf_mem_hr hx).1 bBot).symm

theorem exists_repG_of_mem_Jr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    ∃ g : Challenge.Sym r, Challenge.RepG r x g :=
  ⟨extractedSym hx, repG_extractedSym hx⟩

/-- Every coordinate is tested by a genuine through block, so RepG determines the permutation. -/
theorem repG_unique_of_mem_Jr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r)
    (p q : Challenge.Sym r) (hp : Challenge.RepG r x p) (hq : Challenge.RepG r x q) : p = q := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro k
  apply Fin.ext
  obtain ⟨a, ha, hk⟩ := HalfDiagonal.exists_mem_pos_eq (Challenge.topHalf x).1
    (topHalf_mem_hr hx).1 k
  obtain ⟨b, hab⟩ := Sum.isRight_iff.mp ((mem_topFree_iff x a).mp ha)
  exact (hp k a b hab hk).trans (hq k a b hab hk).symm

/-- The frozen gCoord choice is an actual representing permutation, not an existence assumption. -/
theorem repG_gCoord_of_mem_Jr {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r) :
    Challenge.RepG r x (Challenge.gCoord r x) := by
  classical
  have hex := exists_repG_of_mem_Jr hx
  rw [Challenge.gCoord, dite_eq_left hex]
  exact hex.choose_spec

theorem gCoord_eq_of_repG {D : Challenge.Fam} {n r : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n r)
    (p : Challenge.Sym r) (hp : Challenge.RepG r x p) : Challenge.gCoord r x = p :=
  repG_unique_of_mem_Jr hx _ p (repG_gCoord_of_mem_Jr hx) hp

#print axioms CodexPaper5.DiagramExtraction.isPB_of_mem_Jr
#print axioms CodexPaper5.DiagramExtraction.throughEquiv_apply
#print axioms CodexPaper5.DiagramExtraction.top_bot_free_card
#print axioms CodexPaper5.DiagramExtraction.topHalf_mem_hr
#print axioms CodexPaper5.DiagramExtraction.botHalf_mem_hr
#print axioms CodexPaper5.DiagramExtraction.repG_extractedSym
#print axioms CodexPaper5.DiagramExtraction.exists_repG_of_mem_Jr
#print axioms CodexPaper5.DiagramExtraction.repG_unique_of_mem_Jr
#print axioms CodexPaper5.DiagramExtraction.repG_gCoord_of_mem_Jr
#print axioms CodexPaper5.DiagramExtraction.gCoord_eq_of_repG

end CodexPaper5.DiagramExtraction
