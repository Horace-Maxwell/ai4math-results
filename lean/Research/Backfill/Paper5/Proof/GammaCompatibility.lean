import Research.Backfill.Paper5.Proof.HalfDiagonal
import Research.Backfill.Paper5.Proof.InvolutionEndpoints

set_option autoImplicit false

namespace CodexPaper5.GammaCompatibility

open BackfillPaper5 Function

/-- The actual half-diagram involution, as a genuine permutation. -/
def halfPerm {D : Challenge.Fam} {n r : ℕ} {h : Challenge.Half n}
    (hh : Challenge.IsHalf D n r h) : Equiv.Perm (Fin n) where
  toFun := h.2
  invFun := h.2
  left_inv := hh.2.1
  right_inv := hh.2.1

/-- Removing the redundant inequality inside GammaEdge leaves exactly the moving-edge graph. -/
theorem gammaGraph_eq_movingGraph {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) :
    Challenge.gammaGraph l i = InvolutionEndpoints.movingGraph (halfPerm hl) (halfPerm hi) := by
  ext a b
  change
    (a ≠ b ∧
      (((l.2 a = b ∧ b ≠ a) ∨ (i.2 a = b ∧ b ≠ a)) ∨
        ((l.2 b = a ∧ a ≠ b) ∨ (i.2 b = a ∧ a ≠ b)))) ↔
    (a ≠ b ∧ ((l.2 a = b ∨ i.2 a = b) ∨ (l.2 b = a ∨ i.2 b = a)))
  have hba : a ≠ b → b ≠ a := fun h => Ne.symm h
  tauto

theorem gammaGraph_swap {n : ℕ} (l i : Challenge.Half n) :
    Challenge.gammaGraph l i = Challenge.gammaGraph i l := by
  ext a b
  simp only [Challenge.gammaGraph, SimpleGraph.fromRel_adj, Challenge.GammaEdge]
  tauto

theorem reverse_reachable {n : ℕ} {l i : Challenge.Half n} {a b : Fin n}
    (h : (Challenge.gammaGraph l i).Reachable a b) :
    (Challenge.gammaGraph i l).Reachable b a := by
  rw [← gammaGraph_swap l i]
  exact h.symm

/-- Cross-colour fixed-endpoint uniqueness is instantiated on the actual frozen gamma graph. -/
theorem endpoint_unique {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) {a b c : Fin n}
    (ha : a ∈ l.1) (hb : b ∈ i.1) (hc : c ∈ i.1)
    (hab : (Challenge.gammaGraph l i).Reachable a b)
    (hac : (Challenge.gammaGraph l i).Reachable a c) : b = c := by
  rw [gammaGraph_eq_movingGraph hl hi] at hab hac
  exact InvolutionEndpoints.endpoints_unique (halfPerm hl) (halfPerm hi)
    hl.2.1 hi.2.1 (hl.2.2.1 a ha) (hi.2.2.1 b hb) (hi.2.2.1 c hc) hab hac

/-- Select the actual reachable target supplied by compatibility, rather than an abstract matching. -/
noncomputable def matchMap {n : ℕ} {l i : Challenge.Half n}
    (h : Challenge.Compat l i) (a : l.1) : i.1 :=
  ⟨(h a.val a.property).choose, (h a.val a.property).choose_spec.1⟩

theorem matchMap_reachable {n : ℕ} {l i : Challenge.Half n}
    (h : Challenge.Compat l i) (a : l.1) :
    (Challenge.gammaGraph l i).Reachable a.val (matchMap h a).val :=
  (h a.val a.property).choose_spec.2

theorem matchMap_injective {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : Injective (matchMap h) := by
  intro a b hab
  apply Subtype.ext
  have hba : (Challenge.gammaGraph i l).Reachable (matchMap h a).val b.val := by
    rw [hab]
    exact reverse_reachable (matchMap_reachable h b)
  exact endpoint_unique hi hl (matchMap h a).property a.property b.property
    (reverse_reachable (matchMap_reachable h a)) hba

theorem matchMap_bijective {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : Bijective (matchMap h) := by
  apply (Fintype.bijective_iff_injective_and_card (matchMap h)).mpr
  refine ⟨matchMap_injective hl hi h, ?_⟩
  simp only [Fintype.card_coe, hl.1, hi.1]

noncomputable def matchEquiv {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : l.1 ≃ i.1 :=
  Equiv.ofBijective (matchMap h) (matchMap_bijective hl hi h)

theorem matchEquiv_reachable {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) (a : l.1) :
    (Challenge.gammaGraph l i).Reachable a.val (matchEquiv hl hi h a).val :=
  matchMap_reachable h a

theorem compat_symm {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : Challenge.Compat i l := by
  intro b hb
  obtain ⟨a, ha⟩ := (matchEquiv hl hi h).surjective ⟨b, hb⟩
  refine ⟨a.val, a.property, ?_⟩
  have hr := reverse_reachable (matchEquiv_reachable hl hi h a)
  rw [ha] at hr
  exact hr

/-- The true endpoint matching written in the actual increasing free-point coordinates. -/
noncomputable def matchingPerm {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : Equiv.Perm (Fin r) :=
  (((l.1.orderIsoOfFin hl.1).toEquiv).trans (matchEquiv hl hi h)).trans
    (i.1.orderIsoOfFin hi.1).toEquiv.symm

noncomputable def matchingSym {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) : Challenge.Sym r :=
  MulOpposite.op (matchingPerm hl hi h)

theorem repP_matchingSym {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) :
    Challenge.RepP r l i (matchingSym hl hi h) := by
  intro k a b ha hb hk hr
  let aL : l.1 := ⟨a, ha⟩
  let bI : i.1 := ⟨b, hb⟩
  let eL := l.1.orderIsoOfFin hl.1
  let eI := i.1.orderIsoOfFin hi.1
  have hindex : eL.symm aL = k := by
    apply Fin.ext
    exact (HalfDiagonal.pos_orderIsoOfFin_symm l.1 hl.1 aL).symm.trans hk
  have hsource : eL k = aL := by rw [← hindex, eL.apply_symm_apply]
  have htarget : matchEquiv hl hi h aL = bI := by
    apply Subtype.ext
    exact endpoint_unique hl hi ha (matchEquiv hl hi h aL).property hb
      (matchEquiv_reachable hl hi h aL) hr
  change (eI.symm (matchEquiv hl hi h (eL k))).val = Challenge.pos i.1 b
  rw [hsource, htarget]
  exact (HalfDiagonal.pos_orderIsoOfFin_symm i.1 hi.1 bI).symm

theorem exists_repP {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) :
    ∃ p : Challenge.Sym r, Challenge.RepP r l i p :=
  ⟨matchingSym hl hi h, repP_matchingSym hl hi h⟩

theorem repP_unique {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (h : Challenge.Compat l i) (p q : Challenge.Sym r)
    (hp : Challenge.RepP r l i p) (hq : Challenge.RepP r l i q) : p = q := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro k
  apply Fin.ext
  obtain ⟨a, ha, hk⟩ := HalfDiagonal.exists_mem_pos_eq l.1 hl.1 k
  obtain ⟨b, hb, hr⟩ := h a ha
  exact (hp k a b ha hb hk hr).trans (hq k a b ha hb hk hr).symm

theorem repP_pSand {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) :
    Challenge.RepP r l i (Challenge.pSand r l i) := by
  classical
  have hex := exists_repP hl hi h
  rw [Challenge.pSand, dite_eq_left hex]
  exact hex.choose_spec

/-- Reversing the actual paths represents the inverse permutation, in the frozen opposite group. -/
theorem repP_inv {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (p : Challenge.Sym r) (hp : Challenge.RepP r l i p) : Challenge.RepP r i l p⁻¹ := by
  intro k b a hb ha hk hr
  let j := (l.1.orderIsoOfFin hl.1).symm ⟨a, ha⟩
  have hj : Challenge.pos l.1 a = j.val :=
    HalfDiagonal.pos_orderIsoOfFin_symm l.1 hl.1 ⟨a, ha⟩
  have hperm : (MulOpposite.unop p) j = k := by
    apply Fin.ext
    exact (hp j a b ha hb hj (reverse_reachable hr)).trans hk
  have hinv : (MulOpposite.unop p).symm k = j := by
    rw [← hperm, (MulOpposite.unop p).symm_apply_apply]
  change ((MulOpposite.unop p).symm k).val = Challenge.pos l.1 a
  exact (congrArg Fin.val hinv).trans hj.symm

theorem pSand_reverse {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (h : Challenge.Compat l i) :
    Challenge.pSand r i l = (Challenge.pSand r l i)⁻¹ := by
  exact repP_unique hi (compat_symm hl hi h) _ _
    (repP_pSand hi hl (compat_symm hl hi h))
    (repP_inv hl _ (repP_pSand hl hi h))

/-- All four clauses of the frozen proposition, on actual legal half-diagrams. -/
theorem check_Prop31c : Challenge.Prop31c := by
  intro D n r l hl i hi
  exact ⟨HalfDiagonal.compat_of_same_free rfl,
    HalfDiagonal.pSand_eq_one_of_same_free hl hl rfl,
    ⟨compat_symm hl hi, compat_symm hi hl⟩, pSand_reverse hl hi⟩

#print axioms CodexPaper5.GammaCompatibility.gammaGraph_eq_movingGraph
#print axioms CodexPaper5.GammaCompatibility.gammaGraph_swap
#print axioms CodexPaper5.GammaCompatibility.endpoint_unique
#print axioms CodexPaper5.GammaCompatibility.matchMap_bijective
#print axioms CodexPaper5.GammaCompatibility.compat_symm
#print axioms CodexPaper5.GammaCompatibility.repP_matchingSym
#print axioms CodexPaper5.GammaCompatibility.exists_repP
#print axioms CodexPaper5.GammaCompatibility.repP_unique
#print axioms CodexPaper5.GammaCompatibility.repP_pSand
#print axioms CodexPaper5.GammaCompatibility.repP_inv
#print axioms CodexPaper5.GammaCompatibility.pSand_reverse
#print axioms CodexPaper5.GammaCompatibility.check_Prop31c

end CodexPaper5.GammaCompatibility
