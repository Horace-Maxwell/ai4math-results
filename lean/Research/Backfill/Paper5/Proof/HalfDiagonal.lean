import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5.HalfDiagonal

open BackfillPaper5

/-- The frozen counting definition of position agrees with the actual increasing enumeration. -/
theorem pos_orderIsoOfFin {n r : ℕ} (F : Finset (Fin n)) (hF : F.card = r)
    (k : Fin r) : Challenge.pos F (F.orderIsoOfFin hF k).val = k.val := by
  let e := F.orderIsoOfFin hF
  have hcard : (Finset.Iio k).card = (F.filter (fun a => a < (e k).val)).card := by
    apply Finset.card_bij (fun j _ => (e j).val)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨(e j).property, e.strictMono (Finset.mem_Iio.mp hj)⟩
    · intro j _hj q _hq heq
      exact e.injective (Subtype.ext heq)
    · intro a ha
      have haF : a ∈ F := (Finset.mem_filter.mp ha).1
      refine ⟨e.symm ⟨a, haF⟩, ?_, ?_⟩
      · apply Finset.mem_Iio.mpr
        apply e.lt_iff_lt.mp
        rw [e.apply_symm_apply]
        exact Subtype.coe_lt_coe.mp (Finset.mem_filter.mp ha).2
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨a, haF⟩)
  change (F.filter (fun a => a < (e k).val)).card = k.val
  exact hcard.symm.trans (Fin.card_Iio k)

/-- The inverse enumeration recovers the frozen position of any actual free point. -/
theorem pos_orderIsoOfFin_symm {n r : ℕ} (F : Finset (Fin n)) (hF : F.card = r)
    (a : F) : Challenge.pos F a.val = ((F.orderIsoOfFin hF).symm a).val := by
  simpa only [(F.orderIsoOfFin hF).apply_symm_apply] using
    pos_orderIsoOfFin F hF ((F.orderIsoOfFin hF).symm a)

/-- Every rank index is realized by an actual free point; this includes the empty-rank case. -/
theorem exists_mem_pos_eq {n r : ℕ} (F : Finset (Fin n)) (hF : F.card = r)
    (k : Fin r) : ∃ a ∈ F, Challenge.pos F a = k.val := by
  exact ⟨(F.orderIsoOfFin hF k).val, (F.orderIsoOfFin hF k).property,
    pos_orderIsoOfFin F hF k⟩

/-- A point free in both legal halves has no edge in the actual symmetrized gamma graph. -/
theorem gamma_not_adj_of_same_free {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (hF : l.1 = i.1)
    {a : Fin n} (ha : a ∈ l.1) (b : Fin n) : ¬ (Challenge.gammaGraph l i).Adj a b := by
  have hai : a ∈ i.1 := by simpa only [← hF] using ha
  have hla : l.2 a = a := hl.2.2.1 a ha
  have hia : i.2 a = a := hi.2.2.1 a hai
  intro hab
  change a ≠ b ∧ (Challenge.GammaEdge l i a b ∨ Challenge.GammaEdge l i b a) at hab
  rcases hab with ⟨hne, hab | hba⟩
  · rcases hab with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact hne (hla.symm.trans hab)
    · exact hne (hia.symm.trans hab)
  · rcases hba with ⟨hba, _⟩ | ⟨hba, _⟩
    · have h : b = a := by
        calc
          b = l.2 (l.2 b) := (hl.2.1 b).symm
          _ = l.2 a := congrArg l.2 hba
          _ = a := hla
      exact hne h.symm
    · have h : b = a := by
        calc
          b = i.2 (i.2 b) := (hi.2.1 b).symm
          _ = i.2 a := congrArg i.2 hba
          _ = a := hia
      exact hne h.symm

/-- A gamma path starting at such a free point can end only at that same point. -/
theorem eq_of_gamma_reachable_same_free {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (hF : l.1 = i.1)
    {a e : Fin n} (ha : a ∈ l.1) (hp : (Challenge.gammaGraph l i).Reachable a e) : e = a := by
  by_contra hne
  obtain ⟨b, hb⟩ := hp.nonempty_neighborSet_left (Ne.symm hne)
  exact gamma_not_adj_of_same_free hl hi hF ha b hb

/-- Compatibility uses the actual zero-length path at every common free point. -/
theorem compat_of_same_free {n : ℕ} {l i : Challenge.Half n} (hF : l.1 = i.1) :
    Challenge.Compat l i := by
  intro a ha
  exact ⟨a, by simpa only [← hF] using ha, SimpleGraph.Reachable.rfl⟩

/-- The identity permutation really represents all gamma paths between common free points. -/
theorem repP_one_of_same_free {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (hF : l.1 = i.1) : Challenge.RepP r l i 1 := by
  intro k a e ha _he hk hp
  have hea : e = a := eq_of_gamma_reachable_same_free hl hi hF ha hp
  subst e
  change k.val = Challenge.pos i.1 a
  rw [← hF]
  exact hk.symm

/-- A representing permutation is forced to fix every rank index by the actual ordered free points. -/
theorem repP_eq_one_of_same_free {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hF : l.1 = i.1) (p : Challenge.Sym r) (hp : Challenge.RepP r l i p) : p = 1 := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro k
  apply Fin.ext
  change ((MulOpposite.unop p) k).val = k.val
  obtain ⟨a, ha, hk⟩ := exists_mem_pos_eq l.1 hl.1 k
  have hai : a ∈ i.1 := by simpa only [← hF] using ha
  have hpv := hp k a a ha hai hk SimpleGraph.Reachable.rfl
  exact hpv.trans (by simpa only [← hF] using hk)

/-- The frozen choice-based sandwich entry equals the unique identity representative. -/
theorem pSand_eq_one_of_same_free {D : Challenge.Fam} {n r : ℕ}
    {l i : Challenge.Half n} (hl : Challenge.IsHalf D n r l)
    (hi : Challenge.IsHalf D n r i) (hF : l.1 = i.1) : Challenge.pSand r l i = 1 := by
  classical
  have hex : ∃ p, Challenge.RepP r l i p := ⟨1, repP_one_of_same_free hl hi hF⟩
  rw [Challenge.pSand, dite_eq_left hex]
  exact repP_eq_one_of_same_free hl hF hex.choose hex.choose_spec

/-- Full frozen Proposition 3.1(d), for both diagram families and all n,r including zero. -/
theorem check_Prop31d : Challenge.Prop31d := by
  intro D n r l hl i hi hF
  exact ⟨compat_of_same_free hF, pSand_eq_one_of_same_free hl hi hF⟩

#print axioms CodexPaper5.HalfDiagonal.pos_orderIsoOfFin
#print axioms CodexPaper5.HalfDiagonal.pos_orderIsoOfFin_symm
#print axioms CodexPaper5.HalfDiagonal.exists_mem_pos_eq
#print axioms CodexPaper5.HalfDiagonal.gamma_not_adj_of_same_free
#print axioms CodexPaper5.HalfDiagonal.eq_of_gamma_reachable_same_free
#print axioms CodexPaper5.HalfDiagonal.compat_of_same_free
#print axioms CodexPaper5.HalfDiagonal.repP_one_of_same_free
#print axioms CodexPaper5.HalfDiagonal.repP_eq_one_of_same_free
#print axioms CodexPaper5.HalfDiagonal.pSand_eq_one_of_same_free
#print axioms CodexPaper5.HalfDiagonal.check_Prop31d

end CodexPaper5.HalfDiagonal
