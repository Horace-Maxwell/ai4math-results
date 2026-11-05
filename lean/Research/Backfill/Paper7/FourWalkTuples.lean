import Research.Backfill.Paper7.ChallengeV3

/-! Exact four-step closed walks and their three degeneracy classes. The
genuine-cycle class is the actual Walk.IsCycle subtype, not a substituted count. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical

namespace Paper7FourWalks

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

abbrev Quad := {x : V × V × V × V //
  H.Adj x.1 x.2.1 ∧ H.Adj x.2.1 x.2.2.1 ∧
    H.Adj x.2.2.1 x.2.2.2 ∧ H.Adj x.2.2.2 x.1}

def quadWalk (q : Quad H) : H.Walk q.val.1 q.val.1 :=
  Walk.cons q.property.1 (Walk.cons q.property.2.1
    (Walk.cons q.property.2.2.1 (Walk.cons q.property.2.2.2 Walk.nil)))

def quadOfClosed (u : V) (p : H.Walk u u) (hp : p.length = 4) : Quad H := by
  refine ⟨(u, p.getVert 1, p.getVert 2, p.getVert 3), ?_, ?_, ?_, ?_⟩
  · simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact p.adj_getVert_succ (i := 2) (by omega)
  · have hp4 : p.getVert 4 = u := by simpa only [hp] using p.getVert_length
    simpa only [hp4] using p.adj_getVert_succ (i := 3) (by omega)

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
theorem quadWalk_ofClosed (u : V) (p : H.Walk u u) (hp : p.length = 4) :
    quadWalk H (quadOfClosed H u p hp) = p := by
  have hlen : (quadWalk H (quadOfClosed H u p hp)).length = 4 := rfl
  apply Walk.ext_getVert_le_length (hlen.trans hp.symm)
  intro i hi
  have hi4 : i ≤ 4 := hlen ▸ hi
  have hp4 : p.getVert 4 = u := by simpa only [hp] using p.getVert_length
  interval_cases i
  · exact (Walk.getVert_zero p).symm
  · rfl
  · rfl
  · rfl
  · exact hp4.symm

def quadClosedEquiv : Quad H ≃ Σ u : V, {p : H.Walk u u // p.length = 4} where
  toFun q := ⟨q.val.1, ⟨quadWalk H q, rfl⟩⟩
  invFun p := quadOfClosed H p.1 p.2.val p.2.property
  left_inv q := by
    rcases q with ⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩
    rfl
  right_inv p := by
    rcases p with ⟨u, p, hp⟩
    change (Sigma.mk u ⟨quadWalk H (quadOfClosed H u p hp), rfl⟩ :
      Σ x : V, {w : H.Walk x x // w.length = 4}) = Sigma.mk u ⟨p, hp⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact quadWalk_ofClosed H u p hp

def oppositeA (q : Quad H) : Prop := q.val.1 = q.val.2.2.1
def oppositeB (q : Quad H) : Prop := q.val.2.1 = q.val.2.2.2

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
theorem quadWalk_isCycle_iff (q : Quad H) :
    (quadWalk H q).IsCycle ↔ ¬ oppositeA H q ∧ ¬ oppositeB H q := by
  rcases q with ⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩
  have habn := hab.ne
  have hbcn := hbc.ne
  have hcdn := hcd.ne
  have hdan := hda.ne
  simp only [quadWalk, oppositeA, oppositeB,
    Walk.isCycle_iff_isPath_tail_and_le_length, Walk.tail_cons,
    Walk.length_cons, Walk.length_nil]
  norm_num only
  aesop

def quadCycleEquiv : {q : Quad H // ¬ oppositeA H q ∧ ¬ oppositeB H q} ≃
    {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = 4} where
  toFun q := ⟨⟨q.val.val.1, quadWalk H q.val⟩,
    (quadWalk_isCycle_iff H q.val).mpr q.property, rfl⟩
  invFun p := ⟨quadOfClosed H p.val.1 p.val.2 p.property.2,
    (quadWalk_isCycle_iff H _).mp (by rw [quadWalk_ofClosed]; exact p.property.1)⟩
  left_inv q := by
    rcases q with ⟨⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩, hq⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨u, p⟩, hp, hp4⟩
    apply Subtype.ext
    change (Sigma.mk u (quadWalk H (quadOfClosed H u p hp4)) :
      Σ x : V, H.Walk x x) = @Sigma.mk V (fun x => H.Walk x x) u p
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact quadWalk_ofClosed H u p hp4

def oppositeAEquiv : {q : Quad H // oppositeA H q} ≃
    Σ a : V, H.neighborSet a × H.neighborSet a where
  toFun q := ⟨q.val.val.1,
    ⟨⟨q.val.val.2.1, q.val.property.1⟩,
      ⟨q.val.val.2.2.2, q.val.property.2.2.2.symm⟩⟩⟩
  invFun z := ⟨⟨(z.1, z.2.1.val, z.1, z.2.2.val),
    z.2.1.property, z.2.1.property.symm, z.2.2.property, z.2.2.property.symm⟩, rfl⟩
  left_inv q := by
    rcases q with ⟨⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩, heq⟩
    change a = c at heq
    subst c
    rfl
  right_inv z := by rcases z with ⟨a, ⟨⟨b, hab⟩, ⟨d, had⟩⟩⟩; rfl

def oppositeBEquiv : {q : Quad H // oppositeB H q} ≃
    Σ b : V, H.neighborSet b × H.neighborSet b where
  toFun q := ⟨q.val.val.2.1,
    ⟨⟨q.val.val.1, q.val.property.1.symm⟩,
      ⟨q.val.val.2.2.1, q.val.property.2.1⟩⟩⟩
  invFun z := ⟨⟨(z.2.1.val, z.1, z.2.2.val, z.1),
    z.2.1.property.symm, z.2.2.property, z.2.2.property.symm, z.2.1.property⟩, rfl⟩
  left_inv q := by
    rcases q with ⟨⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩, heq⟩
    change b = d at heq
    subst d
    rfl
  right_inv z := by rcases z with ⟨b, ⟨⟨a, hba⟩, ⟨c, hbc⟩⟩⟩; rfl

def oppositeBothEquiv : {q : Quad H // oppositeA H q ∧ oppositeB H q} ≃ H.Dart where
  toFun q := ⟨(q.val.val.1, q.val.val.2.1), q.val.property.1⟩
  invFun d := ⟨⟨(d.fst, d.snd, d.fst, d.snd), d.adj, d.adj.symm,
    d.adj, d.adj.symm⟩, rfl, rfl⟩
  left_inv q := by
    rcases q with ⟨⟨⟨a, b, c, d⟩, hab, hbc, hcd, hda⟩, hA, hB⟩
    change a = c at hA
    change b = d at hB
    subst c
    subst d
    rfl
  right_inv d := by cases d; rfl

omit [DecidableEq V] in
theorem oppositeA_card :
    Fintype.card {q : Quad H // oppositeA H q} = ∑ v : V, (H.degree v) ^ 2 := by
  rw [Fintype.card_congr (oppositeAEquiv H), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.card_prod, SimpleGraph.card_neighborSet_eq_degree, pow_two]

omit [DecidableEq V] in
theorem oppositeB_card :
    Fintype.card {q : Quad H // oppositeB H q} = ∑ v : V, (H.degree v) ^ 2 := by
  rw [Fintype.card_congr (oppositeBEquiv H), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.card_prod, SimpleGraph.card_neighborSet_eq_degree, pow_two]

omit [DecidableEq V] in
theorem oppositeBoth_card :
    Fintype.card {q : Quad H // oppositeA H q ∧ oppositeB H q} =
      2 * H.edgeFinset.card := by
  rw [Fintype.card_congr (oppositeBothEquiv H), H.dart_card_eq_twice_card_edges]

/-- The inclusion-exclusion count is additive, avoiding natural subtraction
at isolated vertices or in the empty graph. -/
theorem quad_card_classification :
    Fintype.card (Quad H) + 2 * H.edgeFinset.card =
      2 * (∑ v : V, (H.degree v) ^ 2) +
        Nat.card {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = 4} := by
  let A : Finset (Quad H) := Finset.univ.filter (oppositeA H)
  let B : Finset (Quad H) := Finset.univ.filter (oppositeB H)
  let C : Finset (Quad H) := Finset.univ.filter (fun q => ¬ oppositeA H q ∧ ¬ oppositeB H q)
  have hA : A.card = ∑ v : V, (H.degree v) ^ 2 := by
    rw [← Fintype.card_subtype]
    exact oppositeA_card H
  have hB : B.card = ∑ v : V, (H.degree v) ^ 2 := by
    rw [← Fintype.card_subtype]
    exact oppositeB_card H
  have hAB : (A ∩ B).card = 2 * H.edgeFinset.card := by
    have hset : A ∩ B = Finset.univ.filter (fun q => oppositeA H q ∧ oppositeB H q) := by
      ext q
      simp [A, B]
    rw [hset, ← Fintype.card_subtype]
    exact oppositeBoth_card H
  have hC : C.card =
      Nat.card {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = 4} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (quadCycleEquiv H)
  have hdis : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro q hq hc
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hq hc
    tauto
  have hcover : (A ∪ B) ∪ C = Finset.univ := by
    ext q
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have htotal : (A ∪ B).card + C.card = Fintype.card (Quad H) := by
    rw [← Finset.card_union_of_disjoint hdis, hcover, Finset.card_univ]
  have hinc := Finset.card_union_add_card_inter A B
  rw [hA, hB, hAB] at hinc
  rw [hC] at htotal
  omega

end Paper7FourWalks

#print axioms Paper7FourWalks.Quad
#print axioms Paper7FourWalks.quadWalk
#print axioms Paper7FourWalks.quadOfClosed
#print axioms Paper7FourWalks.quadWalk_ofClosed
#print axioms Paper7FourWalks.quadClosedEquiv
#print axioms Paper7FourWalks.oppositeA
#print axioms Paper7FourWalks.oppositeB
#print axioms Paper7FourWalks.quadWalk_isCycle_iff
#print axioms Paper7FourWalks.quadCycleEquiv
#print axioms Paper7FourWalks.oppositeAEquiv
#print axioms Paper7FourWalks.oppositeBEquiv
#print axioms Paper7FourWalks.oppositeBothEquiv
#print axioms Paper7FourWalks.oppositeA_card
#print axioms Paper7FourWalks.oppositeB_card
#print axioms Paper7FourWalks.oppositeBoth_card
#print axioms Paper7FourWalks.quad_card_classification
