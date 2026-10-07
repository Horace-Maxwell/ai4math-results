import Research.Backfill.Paper5.Proof.BrauerJoinSplice

set_option autoImplicit false

namespace CodexPaper5.BrauerJoin

open BackfillPaper5

/-- Equal free-set cardinalities give equal actual difference cardinalities. -/
theorem difference_card_eq {n r : ℕ} (F F' : Finset (Fin n))
    (hF : F.card = r) (hF' : F'.card = r) :
    (F \ F').card = (F' \ F).card := by
  exact Finset.card_sdiff_eq_card_sdiff_iff.mpr (hF.trans hF'.symm)

theorem union_card {n r : ℕ} (F F' : Finset (Fin n)) (hF' : F'.card = r) :
    (F ∪ F').card = r + (F \ F').card := by
  have h := Finset.card_sdiff_add_card F F'
  rw [hF'] at h
  omega

theorem complement_card {n r : ℕ} (F F' : Finset (Fin n))
    (hF' : F'.card = r) :
    ((F ∪ F')ᶜ).card = n - (r + (F \ F').card) := by
  rw [Finset.card_compl, Fintype.card_fin, union_card F F' hF']

theorem bridge_card_bound {n r : ℕ} (F F' : Finset (Fin n))
    (hF' : F'.card = r) (hbound : r + 2 * (F \ F').card ≤ n) :
    (F \ F').card ≤ ((F ∪ F')ᶜ).card := by
  rw [complement_card F F' hF']
  omega

/-- The chosen bridge set consumes a second copy of the difference cardinality. -/
theorem residual_card {n r : ℕ} (F F' Z : Finset (Fin n))
    (hF' : F'.card = r) (hZ : Z ⊆ (F ∪ F')ᶜ)
    (hZcard : Z.card = (F \ F').card)
    (hbound : r + 2 * (F \ F').card ≤ n) :
    (((F ∪ F')ᶜ) \ Z).card = n - r - 2 * (F \ F').card := by
  rw [Finset.card_sdiff_of_subset hZ, complement_card F F' hF', hZcard]
  omega

theorem residual_even {n r : ℕ} (F F' Z : Finset (Fin n))
    (hF' : F'.card = r) (hZ : Z ⊆ (F ∪ F')ᶜ)
    (hZcard : Z.card = (F \ F').card)
    (hbound : r + 2 * (F \ F').card ≤ n) (hpar : n % 2 = r % 2) :
    Even (Fintype.card ↥(((F ∪ F')ᶜ) \ Z)) := by
  rw [Fintype.card_coe, residual_card F F' Z hF' hZ hZcard hbound, Nat.even_iff]
  omega

/-- This is a partition of all nonfree points, including an empty residual block. -/
theorem nonfree_blocks {n : ℕ} (F G Z : Finset (Fin n))
    (hZ : Z ⊆ (F ∪ G)ᶜ) (a : Fin n) :
    a ∉ F ↔ a ∈ G \ F ∨ a ∈ Z ∨ a ∈ ((F ∪ G)ᶜ) \ Z := by
  constructor
  · intro haF
    by_cases haG : a ∈ G
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨haG, haF⟩)
    · have haC : a ∈ (F ∪ G)ᶜ := by
        apply Finset.mem_compl.mpr
        intro ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact haF ha
        · exact haG ha
      by_cases haZ : a ∈ Z
      · exact Or.inr (Or.inl haZ)
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨haC, haZ⟩))
  · intro ha
    rcases ha with haY | haZ | haR
    · exact (Finset.mem_sdiff.mp haY).2
    · intro haF
      exact (Finset.mem_compl.mp (hZ haZ)) (Finset.mem_union.mpr (Or.inl haF))
    · intro haF
      exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp haR).1)
        (Finset.mem_union.mpr (Or.inl haF))

/-- Actual two-edge paths: the second half supplies X→Z and the first Z→Y. -/
theorem bridge_compat {n : ℕ} (F F' Z R : Finset (Fin n))
    (eXY : ↥(F \ F') ≃ ↥(F' \ F)) (eXZ : ↥(F \ F') ≃ ↥Z)
    (q : ↥R → ↥R) (hXZ : Disjoint (F \ F') Z) (hYZ : Disjoint (F' \ F) Z) :
    Challenge.Compat
      (F, BrauerJoinSplice.spliceMatching (F' \ F) Z R (eXY.symm.trans eXZ) q)
      (F', BrauerJoinSplice.spliceMatching (F \ F') Z R eXZ q) := by
  let eYZ : ↥(F' \ F) ≃ ↥Z := eXY.symm.trans eXZ
  let v : Challenge.Half n := (F, BrauerJoinSplice.spliceMatching (F' \ F) Z R eYZ q)
  let w : Challenge.Half n := (F', BrauerJoinSplice.spliceMatching (F \ F') Z R eXZ q)
  change Challenge.Compat v w
  intro a ha
  change a ∈ F at ha
  by_cases haF' : a ∈ F'
  · exact ⟨a, haF', SimpleGraph.Reachable.rfl⟩
  · let x : ↥(F \ F') := ⟨a, Finset.mem_sdiff.mpr ⟨ha, haF'⟩⟩
    let z : ↥Z := eXZ x
    let y : ↥(F' \ F) := eXY x
    have haz : a ≠ z.val := by
      intro heq
      have haZ : a ∈ Z := by
        rw [heq]
        exact z.property
      exact Finset.disjoint_left.mp hXZ x.property haZ
    have hzy : z.val ≠ y.val := by
      intro heq
      have hyZ : y.val ∈ Z := by
        rw [← heq]
        exact z.property
      exact Finset.disjoint_left.mp hYZ y.property hyZ
    have hey : eYZ.symm z = y := by
      change eXY (eXZ.symm (eXZ x)) = eXY x
      rw [eXZ.symm_apply_apply]
    have hw : w.2 a = z.val := by
      exact BrauerJoinSplice.spliceMatching_on_A (F \ F') Z R eXZ q x.property
    have hv : v.2 z.val = y.val := by
      calc
        v.2 z.val = (eYZ.symm ⟨z.val, z.property⟩).val :=
          BrauerJoinSplice.spliceMatching_on_Z (F' \ F) Z R eYZ q hYZ z.property
        _ = y.val := congrArg Subtype.val hey
    have hadj : (Challenge.gammaGraph v w).Adj a z.val := by
      change a ≠ z.val ∧
        (Challenge.GammaEdge v w a z.val ∨ Challenge.GammaEdge v w z.val a)
      exact ⟨haz, Or.inl (Or.inr ⟨hw, Ne.symm haz⟩)⟩
    have hzadjy : (Challenge.gammaGraph v w).Adj z.val y.val := by
      change z.val ≠ y.val ∧
        (Challenge.GammaEdge v w z.val y.val ∨ Challenge.GammaEdge v w y.val z.val)
      exact ⟨hzy, Or.inl (Or.inl ⟨hv, Ne.symm hzy⟩)⟩
    exact ⟨y.val, (Finset.mem_sdiff.mp y.property).1,
      hadj.reachable.trans hzadjy.reachable⟩

/-- Full joining construction; it also permits equal free sets and every empty boundary. -/
theorem exists_join_halves (n r : ℕ) (_hle : r ≤ n) (hpar : n % 2 = r % 2)
    (F F' : Finset (Fin n)) (hF : F.card = r) (hF' : F'.card = r)
    (hbound : r + 2 * (F \ F').card ≤ n) :
    ∃ v ∈ Challenge.Hr Challenge.Fam.B n r,
      ∃ w ∈ Challenge.Hr Challenge.Fam.B n r,
        v.1 = F ∧ w.1 = F' ∧ Challenge.Compat v w := by
  classical
  let X : Finset (Fin n) := F \ F'
  let Y : Finset (Fin n) := F' \ F
  let C : Finset (Fin n) := (F ∪ F')ᶜ
  have hXYcard : X.card = Y.card := difference_card_eq F F' hF hF'
  have hXCcard : X.card ≤ C.card := bridge_card_bound F F' hF' hbound
  obtain ⟨Z, hZ, hZcard⟩ := Finset.exists_subset_card_eq hXCcard
  let R : Finset (Fin n) := C \ Z
  have hReven : Even (Fintype.card ↥R) :=
    residual_even F F' Z hF' hZ hZcard hbound hpar
  obtain ⟨q, hqI, hqN⟩ :=
    DiagramRanksOccurring.exists_fixedPointFree_involution ↥R hReven
  let eXY : ↥X ≃ ↥Y := Finset.equivOfCardEq hXYcard
  let eXZ : ↥X ≃ ↥Z := Finset.equivOfCardEq hZcard.symm
  let eYZ : ↥Y ≃ ↥Z := eXY.symm.trans eXZ
  have hXZ : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro a haX haZ
    exact (Finset.mem_compl.mp (hZ haZ))
      (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp haX).1))
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro a haY haZ
    exact (Finset.mem_compl.mp (hZ haZ))
      (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp haY).1))
  have hXR : Disjoint X R := by
    apply Finset.disjoint_left.mpr
    intro a haX haR
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp haR).1)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp haX).1))
  have hYR : Disjoint Y R := by
    apply Finset.disjoint_left.mpr
    intro a haY haR
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp haR).1)
      (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp haY).1))
  have hZR : Disjoint Z R := by
    apply Finset.disjoint_left.mpr
    intro a haZ haR
    exact (Finset.mem_sdiff.mp haR).2 haZ
  have hFY : Disjoint F Y := by
    apply Finset.disjoint_left.mpr
    intro a haF haY
    exact (Finset.mem_sdiff.mp haY).2 haF
  have hFZ : Disjoint F Z := by
    apply Finset.disjoint_left.mpr
    intro a haF haZ
    exact (Finset.mem_compl.mp (hZ haZ)) (Finset.mem_union.mpr (Or.inl haF))
  have hFR : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro a haF haR
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp haR).1)
      (Finset.mem_union.mpr (Or.inl haF))
  have hF'X : Disjoint F' X := by
    apply Finset.disjoint_left.mpr
    intro a haF' haX
    exact (Finset.mem_sdiff.mp haX).2 haF'
  have hF'Z : Disjoint F' Z := by
    apply Finset.disjoint_left.mpr
    intro a haF' haZ
    exact (Finset.mem_compl.mp (hZ haZ)) (Finset.mem_union.mpr (Or.inr haF'))
  have hF'R : Disjoint F' R := by
    apply Finset.disjoint_left.mpr
    intro a haF' haR
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp haR).1)
      (Finset.mem_union.mpr (Or.inr haF'))
  have hcoverV : ∀ a : Fin n, a ∉ F → a ∈ Y ∨ a ∈ Z ∨ a ∈ R := by
    intro a ha
    exact (nonfree_blocks F F' Z hZ a).mp ha
  have hZflip : Z ⊆ (F' ∪ F)ᶜ := by
    intro a haZ
    apply Finset.mem_compl.mpr
    intro ha
    exact (Finset.mem_compl.mp (hZ haZ))
      (by simpa only [Finset.union_comm] using ha)
  have hcoverW : ∀ a : Fin n, a ∉ F' → a ∈ X ∨ a ∈ Z ∨ a ∈ R := by
    intro a ha
    simpa only [Finset.union_comm] using (nonfree_blocks F' F Z hZflip a).mp ha
  let v : Challenge.Half n := (F, BrauerJoinSplice.spliceMatching Y Z R eYZ q)
  let w : Challenge.Half n := (F', BrauerJoinSplice.spliceMatching X Z R eXZ q)
  have hv : v ∈ Challenge.Hr Challenge.Fam.B n r :=
    BrauerJoinSplice.spliceHalf_mem_hr F Y Z R eYZ q hF hYZ hYR hZR
      hFY hFZ hFR hcoverV hqI hqN
  have hw : w ∈ Challenge.Hr Challenge.Fam.B n r :=
    BrauerJoinSplice.spliceHalf_mem_hr F' X Z R eXZ q hF' hXZ hXR hZR
      hF'X hF'Z hF'R hcoverW hqI hqN
  exact ⟨v, hv, w, hw, rfl, rfl, bridge_compat F F' Z R eXY eXZ q hXZ hYZ⟩

theorem check_Lemma53 : Challenge.Lemma53 := by
  intro n r hle hpar F F' hF hF' _hne hbound
  exact exists_join_halves n r hle hpar F F' hF hF' hbound

#print axioms CodexPaper5.BrauerJoin.difference_card_eq
#print axioms CodexPaper5.BrauerJoin.union_card
#print axioms CodexPaper5.BrauerJoin.complement_card
#print axioms CodexPaper5.BrauerJoin.bridge_card_bound
#print axioms CodexPaper5.BrauerJoin.residual_card
#print axioms CodexPaper5.BrauerJoin.residual_even
#print axioms CodexPaper5.BrauerJoin.nonfree_blocks
#print axioms CodexPaper5.BrauerJoin.bridge_compat
#print axioms CodexPaper5.BrauerJoin.exists_join_halves
#print axioms CodexPaper5.BrauerJoin.check_Lemma53

end CodexPaper5.BrauerJoin
