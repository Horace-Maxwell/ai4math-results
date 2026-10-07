import Research.Backfill.Paper5.Proof.DiagramUnits
import Research.Backfill.Paper5.Proof.AssocGraphCompression

set_option autoImplicit false

namespace CodexPaper5.AssocGeometry

open BackfillPaper5 Function

abbrev FourPt (n : ℕ) := Fin 4 × Fin n

/-- Omit one row without selecting any point of Fin n. -/
def rowEmbedding {n : ℕ} (s : Fin 4) : Challenge.SPt n ↪ FourPt n where
  toFun u := (s.succAbove u.1, u.2)
  inj' _u _v h := Prod.ext
    (Fin.succAbove_right_injective (p := s) (congrArg Prod.fst h))
    (congrArg (fun w : FourPt n => w.2) h)

def embed012 {n : ℕ} : Challenge.SPt n ↪ FourPt n := rowEmbedding 3

def embed123 {n : ℕ} : Challenge.SPt n ↪ FourPt n := rowEmbedding 0

def keepLeft {n : ℕ} : Challenge.SPt n ↪ FourPt n := rowEmbedding 1

def keepRight {n : ℕ} : Challenge.SPt n ↪ FourPt n := rowEmbedding 2

def upperEmbedding {n : ℕ} : Challenge.Pt n ↪ Challenge.SPt n :=
  ⟨Challenge.upper, StackGeometry.upper_injective⟩

def lowerEmbedding {n : ℕ} : Challenge.Pt n ↪ Challenge.SPt n :=
  ⟨Challenge.lower, StackGeometry.lower_injective⟩

def xEmbedding {n : ℕ} : Challenge.Pt n ↪ FourPt n :=
  upperEmbedding.trans embed012

def yEmbedding {n : ℕ} : Challenge.Pt n ↪ FourPt n :=
  lowerEmbedding.trans embed012

def zEmbedding {n : ℕ} : Challenge.Pt n ↪ FourPt n :=
  lowerEmbedding.trans embed123

def outerFour {n : ℕ} : Challenge.Pt n → FourPt n
  | .inl a => (0, a)
  | .inr a => (3, a)

/-- The raw singleton matching; this is distinct from the swapping diagram unit. -/
def rawId {n : ℕ} : Challenge.Pt n → Challenge.Pt n := fun p => p

def blockGraph {V : Type*} (x : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun p q => x p = q)

/-- A mapped matching relation, including singleton loop removal. -/
theorem fromRel_edge_map {V W : Type*} (x : V → V) (f : V ↪ W) :
    SimpleGraph.fromRel (fun u v => ∃ p, u = f p ∧ v = f (x p)) =
      (blockGraph x).map f := by
  ext u v
  rw [SimpleGraph.fromRel_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hne, h⟩
    rcases h with ⟨p, hu, hv⟩ | ⟨p, hv, hu⟩
    · refine ⟨p, x p, ?_, hu.symm, hv.symm⟩
      change p ≠ x p ∧ (x p = x p ∨ x (x p) = p)
      refine ⟨?_, Or.inl rfl⟩
      intro h
      exact hne (hu.trans ((congrArg f h).trans hv.symm))
    · refine ⟨x p, p, ?_, hu.symm, hv.symm⟩
      change x p ≠ p ∧ (x (x p) = p ∨ x p = x p)
      refine ⟨?_, Or.inr rfl⟩
      intro h
      exact hne (hu.trans ((congrArg f h).trans hv.symm))
  · rintro ⟨p, q, hpq, hpu, hqv⟩
    change p ≠ q ∧ (x p = q ∨ x q = p) at hpq
    have hne : u ≠ v := by
      intro h
      exact hpq.1 (f.injective (hpu.trans (h.trans hqv.symm)))
    refine ⟨hne, ?_⟩
    rcases hpq.2 with h | h
    · exact Or.inl ⟨p, hpu.symm, hqv.symm.trans (congrArg f h.symm)⟩
    · exact Or.inr ⟨q, hqv.symm, hpu.symm.trans (congrArg f h.symm)⟩

theorem fromRel_or {V : Type*} (r s : V → V → Prop) :
    SimpleGraph.fromRel (fun u v => r u v ∨ s u v) =
      SimpleGraph.fromRel r ⊔ SimpleGraph.fromRel s := by
  ext u v
  simp only [SimpleGraph.fromRel_adj, SimpleGraph.sup_adj]
  tauto

theorem map_sup {V W : Type*} (G H : SimpleGraph V) (f : V → W) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext u v
  simp only [SimpleGraph.map_adj', SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hne, a, b, hab, ha, hb⟩
    rcases hab with hG | hH
    · exact Or.inl ⟨hne, a, b, hG, ha, hb⟩
    · exact Or.inr ⟨hne, a, b, hH, ha, hb⟩
  · rintro (⟨hne, a, b, hab, ha, hb⟩ | ⟨hne, a, b, hab, ha, hb⟩)
    · exact ⟨hne, a, b, Or.inl hab, ha, hb⟩
    · exact ⟨hne, a, b, Or.inr hab, ha, hb⟩

theorem map_bot {V W : Type*} (f : V → W) :
    (⊥ : SimpleGraph V).map f = ⊥ := by
  ext u v
  simp [SimpleGraph.map_adj']

theorem blockGraph_rawId {n : ℕ} : blockGraph (@rawId n) = ⊥ := by
  ext p q
  change (p ≠ q ∧ (p = q ∨ q = p)) ↔ False
  constructor
  · rintro ⟨hne, h⟩
    exact h.elim hne (fun hqp => hne hqp.symm)
  · intro h
    exact h.elim

/-- The actual frozen stack is the union of the two mapped block graphs. -/
theorem stackGraph_eq_sup_map {n : ℕ}
    (x y : Challenge.Pt n → Challenge.Pt n) :
    Challenge.stackGraph x y =
      (blockGraph x).map upperEmbedding ⊔ (blockGraph y).map lowerEmbedding := by
  change SimpleGraph.fromRel (fun u v =>
    (∃ p, u = upperEmbedding p ∧ v = upperEmbedding (x p)) ∨
    (∃ p, u = lowerEmbedding p ∧ v = lowerEmbedding (y p))) = _
  rw [fromRel_or, fromRel_edge_map x upperEmbedding,
    fromRel_edge_map y lowerEmbedding]

theorem raw_right_graph {n : ℕ} (d : Challenge.Pt n → Challenge.Pt n) :
    Challenge.stackGraph d rawId = (blockGraph d).map upperEmbedding := by
  rw [stackGraph_eq_sup_map, blockGraph_rawId, map_bot, sup_bot_eq]

theorem raw_left_graph {n : ℕ} (d : Challenge.Pt n → Challenge.Pt n) :
    Challenge.stackGraph rawId d = (blockGraph d).map lowerEmbedding := by
  rw [stackGraph_eq_sup_map, blockGraph_rawId, map_bot, bot_sup_eq]

/-- Use the existing path projection theorem with the actual identity projection. -/
theorem blockGraph_reachable_iff {V : Type*} (d : V → V)
    (hd : Involutive d) (p q : V) :
    (blockGraph d).Reachable p q ↔ q = p ∨ q = d p := by
  constructor
  · intro h
    apply DiagramUnits.projection_of_reachable (blockGraph d) (fun a => a) d hd ?_ h
    intro a b hab
    change a ≠ b ∧ (d a = b ∨ d b = a) at hab
    rcases hab.2 with hab | hab
    · exact Or.inr hab.symm
    · exact Or.inr ((hd b).symm.trans (congrArg d hab))
  · rintro (rfl | rfl)
    · exact SimpleGraph.Reachable.rfl
    · by_cases hp : p = d p
      · rw [← hp]
      · have hadj : (blockGraph d).Adj p (d p) := by
          exact ⟨hp, Or.inl rfl⟩
        exact hadj.reachable

/-- Actual list-search partners completely describe all outer connectivity. -/
theorem outer_reachable_iff {n : ℕ}
    (x y : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) (p q : Challenge.Pt n) :
    (Challenge.stackGraph x y).Reachable (Challenge.outer p) (Challenge.outer q) ↔
      q = p ∨ q = Challenge.dmul x y p := by
  constructor
  · intro h
    by_cases hqp : q = p
    · exact Or.inl hqp
    · right
      symm
      apply DiagramProduct.dmul_eq_of_partner x y p q hqp h
      intro s hsp hps
      exact StackGeometry.outer_partner_unique hx hy hsp hqp hps h
  · rintro (rfl | rfl)
    · exact SimpleGraph.Reachable.rfl
    · rcases DiagramProduct.dmul_spec x y p with hp | hp
      · rw [hp]
      · exact hp.2

@[simp] theorem keepLeft_upper {n : ℕ} (p : Challenge.Pt n) :
    keepLeft (upperEmbedding p) = embed012 (Challenge.outer p) := by
  cases p <;> rfl

@[simp] theorem keepRight_lower {n : ℕ} (p : Challenge.Pt n) :
    keepRight (lowerEmbedding p) = embed123 (Challenge.outer p) := by
  cases p <;> rfl

@[simp] theorem keepLeft_extra {n : ℕ} (a : Fin n) :
    keepLeft (2, a) = (3, a) := rfl

@[simp] theorem keepRight_extra {n : ℕ} (a : Fin n) :
    keepRight (0, a) = (0, a) := rfl

@[simp] theorem keepLeft_outer {n : ℕ} (p : Challenge.Pt n) :
    keepLeft (Challenge.outer p) = outerFour p := by
  cases p <;> rfl

@[simp] theorem keepRight_outer {n : ℕ} (p : Challenge.Pt n) :
    keepRight (Challenge.outer p) = outerFour p := by
  cases p <;> rfl

theorem embed012_no_extra {n : ℕ} (a : Fin n) (u : Challenge.SPt n) :
    embed012 u ≠ (3, a) := by
  intro h
  have hf := congrArg Prod.fst h
  exact Fin.succAbove_ne (3 : Fin 4) u.1 hf

theorem embed123_no_extra {n : ℕ} (a : Fin n) (u : Challenge.SPt n) :
    embed123 u ≠ (0, a) := by
  intro h
  have hf := congrArg Prod.fst h
  exact Fin.succAbove_ne (0 : Fin 4) u.1 hf

theorem upper_no_extra {n : ℕ} (a : Fin n) (p : Challenge.Pt n) :
    upperEmbedding p ≠ (2, a) := by
  cases p <;> simp [upperEmbedding, Challenge.upper]

theorem lower_no_extra {n : ℕ} (a : Fin n) (p : Challenge.Pt n) :
    lowerEmbedding p ≠ (0, a) := by
  cases p <;> simp [lowerEmbedding, Challenge.lower]

theorem upper_or_extra {n : ℕ} (u : Challenge.SPt n) :
    (∃ p : Challenge.Pt n, u = upperEmbedding p) ∨ ∃ a : Fin n, u = (2, a) := by
  rcases u with ⟨row, a⟩
  fin_cases row
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inl ⟨Sum.inr a, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

theorem lower_or_extra {n : ℕ} (u : Challenge.SPt n) :
    (∃ p : Challenge.Pt n, u = lowerEmbedding p) ∨ ∃ a : Fin n, u = (0, a) := by
  rcases u with ⟨row, a⟩
  fin_cases row
  · exact Or.inr ⟨a, rfl⟩
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inl ⟨Sum.inr a, rfl⟩

/-- The unused retained row is isolated on both sides of the replacement. -/
theorem left_extra_boundary {n : ℕ}
    (x y d : Challenge.Pt n → Challenge.Pt n) (a : Fin n) (u : Challenge.SPt n) :
    ((Challenge.stackGraph x y).map embed012).Reachable
      (keepLeft (2, a)) (keepLeft u) ↔
      (Challenge.stackGraph d rawId).Reachable (2, a) u := by
  rw [raw_right_graph]
  have hG := AssocGraphCompression.reachable_map_outside_iff embed012
    (Challenge.stackGraph x y) (keepLeft (2, a)) (keepLeft u)
    (fun v => by simpa only [keepLeft_extra] using embed012_no_extra a v)
  have hC := AssocGraphCompression.reachable_map_outside_iff upperEmbedding
    (blockGraph d) (2, a) u (upper_no_extra a)
  exact hG.trans (keepLeft.injective.eq_iff.trans hC.symm)

theorem right_extra_boundary {n : ℕ}
    (x y d : Challenge.Pt n → Challenge.Pt n) (a : Fin n) (u : Challenge.SPt n) :
    ((Challenge.stackGraph x y).map embed123).Reachable
      (keepRight (0, a)) (keepRight u) ↔
      (Challenge.stackGraph rawId d).Reachable (0, a) u := by
  rw [raw_left_graph]
  have hG := AssocGraphCompression.reachable_map_outside_iff embed123
    (Challenge.stackGraph x y) (keepRight (0, a)) (keepRight u)
    (fun v => by simpa only [keepRight_extra] using embed123_no_extra a v)
  have hC := AssocGraphCompression.reachable_map_outside_iff lowerEmbedding
    (blockGraph d) (0, a) u (lower_no_extra a)
  exact hG.trans (keepRight.injective.eq_iff.trans hC.symm)

/-- Every retained pair, including the whole unused row, is covered. -/
theorem left_boundary {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) (u v : Challenge.SPt n) :
    ((Challenge.stackGraph x y).map embed012).Reachable (keepLeft u) (keepLeft v) ↔
      (Challenge.stackGraph (Challenge.dmul x y) rawId).Reachable u v := by
  rcases upper_or_extra u with ⟨p, rfl⟩ | ⟨a, rfl⟩
  · rcases upper_or_extra v with ⟨q, rfl⟩ | ⟨a, rfl⟩
    · rw [keepLeft_upper, keepLeft_upper, raw_right_graph,
        AssocGraphCompression.reachable_map_embedding_iff,
        AssocGraphCompression.reachable_map_embedding_iff,
        blockGraph_reachable_iff _ (DiagramProduct.dmul_isPB hx hy)]
      exact outer_reachable_iff x y hx hy p q
    · constructor
      · intro h
        exact ((left_extra_boundary x y (Challenge.dmul x y) a (upperEmbedding p)).mp h.symm).symm
      · intro h
        exact ((left_extra_boundary x y (Challenge.dmul x y) a (upperEmbedding p)).mpr h.symm).symm
  · exact left_extra_boundary x y (Challenge.dmul x y) a v

theorem right_boundary {n : ℕ} (x y : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) (u v : Challenge.SPt n) :
    ((Challenge.stackGraph x y).map embed123).Reachable (keepRight u) (keepRight v) ↔
      (Challenge.stackGraph rawId (Challenge.dmul x y)).Reachable u v := by
  rcases lower_or_extra u with ⟨p, rfl⟩ | ⟨a, rfl⟩
  · rcases lower_or_extra v with ⟨q, rfl⟩ | ⟨a, rfl⟩
    · rw [keepRight_lower, keepRight_lower, raw_left_graph,
        AssocGraphCompression.reachable_map_embedding_iff,
        AssocGraphCompression.reachable_map_embedding_iff,
        blockGraph_reachable_iff _ (DiagramProduct.dmul_isPB hx hy)]
      exact outer_reachable_iff x y hx hy p q
    · constructor
      · intro h
        exact ((right_extra_boundary x y (Challenge.dmul x y) a (lowerEmbedding p)).mp h.symm).symm
      · intro h
        exact ((right_extra_boundary x y (Challenge.dmul x y) a (lowerEmbedding p)).mpr h.symm).symm
  · exact right_extra_boundary x y (Challenge.dmul x y) a v

theorem embed123_upper {n : ℕ} :
    (fun p : Challenge.Pt n => embed123 (upperEmbedding p)) = yEmbedding := by
  funext p
  cases p <;> rfl

theorem keepLeft_lower {n : ℕ} :
    (fun p : Challenge.Pt n => keepLeft (lowerEmbedding p)) = zEmbedding := by
  funext p
  cases p <;> rfl

theorem keepRight_upper {n : ℕ} :
    (fun p : Challenge.Pt n => keepRight (upperEmbedding p)) = xEmbedding := by
  funext p
  cases p <;> rfl

/-- The actual four-row union of the three diagram block graphs. -/
def fourGraph {n : ℕ} (x y z : Challenge.Pt n → Challenge.Pt n) : SimpleGraph (FourPt n) :=
  ((blockGraph x).map xEmbedding ⊔ (blockGraph y).map yEmbedding) ⊔
    (blockGraph z).map zEmbedding

theorem fourGraph_left {n : ℕ} (x y z : Challenge.Pt n → Challenge.Pt n) :
    (Challenge.stackGraph x y).map embed012 ⊔
      (Challenge.stackGraph rawId z).map keepLeft = fourGraph x y z := by
  rw [stackGraph_eq_sup_map x y, raw_left_graph, map_sup,
    SimpleGraph.map_map, SimpleGraph.map_map, SimpleGraph.map_map]
  change ((blockGraph x).map xEmbedding ⊔ (blockGraph y).map yEmbedding) ⊔
    (blockGraph z).map (fun p => keepLeft (lowerEmbedding p)) = fourGraph x y z
  unfold fourGraph
  rw [keepLeft_lower]

theorem fourGraph_right {n : ℕ} (x y z : Challenge.Pt n → Challenge.Pt n) :
    (Challenge.stackGraph y z).map embed123 ⊔
      (Challenge.stackGraph x rawId).map keepRight = fourGraph x y z := by
  rw [stackGraph_eq_sup_map y z, raw_right_graph, map_sup,
    SimpleGraph.map_map, SimpleGraph.map_map, SimpleGraph.map_map]
  change ((blockGraph y).map (fun p => embed123 (upperEmbedding p)) ⊔
    (blockGraph z).map zEmbedding) ⊔
    (blockGraph x).map (fun p => keepRight (upperEmbedding p)) = fourGraph x y z
  rw [embed123_upper, keepRight_upper]
  unfold fourGraph
  ac_rfl

theorem left_bracket_graph {n : ℕ} (d z : Challenge.Pt n → Challenge.Pt n) :
    Challenge.stackGraph d rawId ⊔ Challenge.stackGraph rawId z =
      Challenge.stackGraph d z := by
  rw [raw_right_graph, raw_left_graph, stackGraph_eq_sup_map]

theorem right_bracket_graph {n : ℕ} (x d : Challenge.Pt n → Challenge.Pt n) :
    Challenge.stackGraph rawId d ⊔ Challenge.stackGraph x rawId =
      Challenge.stackGraph x d := by
  rw [raw_right_graph, raw_left_graph, stackGraph_eq_sup_map]
  exact sup_comm _ _

/-- Eliminate either interior row of the same four-row graph. -/
theorem outer_bracket_reachable_iff {n : ℕ}
    (x y z : Challenge.Pt n → Challenge.Pt n)
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) (hz : Challenge.IsPB z)
    (p q : Challenge.Pt n) :
    (Challenge.stackGraph (Challenge.dmul x y) z).Reachable
      (Challenge.outer p) (Challenge.outer q) ↔
    (Challenge.stackGraph x (Challenge.dmul y z)).Reachable
      (Challenge.outer p) (Challenge.outer q) := by
  have hL := AssocGraphCompression.reachable_sup_map_iff keepLeft
    ((Challenge.stackGraph x y).map embed012)
    (Challenge.stackGraph (Challenge.dmul x y) rawId)
    (Challenge.stackGraph rawId z) (left_boundary x y hx hy)
    (Challenge.outer p) (Challenge.outer q)
  have hR := AssocGraphCompression.reachable_sup_map_iff keepRight
    ((Challenge.stackGraph y z).map embed123)
    (Challenge.stackGraph rawId (Challenge.dmul y z))
    (Challenge.stackGraph x rawId) (right_boundary y z hy hz)
    (Challenge.outer p) (Challenge.outer q)
  rw [fourGraph_left, left_bracket_graph, keepLeft_outer, keepLeft_outer] at hL
  rw [fourGraph_right, right_bracket_graph, keepRight_outer, keepRight_outer] at hR
  exact hL.symm.trans hR

theorem check_OuterBracketReachability :
    CodexPaper5.AssociativityStatement.OuterBracketReachability := by
  intro n x y z hx hy hz p q
  exact outer_bracket_reachable_iff x y z hx hy hz p q

end CodexPaper5.AssocGeometry

#print axioms CodexPaper5.AssocGeometry.FourPt
#print axioms CodexPaper5.AssocGeometry.rowEmbedding
#print axioms CodexPaper5.AssocGeometry.embed012
#print axioms CodexPaper5.AssocGeometry.embed123
#print axioms CodexPaper5.AssocGeometry.keepLeft
#print axioms CodexPaper5.AssocGeometry.keepRight
#print axioms CodexPaper5.AssocGeometry.upperEmbedding
#print axioms CodexPaper5.AssocGeometry.lowerEmbedding
#print axioms CodexPaper5.AssocGeometry.xEmbedding
#print axioms CodexPaper5.AssocGeometry.yEmbedding
#print axioms CodexPaper5.AssocGeometry.zEmbedding
#print axioms CodexPaper5.AssocGeometry.outerFour
#print axioms CodexPaper5.AssocGeometry.rawId
#print axioms CodexPaper5.AssocGeometry.blockGraph
#print axioms CodexPaper5.AssocGeometry.fromRel_edge_map
#print axioms CodexPaper5.AssocGeometry.fromRel_or
#print axioms CodexPaper5.AssocGeometry.map_sup
#print axioms CodexPaper5.AssocGeometry.map_bot
#print axioms CodexPaper5.AssocGeometry.blockGraph_rawId
#print axioms CodexPaper5.AssocGeometry.stackGraph_eq_sup_map
#print axioms CodexPaper5.AssocGeometry.raw_right_graph
#print axioms CodexPaper5.AssocGeometry.raw_left_graph
#print axioms CodexPaper5.AssocGeometry.blockGraph_reachable_iff
#print axioms CodexPaper5.AssocGeometry.outer_reachable_iff
#print axioms CodexPaper5.AssocGeometry.keepLeft_upper
#print axioms CodexPaper5.AssocGeometry.keepRight_lower
#print axioms CodexPaper5.AssocGeometry.keepLeft_extra
#print axioms CodexPaper5.AssocGeometry.keepRight_extra
#print axioms CodexPaper5.AssocGeometry.keepLeft_outer
#print axioms CodexPaper5.AssocGeometry.keepRight_outer
#print axioms CodexPaper5.AssocGeometry.embed012_no_extra
#print axioms CodexPaper5.AssocGeometry.embed123_no_extra
#print axioms CodexPaper5.AssocGeometry.upper_no_extra
#print axioms CodexPaper5.AssocGeometry.lower_no_extra
#print axioms CodexPaper5.AssocGeometry.upper_or_extra
#print axioms CodexPaper5.AssocGeometry.lower_or_extra
#print axioms CodexPaper5.AssocGeometry.left_extra_boundary
#print axioms CodexPaper5.AssocGeometry.right_extra_boundary
#print axioms CodexPaper5.AssocGeometry.left_boundary
#print axioms CodexPaper5.AssocGeometry.right_boundary
#print axioms CodexPaper5.AssocGeometry.embed123_upper
#print axioms CodexPaper5.AssocGeometry.keepLeft_lower
#print axioms CodexPaper5.AssocGeometry.keepRight_upper
#print axioms CodexPaper5.AssocGeometry.fourGraph
#print axioms CodexPaper5.AssocGeometry.fourGraph_left
#print axioms CodexPaper5.AssocGeometry.fourGraph_right
#print axioms CodexPaper5.AssocGeometry.left_bracket_graph
#print axioms CodexPaper5.AssocGeometry.right_bracket_graph
#print axioms CodexPaper5.AssocGeometry.outer_bracket_reachable_iff
#print axioms CodexPaper5.AssocGeometry.check_OuterBracketReachability
