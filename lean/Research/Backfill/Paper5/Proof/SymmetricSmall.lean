import Research.Backfill.Paper5.Proof.CMTransport
import Research.Backfill.Paper5.Proof.CycleRemarks

set_option autoImplicit false

namespace CodexPaper5.SymmetricSmall

open BackfillPaper5 Function
open scoped BigOperators

/-- Enumerate the opposite group through the computable permutation enumeration. -/
local instance instFintypeSym (r : ℕ) : Fintype (Challenge.Sym r) :=
  Fintype.ofEquiv (Equiv.Perm (Fin r)) MulOpposite.opEquiv

/-- On a subsingleton magma the identity is an actual complete mapping. -/
theorem hasCM_subsingleton (G : Type*) [Mul G] [Subsingleton G] : Challenge.HasCM G := by
  refine ⟨id, Function.bijective_id, ?_⟩
  constructor
  · intro x y _h
    exact Subsingleton.elim x y
  · intro y
    exact ⟨y, Subsingleton.elim _ _⟩

theorem perm_zero_hasCM : Challenge.HasCM (Equiv.Perm (Fin 0)) :=
  hasCM_subsingleton _

theorem perm_one_hasCM : Challenge.HasCM (Equiv.Perm (Fin 1)) :=
  hasCM_subsingleton _

theorem sym_zero_hasCM : Challenge.HasCM (Challenge.Sym 0) :=
  (CMTransport.hasCM_opposite (Equiv.Perm (Fin 0))).mp perm_zero_hasCM

theorem sym_one_hasCM : Challenge.HasCM (Challenge.Sym 1) :=
  (CMTransport.hasCM_opposite (Equiv.Perm (Fin 1))).mp perm_one_hasCM

/-- Any complete mapping forces the sum of an additive parity character to vanish.
The argument reindexes the two actual bijections; it does not enumerate candidate functions. -/
theorem sign_sum_eq_zero_of_cm {G : Type*} [Group G] [Fintype G]
    (s : G → ZMod 2) (hmul : ∀ x y, s (x * y) = s x + s y)
    (h : Challenge.HasCM G) : (∑ x : G, s x) = 0 := by
  classical
  obtain ⟨α, hα, hp⟩ := h
  have hsum : (∑ x : G, s (x * α x)) = ∑ x : G, s x := hp.sum_comp s
  have hzero : (∑ x : G, s (x * α x)) = 0 := by
    calc
      (∑ x : G, s (x * α x)) = ∑ x : G, (s x + s (α x)) :=
        Finset.sum_congr rfl (fun x _ => hmul x (α x))
      _ = (∑ x : G, s x) + ∑ x : G, s (α x) := Finset.sum_add_distrib
      _ = (∑ x : G, s x) + ∑ x : G, s x := by rw [hα.sum_comp s]
      _ = 0 := CharTwo.add_self_eq_zero _
  exact hsum.symm.trans hzero

/-- Only the two actual degree-two group elements are summed. -/
theorem sign_sum_two : (∑ g : Challenge.Sym 2, Challenge.sgn g) = 1 := by
  decide +kernel

/-- Only the six actual degree-three group elements are summed. -/
theorem sign_sum_three : (∑ g : Challenge.Sym 3, Challenge.sgn g) = 1 := by
  decide +kernel

theorem sym_two_noCM : ¬ Challenge.HasCM (Challenge.Sym 2) := by
  intro h
  have hz := sign_sum_eq_zero_of_cm Challenge.sgn CycleRemarks.sgn_mul h
  rw [sign_sum_two] at hz
  exact one_ne_zero hz

theorem sym_three_noCM : ¬ Challenge.HasCM (Challenge.Sym 3) := by
  intro h
  have hz := sign_sum_eq_zero_of_cm Challenge.sgn CycleRemarks.sgn_mul h
  rw [sign_sum_three] at hz
  exact one_ne_zero hz

theorem perm_two_noCM : ¬ Challenge.HasCM (Equiv.Perm (Fin 2)) := by
  intro h
  exact sym_two_noCM ((CMTransport.hasCM_opposite (Equiv.Perm (Fin 2))).mp h)

theorem perm_three_noCM : ¬ Challenge.HasCM (Equiv.Perm (Fin 3)) := by
  intro h
  exact sym_three_noCM ((CMTransport.hasCM_opposite (Equiv.Perm (Fin 3))).mp h)

/- The following four literal arrays come from the existing cm_S4.json certificate.
Rows are actual point images, inverse rows are their computed inverses, and the two
index maps are the certificate and its right-action products. Every required property
of these literals is reproved below by Lean's kernel. No Cayley table is assumed. -/

def s4Rows : Fin 24 → Fin 4 → Fin 4 :=
![
  ![0, 1, 2, 3],
  ![0, 1, 3, 2],
  ![0, 2, 1, 3],
  ![0, 2, 3, 1],
  ![0, 3, 1, 2],
  ![0, 3, 2, 1],
  ![1, 0, 2, 3],
  ![1, 0, 3, 2],
  ![1, 2, 0, 3],
  ![1, 2, 3, 0],
  ![1, 3, 0, 2],
  ![1, 3, 2, 0],
  ![2, 0, 1, 3],
  ![2, 0, 3, 1],
  ![2, 1, 0, 3],
  ![2, 1, 3, 0],
  ![2, 3, 0, 1],
  ![2, 3, 1, 0],
  ![3, 0, 1, 2],
  ![3, 0, 2, 1],
  ![3, 1, 0, 2],
  ![3, 1, 2, 0],
  ![3, 2, 0, 1],
  ![3, 2, 1, 0]]

def s4InverseRows : Fin 24 → Fin 4 → Fin 4 :=
![
  ![0, 1, 2, 3],
  ![0, 1, 3, 2],
  ![0, 2, 1, 3],
  ![0, 3, 1, 2],
  ![0, 2, 3, 1],
  ![0, 3, 2, 1],
  ![1, 0, 2, 3],
  ![1, 0, 3, 2],
  ![2, 0, 1, 3],
  ![3, 0, 1, 2],
  ![2, 0, 3, 1],
  ![3, 0, 2, 1],
  ![1, 2, 0, 3],
  ![1, 3, 0, 2],
  ![2, 1, 0, 3],
  ![3, 1, 0, 2],
  ![2, 3, 0, 1],
  ![3, 2, 0, 1],
  ![1, 2, 3, 0],
  ![1, 3, 2, 0],
  ![2, 1, 3, 0],
  ![3, 1, 2, 0],
  ![2, 3, 1, 0],
  ![3, 2, 1, 0]]

def s4AlphaIndex : Fin 24 → Fin 24 :=
  ![23, 20, 19, 13, 21, 22, 5, 8, 3, 14, 1, 12, 6, 0, 4, 10, 18, 2, 9, 17, 7, 15, 16, 11]

def s4ProductIndex : Fin 24 → Fin 24 :=
  ![23, 21, 22, 17, 18, 20, 19, 15, 16, 7, 8, 4, 14, 13, 10, 5, 9, 11, 0, 2, 12, 1, 6, 3]

private theorem s4_rows_inverse : ∀ (i : Fin 24) (x : Fin 4),
    s4InverseRows i (s4Rows i x) = x ∧ s4Rows i (s4InverseRows i x) = x := by
  decide +kernel

private theorem s4_rows_injective : Injective s4Rows := by
  decide +kernel

private theorem s4_alpha_injective : Injective s4AlphaIndex := by
  decide +kernel

private theorem s4_product_injective : Injective s4ProductIndex := by
  decide +kernel

private theorem s4_rows_product : ∀ (i : Fin 24) (x : Fin 4),
    s4Rows (s4AlphaIndex i) (s4Rows i x) = s4Rows (s4ProductIndex i) x := by
  decide +kernel

/-- The literals define genuine permutations, with both inverse laws checked. -/
def s4Perm (i : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := s4Rows i
  invFun := s4InverseRows i
  left_inv := fun x => (s4_rows_inverse i x).1
  right_inv := fun x => (s4_rows_inverse i x).2

/-- The frozen convention is right action, hence the opposite group here. -/
def s4Enum (i : Fin 24) : Challenge.Sym 4 := MulOpposite.op (s4Perm i)

theorem s4_enum_bijective : Bijective s4Enum := by
  have hi : Injective s4Enum := by
    intro i j hij
    apply s4_rows_injective
    funext x
    exact congrArg (fun g : Challenge.Sym 4 => MulOpposite.unop g x) hij
  have hc : Fintype.card (Challenge.Sym 4) = 24 := by
    calc
      Fintype.card (Challenge.Sym 4) = Fintype.card (Equiv.Perm (Fin 4)) :=
        (Fintype.card_congr
          (MulOpposite.opEquiv : Equiv.Perm (Fin 4) ≃ Challenge.Sym 4)).symm
      _ = 24 := by norm_num [Fintype.card_perm]
  exact (Fintype.bijective_iff_injective_and_card s4Enum).mpr ⟨hi, by simp [hc]⟩

noncomputable def s4Equiv : Fin 24 ≃ Challenge.Sym 4 :=
  Equiv.ofBijective s4Enum s4_enum_bijective

/-- This is equality in the actual permutation group, not a natural-number table relation. -/
theorem s4_product_bridge (i : Fin 24) :
    s4Enum i * s4Enum (s4AlphaIndex i) = s4Enum (s4ProductIndex i) := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro x
  exact s4_rows_product i x

/-- The actual degree-four mapping is the literal index map conjugated by the true enumeration. -/
noncomputable def s4Mapping (g : Challenge.Sym 4) : Challenge.Sym 4 :=
  s4Equiv (s4AlphaIndex (s4Equiv.symm g))

theorem s4Mapping_complete : Challenge.IsCompleteMapping (· * ·) s4Mapping := by
  have ha : Bijective s4AlphaIndex := s4_alpha_injective.bijective_of_finite
  have hb : Bijective s4ProductIndex := s4_product_injective.bijective_of_finite
  constructor
  · exact s4Equiv.bijective.comp (ha.comp s4Equiv.symm.bijective)
  · have hformula : ∀ g : Challenge.Sym 4,
        g * s4Mapping g = s4Equiv (s4ProductIndex (s4Equiv.symm g)) := by
      intro g
      obtain ⟨i, rfl⟩ := s4Equiv.surjective g
      simp only [s4Mapping, s4Equiv.symm_apply_apply]
      exact s4_product_bridge i
    change Bijective (fun g : Challenge.Sym 4 => g * s4Mapping g)
    rw [funext hformula]
    exact s4Equiv.bijective.comp (hb.comp s4Equiv.symm.bijective)

theorem sym_four_hasCM : Challenge.HasCM (Challenge.Sym 4) :=
  ⟨s4Mapping, s4Mapping_complete⟩

theorem perm_four_hasCM : Challenge.HasCM (Equiv.Perm (Fin 4)) :=
  (CMTransport.hasCM_opposite (Equiv.Perm (Fin 4))).mpr sym_four_hasCM

#print axioms CodexPaper5.SymmetricSmall.hasCM_subsingleton
#print axioms CodexPaper5.SymmetricSmall.sign_sum_eq_zero_of_cm
#print axioms CodexPaper5.SymmetricSmall.sign_sum_two
#print axioms CodexPaper5.SymmetricSmall.sign_sum_three
#print axioms CodexPaper5.SymmetricSmall.s4_enum_bijective
#print axioms CodexPaper5.SymmetricSmall.s4_product_bridge
#print axioms CodexPaper5.SymmetricSmall.s4Mapping_complete
#print axioms CodexPaper5.SymmetricSmall.perm_zero_hasCM
#print axioms CodexPaper5.SymmetricSmall.perm_one_hasCM
#print axioms CodexPaper5.SymmetricSmall.perm_two_noCM
#print axioms CodexPaper5.SymmetricSmall.perm_three_noCM
#print axioms CodexPaper5.SymmetricSmall.perm_four_hasCM
#print axioms CodexPaper5.SymmetricSmall.sym_zero_hasCM
#print axioms CodexPaper5.SymmetricSmall.sym_one_hasCM
#print axioms CodexPaper5.SymmetricSmall.sym_two_noCM
#print axioms CodexPaper5.SymmetricSmall.sym_three_noCM
#print axioms CodexPaper5.SymmetricSmall.sym_four_hasCM

end CodexPaper5.SymmetricSmall
