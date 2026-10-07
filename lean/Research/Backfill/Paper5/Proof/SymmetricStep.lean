import Research.Backfill.Paper5.Proof.CMTransversal

set_option autoImplicit false

namespace CodexPaper5.SymmetricStep

open BackfillPaper5 Function

/-- Extend an actual permutation by fixing the new point. -/
def optionHom (α : Type*) : Equiv.Perm α →* Equiv.Perm (Option α) where
  toFun := Equiv.optionCongr
  map_one' := Equiv.optionCongr_one
  map_mul' p q := by
    ext x
    cases x <;> rfl

/-- The actual image subgroup of permutations fixing the new point. -/
def optionSubgroup (α : Type*) : Subgroup (Equiv.Perm (Option α)) :=
  (optionHom α).range

/-- The old symmetric group is multiplicatively equivalent to this subgroup. -/
noncomputable def optionEquiv (α : Type*) :
    Equiv.Perm α ≃* optionSubgroup α :=
  MonoidHom.ofInjective (f := optionHom α) Equiv.optionCongr_injective

@[simp]
theorem optionEquiv_apply_coe {α : Type*} (p : Equiv.Perm α) :
    (optionEquiv α p : Equiv.Perm (Option α)) = p.optionCongr := rfl

@[simp]
theorem optionEquiv_symm_coe {α : Type*} (p : optionSubgroup α) :
    ((optionEquiv α).symm p).optionCongr = (p : Equiv.Perm (Option α)) :=
  MonoidHom.apply_ofInjective_symm
    (f := optionHom α) Equiv.optionCongr_injective p

/-- The image really is the point stabilizer; this is proved, not assumed. -/
theorem mem_optionSubgroup_iff {α : Type*} [DecidableEq α]
    (p : Equiv.Perm (Option α)) :
    p ∈ optionSubgroup α ↔ p none = none := by
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · intro hp
    refine ⟨Equiv.removeNone p, ?_⟩
    change (Equiv.removeNone p).optionCongr = p
    rw [map_equiv_removeNone, hp]
    simp
    rfl

/-- Representatives exchange the distinguished point with the selected point. -/
def reps {α : Type*} [DecidableEq α] (i : Option α) :
    Equiv.Perm (Option α) :=
  Equiv.swap none i

/-- Every permutation has its actual unique left factorization. -/
noncomputable def leftEquiv (α : Type*) [DecidableEq α] :
    Option α × optionSubgroup α ≃ Equiv.Perm (Option α) :=
  (Equiv.prodCongr (Equiv.refl (Option α)) (optionEquiv α).symm.toEquiv).trans
    Equiv.Perm.decomposeOption.symm

theorem leftEquiv_apply {α : Type*} [DecidableEq α]
    (i : Option α) (p : optionSubgroup α) :
    leftEquiv α (i, p) = reps i * (p : Equiv.Perm (Option α)) := by
  change Equiv.swap none i * ((optionEquiv α).symm p).optionCongr =
    Equiv.swap none i * (p : Equiv.Perm (Option α))
  rw [optionEquiv_symm_coe]

/-- Invert a left factorization to obtain the actual unique right factorization.
The representatives are involutions; the subgroup need not be normal. -/
noncomputable def rightEquiv (α : Type*) [DecidableEq α] :
    optionSubgroup α × Option α ≃ Equiv.Perm (Option α) :=
  (Equiv.prodComm (optionSubgroup α) (Option α)).trans
    ((Equiv.prodCongr (Equiv.refl (Option α)) (Equiv.inv (optionSubgroup α))).trans
      ((leftEquiv α).trans (Equiv.inv (Equiv.Perm (Option α)))))

theorem rightEquiv_apply {α : Type*} [DecidableEq α]
    (p : optionSubgroup α) (i : Option α) :
    rightEquiv α (p, i) = (p : Equiv.Perm (Option α)) * reps i := by
  change (leftEquiv α (i, p⁻¹))⁻¹ =
    (p : Equiv.Perm (Option α)) * reps i
  rw [leftEquiv_apply]
  simp only [Subgroup.coe_inv, mul_inv_rev, inv_inv, reps, Equiv.swap_inv]

/-- A nontrivial finite rotation has no fixed point, including its wraparound point. -/
theorem rotate_ne {n : ℕ} (hn : 2 ≤ n) (a : Fin n) : finRotate n a ≠ a := by
  cases n with
  | zero => exact a.elim0
  | succ m =>
    intro he
    have hv : (finRotate (m + 1) a : ℕ) = a.val := congrArg Fin.val he
    rw [coe_finRotate] at hv
    by_cases ha : a = Fin.last m
    · rw [ite_eq_left ha] at hv
      have hav : a.val = m := congrArg Fin.val ha
      omega
    · rw [ite_eq_right ha] at hv
      omega

/-- The actual product law for three distinct points in the enlarged set. -/
theorem reps_product {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    reps (some a) * reps (some b) =
      reps (some b) * (Equiv.swap a b).optionCongr := by
  change Equiv.swap none (some a) * Equiv.swap none (some b) =
    Equiv.swap none (some b) * (Equiv.swap a b).optionCongr
  calc
    Equiv.swap none (some a) * Equiv.swap none (some b) =
        Equiv.swap none (some b) * Equiv.swap (some b) (some a) := by
      rw [Equiv.swap_mul_eq_mul_swap]
      simp only [Equiv.swap_inv, Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hab)]
    _ = Equiv.swap none (some b) * (Equiv.swap a b).optionCongr := by
      rw [Equiv.optionCongr_swap, Equiv.swap_comm (some a) (some b)]

/-- Fix the new point and rotate the old points. Both index permutations are this map. -/
def shift (n : ℕ) : Equiv.Perm (Option (Fin n)) :=
  (finRotate n).optionCongr

/-- The coefficients are explicit old-point transpositions, viewed in the image subgroup. -/
noncomputable def coeff (n : ℕ) : Option (Fin n) → optionSubgroup (Fin n)
  | none => 1
  | some a => optionEquiv (Fin n) (Equiv.swap a (finRotate n a))

theorem rep_product (n : ℕ) (hn : 2 ≤ n) (i : Option (Fin n)) :
    reps i * reps (shift n i) =
      reps (shift n i) * (coeff n i : Equiv.Perm (Option (Fin n))) := by
  cases i with
  | none =>
    simp [shift, reps, coeff]
    rfl
  | some a =>
    simpa only [shift, Equiv.optionCongr_apply, Option.map_some, coeff,
      optionEquiv_apply_coe] using
      reps_product a (finRotate n a) (Ne.symm (rotate_ne hn a))

/-- Fully instantiated two-sided transversal data for the successive symmetric groups. -/
noncomputable def data (n : ℕ) (hn : 2 ≤ n) :
    CMTransversal.Data (optionSubgroup (Fin n)) (Option (Fin n)) where
  reps := reps
  left := leftEquiv (Fin n)
  right := rightEquiv (Fin n)
  left_apply := leftEquiv_apply
  right_apply := rightEquiv_apply
  shift := shift n
  productIndex := shift n
  coeff := coeff n
  rep_product := rep_product n hn

/-- Apply the actual transversal construction on the Option model. -/
theorem hasCM_option (n : ℕ) (hn : 2 ≤ n)
    (h : Challenge.HasCM (Equiv.Perm (Fin n))) :
    Challenge.HasCM (Equiv.Perm (Option (Fin n))) := by
  have hK : Challenge.HasCM (optionSubgroup (Fin n)) :=
    (CMTransport.hasCM_iff (optionEquiv (Fin n))).mp h
  exact CMTransversal.hasCM_of_data (data n hn) hK

/-- The complete induction step, with no factorization or ambient-existence hypothesis. -/
theorem hasCM_succ (n : ℕ) (hn : 2 ≤ n)
    (h : Challenge.HasCM (Equiv.Perm (Fin n))) :
    Challenge.HasCM (Equiv.Perm (Fin (n + 1))) := by
  exact (CMTransport.hasCM_iff
    (Equiv.permCongrHom (finSuccEquiv n).symm)).mp (hasCM_option n hn h)

#print axioms CodexPaper5.SymmetricStep.mem_optionSubgroup_iff
#print axioms CodexPaper5.SymmetricStep.leftEquiv_apply
#print axioms CodexPaper5.SymmetricStep.rightEquiv_apply
#print axioms CodexPaper5.SymmetricStep.rotate_ne
#print axioms CodexPaper5.SymmetricStep.reps_product
#print axioms CodexPaper5.SymmetricStep.rep_product
#print axioms CodexPaper5.SymmetricStep.hasCM_option
#print axioms CodexPaper5.SymmetricStep.hasCM_succ

end CodexPaper5.SymmetricStep

