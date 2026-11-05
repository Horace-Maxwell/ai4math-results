import Research.Backfill.Paper7.MomentB6SlicedWeights

/-! Source-only finite histogram transport and exact ordered-position counting.
No capacity table or numerical moment total occurs in these generic lemmas. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

def finiteValueHistogram (f : α → β) (b : β) : ℕ :=
  Fintype.card {a : α // f a = b}
#print axioms Paper7MomentCounts.finiteValueHistogram

theorem finiteValueHistogram_sum_weight (f : α → β) (w : β → ℕ) :
    (∑ b, finiteValueHistogram f b * w b) = ∑ a, w (f a) := by
  have h := Fintype.sum_fiberwise' f w
  simpa [finiteValueHistogram] using h
#print axioms Paper7MomentCounts.finiteValueHistogram_sum_weight

theorem finiteValueHistogram_total (f : α → β) :
    (∑ b, finiteValueHistogram f b) = Fintype.card α := by
  simpa using finiteValueHistogram_sum_weight f (fun _ => 1)
#print axioms Paper7MomentCounts.finiteValueHistogram_total

omit [Fintype β] in
theorem finiteValueHistogram_comp_perm (f : α → β) (e : Equiv.Perm α) :
    finiteValueHistogram (f ∘ e) = finiteValueHistogram f := by
  funext b
  apply Fintype.card_congr
  exact {
    toFun := fun a => ⟨e a.val,a.property⟩
    invFun := fun a => ⟨e.symm a.val,by simpa using a.property⟩
    left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
    right_inv := fun a => Subtype.ext (e.apply_symm_apply a.val) }
#print axioms Paper7MomentCounts.finiteValueHistogram_comp_perm

omit [Fintype β] in
theorem finiteValueHistogram_exists_perm (f g : α → β)
    (h : finiteValueHistogram g = finiteValueHistogram f) :
    ∃ e : Equiv.Perm α, g = f ∘ e := by
  let ef : ∀ b, {a : α // g a = b} ≃ {a : α // f a = b} :=
    fun b => Fintype.equivOfCardEq (congrFun h b)
  refine ⟨Equiv.ofFiberEquiv ef,?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map ef a).symm
#print axioms Paper7MomentCounts.finiteValueHistogram_exists_perm

abbrev FiniteHistogramFiber (f : α → β) :=
  {g : α → β // finiteValueHistogram g = finiteValueHistogram f}
#print axioms Paper7MomentCounts.FiniteHistogramFiber

abbrev FiniteHistogramStabilizer (f : α → β) :=
  {e : Equiv.Perm α // f ∘ e = f}
#print axioms Paper7MomentCounts.FiniteHistogramStabilizer

def finiteHistogramStabilizerEquiv (f : α → β) :
    (∀ b : β, Equiv.Perm {a : α // f a = b}) ≃ FiniteHistogramStabilizer f where
  toFun es := ⟨Equiv.ofFiberEquiv es,by
    funext a
    exact Equiv.ofFiberEquiv_map es a⟩
  invFun e b := {
    toFun := fun a => ⟨e.val a.val,(congrFun e.property a.val).trans a.property⟩
    invFun := fun a => ⟨e.val.symm a.val,by
      have h := congrFun e.property (e.val.symm a.val)
      change f (e.val (e.val.symm a.val)) = f (e.val.symm a.val) at h
      rw [e.val.apply_symm_apply] at h
      exact h.symm.trans a.property⟩
    left_inv := fun a => Subtype.ext (e.val.symm_apply_apply a.val)
    right_inv := fun a => Subtype.ext (e.val.apply_symm_apply a.val) }
  left_inv es := by
    funext b
    apply Equiv.ext
    rintro ⟨a,ha⟩
    apply Subtype.ext
    cases ha
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rfl
#print axioms Paper7MomentCounts.finiteHistogramStabilizerEquiv

theorem finiteHistogramStabilizer_card (f : α → β) :
    Fintype.card (FiniteHistogramStabilizer f) =
      ∏ b, (finiteValueHistogram f b).factorial := by
  rw [Fintype.card_congr (finiteHistogramStabilizerEquiv f).symm,Fintype.card_pi]
  simp only [Fintype.card_perm,finiteValueHistogram]
#print axioms Paper7MomentCounts.finiteHistogramStabilizer_card

def finiteHistogramChosenPerm (f : α → β) (g : FiniteHistogramFiber f) : Equiv.Perm α :=
  Classical.choose (finiteValueHistogram_exists_perm f g.val g.property)
#print axioms Paper7MomentCounts.finiteHistogramChosenPerm

omit [Fintype β] in
theorem finiteHistogramChosenPerm_spec (f : α → β) (g : FiniteHistogramFiber f) :
    g.val = f ∘ finiteHistogramChosenPerm f g :=
  Classical.choose_spec (finiteValueHistogram_exists_perm f g.val g.property)
#print axioms Paper7MomentCounts.finiteHistogramChosenPerm_spec

def finiteHistogramPermBase (f : α → β) (e : Equiv.Perm α) : FiniteHistogramFiber f :=
  ⟨f ∘ e,finiteValueHistogram_comp_perm f e⟩
#print axioms Paper7MomentCounts.finiteHistogramPermBase

def finiteHistogramPermResidual (f : α → β) (e : Equiv.Perm α) : FiniteHistogramStabilizer f :=
  ⟨(finiteHistogramChosenPerm f (finiteHistogramPermBase f e)).symm.trans e,by
    funext a
    have h := congrFun (finiteHistogramChosenPerm_spec f (finiteHistogramPermBase f e))
      ((finiteHistogramChosenPerm f (finiteHistogramPermBase f e)).symm a)
    simpa [finiteHistogramPermBase] using h⟩
#print axioms Paper7MomentCounts.finiteHistogramPermResidual

def finiteHistogramPermAssemble (f : α → β)
    (g : FiniteHistogramFiber f) (e : FiniteHistogramStabilizer f) : Equiv.Perm α :=
  (finiteHistogramChosenPerm f g).trans e.val
#print axioms Paper7MomentCounts.finiteHistogramPermAssemble

omit [Fintype β] in
theorem finiteHistogramPermBase_assemble (f : α → β)
    (g : FiniteHistogramFiber f) (e : FiniteHistogramStabilizer f) :
    finiteHistogramPermBase f (finiteHistogramPermAssemble f g e) = g := by
  apply Subtype.ext
  funext a
  have hp := congrFun e.property (finiteHistogramChosenPerm f g a)
  have hg := congrFun (finiteHistogramChosenPerm_spec f g) a
  change f (e.val (finiteHistogramChosenPerm f g a)) = g.val a
  exact hp.trans hg.symm
#print axioms Paper7MomentCounts.finiteHistogramPermBase_assemble

def finiteHistogramPermProductEquiv (f : α → β) :
    Equiv.Perm α ≃ FiniteHistogramFiber f × FiniteHistogramStabilizer f where
  toFun e := (finiteHistogramPermBase f e,finiteHistogramPermResidual f e)
  invFun p := finiteHistogramPermAssemble f p.1 p.2
  left_inv e := by
    apply Equiv.ext
    intro a
    simp [finiteHistogramPermAssemble,finiteHistogramPermResidual]
  right_inv p := by
    apply Prod.ext
    · exact finiteHistogramPermBase_assemble f p.1 p.2
    · apply Subtype.ext
      change (finiteHistogramChosenPerm f
        (finiteHistogramPermBase f (finiteHistogramPermAssemble f p.1 p.2))).symm.trans
        (finiteHistogramPermAssemble f p.1 p.2) = p.2.val
      rw [finiteHistogramPermBase_assemble]
      apply Equiv.ext
      intro a
      simp [finiteHistogramPermAssemble]
#print axioms Paper7MomentCounts.finiteHistogramPermProductEquiv

theorem finiteHistogramFiber_card_factorial (f : α → β) :
    Fintype.card (FiniteHistogramFiber f) * (∏ b, (finiteValueHistogram f b).factorial) =
      (Fintype.card α).factorial := by
  have h := Fintype.card_congr (finiteHistogramPermProductEquiv f)
  rw [Fintype.card_perm,Fintype.card_prod,finiteHistogramStabilizer_card] at h
  exact h.symm
#print axioms Paper7MomentCounts.finiteHistogramFiber_card_factorial

end Paper7MomentCounts
