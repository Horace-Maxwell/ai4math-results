import Research.Backfill.Paper7.MomentB4Type112QRecovery

/-! SOURCE ONLY. Exact elimination of the Q loop by the original catalogue.
Injectivity of the catalogue's fourth-moment projection prevents duplicate
counting; the graph fibre weight and all original guards are retained.
The final expression keeps the true diagonal/off-diagonal multiplicities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_feature_catalog_snd_injective :
    ∀ a ∈ b4FeatureCatalog, ∀ b ∈ b4FeatureCatalog,
      a.2 = b.2 → a = b := by
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.b4_feature_catalog_snd_injective

theorem type112_recovered_catalog_unique (S t D Q : ℕ) (a b : ℤ × ℤ)
    (ha : a ∈ b4FeatureCatalog) (hb : b ∈ b4FeatureCatalog)
    (hga : b4Type112RecoveredGuard S t D a)
    (hgb : b4Type112RecoveredGuard S t D b)
    (hQa : Q = b4Type112RecoveredQ S t D a.2)
    (hQb : Q = b4Type112RecoveredQ S t D b.2) : a = b := by
  have hA := (type112_residual_recovery_iff S t D Q a.2).mpr
    ⟨hga.1,hga.2.1,hQa⟩
  have hB := (type112_residual_recovery_iff S t D Q b.2).mpr
    ⟨hgb.1,hgb.2.1,hQb⟩
  apply b4_feature_catalog_snd_injective a ha b hb
  omega
#print axioms Paper7MomentCanonicalNumeric.type112_recovered_catalog_unique

theorem finset_exists_unique_indicator_sum {A : Type} [DecidableEq A]
    (s : Finset A) (p : A → Prop) [DecidablePred p] (w : ℕ)
    (huniq : ∀ a ∈ s, ∀ b ∈ s, p a → p b → a = b) :
    (if ∃ a ∈ s, p a then w else 0) = ∑ a ∈ s, if p a then w else 0 := by
  by_cases h : ∃ a ∈ s, p a
  · rcases h with ⟨a,ha,hpa⟩
    rw [ite_eq_left ⟨a,ha,hpa⟩]
    symm
    calc
      _ = if p a then w else 0 := by
        apply Finset.sum_eq_single a
        · intro b hb hne
          apply ite_eq_right
          intro hpb
          exact hne (huniq b hb a ha hpb hpa)
        · intro hnot
          exact False.elim (hnot ha)
      _ = w := ite_eq_left hpa
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    exact fun hp => h ⟨a,ha,hp⟩
#print axioms Paper7MomentCanonicalNumeric.finset_exists_unique_indicator_sum

def b4Type112RecoveredBlock (z : Fin 38) (t : Fin 19) (u : Fin 38) : ℕ :=
  ∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm then
      b4Type112PlainWeight z.val t.val u.val
        (b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type112RecoveredBlock

theorem type112_block_eq_recovered_catalog_sum
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (hzu : z ≤ u) :
    b4Type112Block z t u = b4Type112RecoveredBlock z t u := by
  unfold b4Type112Block b4Type112RecoveredBlock
  calc
    _ = ∑ Q : Fin 19, ∑ sm ∈ b4FeatureCatalog,
        if b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm ∧
          Q.val = b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2 then
            b4Type112PlainWeight z.val t.val u.val Q.val else 0 := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [type112_accept_iff_recovered_catalog z t u Q hzu,type112_row_weight_eq_plain]
      have hs := finset_exists_unique_indicator_sum b4FeatureCatalog
        (fun sm => b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm ∧
          Q.val = b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2)
        (b4Type112PlainWeight z.val t.val u.val Q.val) (by
          intro a ha b hb hpa hpb
          exact type112_recovered_catalog_unique (z.val+u.val) t.val (u.val-z.val)
            Q.val a b ha hb hpa.1 hpb.1 hpa.2 hpb.2)
      by_cases he : ∃ sm ∈ b4FeatureCatalog,
          b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm ∧
          Q.val = b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2
      · simpa only [ite_eq_left he] using hs
      · simpa only [ite_eq_right he] using hs
    _ = ∑ sm ∈ b4FeatureCatalog, ∑ Q : Fin 19,
        if b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm ∧
          Q.val = b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2 then
            b4Type112PlainWeight z.val t.val u.val Q.val else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sm _
      exact type112_recovered_fibre_sum (z.val+u.val) t.val (u.val-z.val) sm
        (b4Type112PlainWeight z.val t.val u.val)
#print axioms Paper7MomentCanonicalNumeric.type112_block_eq_recovered_catalog_sum

theorem b4_type112_finite_sum_eq_recovered_catalog_triangle :
    b4Type112FiniteSum =
      ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 13),
        ((∑ z ∈ (Finset.univ : Finset (Fin 38)).filter
          (fun z => 2*z.val+2*t.val ≤ 37), b4Type112RecoveredBlock z t z) +
        2*(∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
          (fun u => z < u ∧ z.val+2*t.val+u.val ≤ 37), b4Type112RecoveredBlock z t u)) := by
  rw [b4_type112_finite_sum_eq_thirteen_middle_slices]
  apply Finset.sum_congr rfl
  intro t _
  rw [b4_type112_middle_sum_eq_triangular_budget]
  apply congrArg₂ (fun a b : ℕ => a+2*b)
  · apply Finset.sum_congr rfl
    intro z _
    exact type112_block_eq_recovered_catalog_sum z t z le_rfl
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro u hu
    have hzu := (Finset.mem_filter.mp hu).2.1
    exact type112_block_eq_recovered_catalog_sum z t u hzu.le
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_recovered_catalog_triangle

end Paper7MomentCanonicalNumeric
