import Research.Backfill.Paper7.MomentB4RowCertificateBridge

/-! Uncompiled source-only reduction helpers. These concern the labelled B1
moment-count row, not graph isomorphisms or D2 canonical representatives.
No numerical total, candidate table, sorted-domain coverage or orbit weight
is assumed. Every permutation transports the actual bounded q fibre. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7MomentCounts Paper7MomentDP Paper7MomentCertificate
open scoped BigOperators Classical

def boundedQFibrePermEquiv {n : ℕ} (z : Fin n → ℕ) (Q : ℕ)
    (e : Equiv.Perm (Fin n)) : BoundedQFibre z Q ≃ BoundedQFibre (z ∘ e) Q where
  toFun q := ⟨(fun i => q.val (e i)), by
    change (∑ i, (q.val (e i)).val) = Q
    exact (e.bijective.sum_comp (fun i => (q.val i).val)).trans q.property⟩
  invFun q := ⟨(fun i => ⟨(q.val (e.symm i)).val, by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        (q.val (e.symm i)).isLt⟩), by
    change (∑ i, (q.val (e.symm i)).val) = Q
    exact (e.symm.bijective.sum_comp (fun i => (q.val i).val)).trans q.property⟩
  left_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (q.val (e (e.symm i))).val = (q.val i).val
    rw [e.apply_symm_apply]
  right_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (q.val (e.symm (e i))).val = (q.val i).val
    rw [e.symm_apply_apply]
#print axioms Paper7MomentReduction.boundedQFibrePermEquiv

theorem boundedQDP_comp_perm {n : ℕ} (z : Fin n → ℕ) (Q : ℕ)
    (e : Equiv.Perm (Fin n)) : boundedQDP n (z ∘ e) Q = boundedQDP n z Q := by
  rw [boundedQDP_eq_card, boundedQDP_eq_card]
  unfold boundedQFibreCard
  exact Nat.card_congr (boundedQFibrePermEquiv z Q e).symm
#print axioms Paper7MomentReduction.boundedQDP_comp_perm

theorem b4Theta_comp_perm (z : Fin 4 → ℕ) (Q : ℕ)
    (e : Equiv.Perm (Fin 4)) : b4Theta (z ∘ e) Q = b4Theta z Q := by
  have hsum : (∑ i, (z ∘ e) i) = ∑ i, z i := e.bijective.sum_comp z
  have hsq : (∑ i, ((z ∘ e) i : ℤ)^2) = ∑ i, (z i : ℤ)^2 :=
    e.bijective.sum_comp (fun i => (z i : ℤ)^2)
  simp only [b4Theta, hsum, hsq]
#print axioms Paper7MomentReduction.b4Theta_comp_perm

theorem b4CatalogRowAccept_comp_perm (z : Fin 4 → ℕ) (Q : ℕ)
    (e : Equiv.Perm (Fin 4)) :
    B4CatalogRowAccept (z ∘ e) Q ↔ B4CatalogRowAccept z Q := by
  have hsum : (∑ i, (z ∘ e) i) = ∑ i, z i := e.bijective.sum_comp z
  simp only [B4CatalogRowAccept, hsum, b4Theta_comp_perm]
#print axioms Paper7MomentReduction.b4CatalogRowAccept_comp_perm

/-- Any permutation has exactly the same row weight. A future sorted-row sum
must still multiply by the actual number of distinct ordered permutations. -/
theorem b4RowContribution_comp_perm (z : Fin 4 → ℕ)
    (e : Equiv.Perm (Fin 4)) : b4RowContribution (z ∘ e) = b4RowContribution z := by
  unfold b4RowContribution
  apply Finset.sum_congr rfl
  intro Q _
  rw [b4CatalogRowAccept_comp_perm, boundedQDP_comp_perm]
#print axioms Paper7MomentReduction.b4RowContribution_comp_perm

/-- One fixed feature can select at most one total Q. This does not count
feature witnesses: distinct features still require a proved disjointness gate. -/
theorem b4_fixed_feature_Q_unique (z : Fin 4 → ℕ) (M : ℤ) (Q R : ℕ)
    (hQ : M = b4Theta z Q + 4) (hR : M = b4Theta z R + 4) : Q = R := by
  unfold b4Theta at hQ hR
  omega
#print axioms Paper7MomentReduction.b4_fixed_feature_Q_unique

theorem b4_catalog_fourth_bounds (S M : ℤ) (h : (S, M) ∈ b4FeatureCatalog) :
    M ≤ 1272 ∧ M % 12 = 0 := by
  simp only [b4FeatureCatalog, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at h
  rcases h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num
#print axioms Paper7MomentReduction.b4_catalog_fourth_bounds

/-- All accepted Q values of one row belong to the same residue class mod 6.
Within Fin19 this leaves at most four possible values; no feature is counted
as an additional assignment. -/
theorem b4CatalogRowAccept_Q_mod_six (z : Fin 4 → ℕ) (Q R : ℕ)
    (hQ : B4CatalogRowAccept z Q) (hR : B4CatalogRowAccept z R) :
    Q % 6 = R % 6 := by
  rcases hQ with ⟨_, _, _, ⟨SQ, MQ⟩, hmQ, heQ, _, _⟩
  rcases hR with ⟨_, _, _, ⟨SR, MR⟩, hmR, heR, _, _⟩
  have hdQ := (b4_catalog_fourth_bounds SQ MQ hmQ).2
  have hdR := (b4_catalog_fourth_bounds SR MR hmR).2
  unfold b4Theta at heQ heR
  omega
#print axioms Paper7MomentReduction.b4CatalogRowAccept_Q_mod_six

/-- A symbolic family rejection eliminates all Q simultaneously. -/
theorem b4RowContribution_zero_of_large_base (z : Fin 4 → ℕ)
    (hbase : 1272 < b4Theta z 0 + 4) : b4RowContribution z = 0 := by
  unfold b4RowContribution
  apply Finset.sum_eq_zero
  intro Q _
  apply ite_eq_right
  rintro ⟨_hQ, _hp, _hn, ⟨S, M⟩, hm, heq, _hlo, _hhi⟩
  have hub := (b4_catalog_fourth_bounds S M hm).1
  unfold b4Theta at hbase heq
  have hnonneg : (0 : ℤ) ≤ (Q.val : ℤ) := Int.natCast_nonneg _
  omega
#print axioms Paper7MomentReduction.b4RowContribution_zero_of_large_base

/-- Small comparison pilot: nineteen catalogue branches, symbolic Q.
No fin_cases Q and no per-Q DP table are needed for this rejected row. -/
theorem b4RowContribution_00180 :
    b4RowContribution (![0, 0, 18, 0] : Fin 4 → ℕ) = 0 := by
  unfold b4RowContribution
  apply Finset.sum_eq_zero
  intro Q _
  apply ite_eq_right
  rintro ⟨_hQ, _hp, _hn, ⟨S, M⟩, hm, heq, hlo, _hhi⟩
  norm_num [b4Theta, Fin.sum_univ_four] at heq
  norm_num [Fin.sum_univ_four] at hlo
  simp only [b4FeatureCatalog, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals omega
#print axioms Paper7MomentReduction.b4RowContribution_00180

end Paper7MomentReduction
