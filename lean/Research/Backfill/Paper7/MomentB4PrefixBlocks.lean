import Research.Backfill.Paper7.BoundedTuplePrefixEquiv
import Research.Backfill.Paper7.MomentB4RowCertificateBridge

/-! Full structural indexing of the original bounded z-domain. Prefix blocks
are disjoint finite sums, obtained from equivalences, without reference to a
candidate file or its row count. All nineteen Q values remain in each row. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCertificate
open Paper7Budget Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev B4PrefixIndex :=
  Σ a : Fin 38, Σ b : Fin (37-a.val+1),
    Σ c : Fin (37-a.val-b.val+1), Fin (37-a.val-b.val-c.val+1)
#print axioms Paper7MomentCertificate.B4PrefixIndex

def b4TupleIndexEquiv : BoundedTuple 4 37 ≃ B4PrefixIndex :=
  (boundedTupleHeadEquiv 3 37).trans (Equiv.sigmaCongrRight fun a =>
    (boundedTupleHeadEquiv 2 (37-a.val)).trans (Equiv.sigmaCongrRight fun b =>
      (boundedTupleHeadEquiv 1 (37-a.val-b.val)).trans (Equiv.sigmaCongrRight fun c =>
        boundedTupleOneEquivFin (37-a.val-b.val-c.val))))
#print axioms Paper7MomentCertificate.b4TupleIndexEquiv

def b4IndexZ (r : B4PrefixIndex) : Fin 4 → ℕ :=
  Fin.cons r.1.val (Fin.cons r.2.1.val
    (Fin.cons r.2.2.1.val (fun _ : Fin 1 => r.2.2.2.val)))
#print axioms Paper7MomentCertificate.b4IndexZ

theorem b4Index_decode (r : B4PrefixIndex) :
    (b4TupleIndexEquiv.symm r).val = b4IndexZ r := rfl
#print axioms Paper7MomentCertificate.b4Index_decode

theorem b4Index_encode (z : BoundedTuple 4 37) :
    b4IndexZ (b4TupleIndexEquiv z) = z.val := by
  calc
    b4IndexZ (b4TupleIndexEquiv z) =
        (b4TupleIndexEquiv.symm (b4TupleIndexEquiv z)).val :=
      (b4Index_decode (b4TupleIndexEquiv z)).symm
    _ = z.val := congrArg Subtype.val (b4TupleIndexEquiv.symm_apply_apply z)
#print axioms Paper7MomentCertificate.b4Index_encode

theorem b4IndexZ_injective : Function.Injective b4IndexZ := by
  intro r s h
  apply b4TupleIndexEquiv.symm.injective
  apply Subtype.ext
  simpa only [b4Index_decode] using h
#print axioms Paper7MomentCertificate.b4IndexZ_injective

/-- Every original bounded z-vector has exactly one four-coordinate index. -/
theorem b4Index_complete_unique (z : BoundedTuple 4 37) :
    ∃! r : B4PrefixIndex, b4IndexZ r = z.val := by
  refine ⟨b4TupleIndexEquiv z, b4Index_encode z, ?_⟩
  intro r hr
  apply b4IndexZ_injective
  exact hr.trans (b4Index_encode z).symm
#print axioms Paper7MomentCertificate.b4Index_complete_unique

theorem b4Index_sum_bound (r : B4PrefixIndex) : (∑ i, b4IndexZ r i) ≤ 37 := by
  have h := (b4TupleIndexEquiv.symm r).property
  simpa only [b4Index_decode] using h
#print axioms Paper7MomentCertificate.b4Index_sum_bound

/-- The Q index is unchanged: all Fin19 values are present for every z. -/
def b4FullIndexEquiv : (BoundedTuple 4 37 × Fin 19) ≃ (B4PrefixIndex × Fin 19) :=
  Equiv.prodCongr b4TupleIndexEquiv (Equiv.refl (Fin 19))
#print axioms Paper7MomentCertificate.b4FullIndexEquiv

theorem b4FullIndex_Q (z : BoundedTuple 4 37) (Q : Fin 19) :
    (b4FullIndexEquiv (z, Q)).2 = Q := rfl
#print axioms Paper7MomentCertificate.b4FullIndex_Q

theorem candB1_b4_ncard_eq_prefix_index_sum :
    (CandB1 4 41).ncard = ∑ r : B4PrefixIndex, b4RowContribution (b4IndexZ r) := by
  rw [candB1_b4_ncard_eq_row_contributions]
  calc
    (∑ z : BoundedTuple 4 37, b4RowContribution z.val) =
        ∑ r : B4PrefixIndex, b4RowContribution (b4TupleIndexEquiv.symm r).val :=
      (b4TupleIndexEquiv.symm.sum_comp (fun z => b4RowContribution z.val)).symm
    _ = _ := by simp only [b4Index_decode]
#print axioms Paper7MomentCertificate.candB1_b4_ncard_eq_prefix_index_sum

/-- One block fixes exactly the first two z coordinates. It contains every
legal remaining c,d pair, including zeros, each exactly once. -/
def b4PrefixBlock (a : Fin 38) (b : Fin (37-a.val+1)) : ℕ :=
  ∑ c : Fin (37-a.val-b.val+1), ∑ d : Fin (37-a.val-b.val-c.val+1),
    b4RowContribution (b4IndexZ ⟨a, b, c, d⟩)
#print axioms Paper7MomentCertificate.b4PrefixBlock

/-- Complete block assembly for the original set. No candidate-file coverage
claim, omitted-row list, numerical block sum or global total is assumed. -/
theorem candB1_b4_ncard_eq_prefix_blocks :
    (CandB1 4 41).ncard = ∑ a : Fin 38, ∑ b : Fin (37-a.val+1), b4PrefixBlock a b := by
  simpa only [Fintype.sum_sigma, b4PrefixBlock] using
    candB1_b4_ncard_eq_prefix_index_sum
#print axioms Paper7MomentCertificate.candB1_b4_ncard_eq_prefix_blocks

end Paper7MomentCertificate
