import Research.Backfill.Paper8.Proof.Spec.Roots
import Research.Backfill.Paper8.Proof.Spec.Eigen
import Research.Backfill.Paper8.Proof.Spec.Kernel
import Research.Backfill.Paper8.Proof.Spec.Count

/-!
# Paper 8: `Secular_monic` and Lemma 3.1 (the spectrum of `T(a)`)

Final statements of agent `spec`, each of the exact type of the frozen statement in
`Research.Backfill.Paper8.Challenge`. The proofs combine `Research.Backfill.Paper8.Proof.Spec.Secular` (the polynomial `R`),
`Research.Backfill.Paper8.Proof.Spec.Roots` (location of the roots of `R`), `Research.Backfill.Paper8.Proof.Spec.Eigen` (eigenvectors),
`Research.Backfill.Paper8.Proof.Spec.Kernel` (the kernel) and `Research.Backfill.Paper8.Proof.Spec.Count` (the list and number of eigenvalues).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial Matrix

namespace P8Spec

theorem check_Secular_monic : BackfillPaper8.Challenge.Secular_monic :=
  fun m hm => secular_monic m hm

#print axioms check_Secular_monic

theorem check_Lemma_3_1_i : BackfillPaper8.Challenge.Lemma_3_1_i := by
  intro k a hk
  obtain ⟨t, hmono, hroots, hlo, hhi, hpos, hR⟩ := roots_spec (branchMS a) (branchMS_ne_zero a hk)
  refine ⟨t, hmono, hroots, hlo, hhi, hpos, ?_⟩
  intro j θ hθ
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have h := (hpos j).1
    rw [← hθ] at h
    norm_num at h
  have hne : ∀ i, θ ^ 2 ≠ (a i : ℝ) := by
    intro i
    rw [hθ]
    exact (hpos j).2 (a i) ((mem_Bset_branchMS a (a i)).2 ⟨i, rfl⟩)
  have hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1 :=
    (aeval_secular_eq_zero_iff a (θ ^ 2) hne).1 (by rw [hθ]; exact hR j)
  exact eigenspace_eq_span_secVec a θ hθ0 hne hF

#print axioms check_Lemma_3_1_i

theorem check_Lemma_3_1_iii : BackfillPaper8.Challenge.Lemma_3_1_iii :=
  fun _ a _ => lemma_3_1_iii a

#print axioms check_Lemma_3_1_iii

theorem check_Lemma_3_1_ii : BackfillPaper8.Challenge.Lemma_3_1_ii := by
  intro k a _ b hb hb1 _ θ hθb
  have hex := (mem_Bset_branchMS a b).1 hb
  have hθ : θ ≠ 0 := by
    rintro rfl
    have h1 : (b : ℝ) = 0 := by
      rw [← hθb]
      ring
    have h2 : b = 0 := by exact_mod_cast h1
    omega
  refine ⟨fun x => (P8Basic.mem_eigenspace_iff _ _ _).trans
    (mulVec_eq_smul_sqrt_iff a b hex θ hθ hθb x), ?_⟩
  rw [finrank_eigenspace_sqrt a b hex θ hθ hθb, kb_branchMS]

#print axioms check_Lemma_3_1_ii

theorem check_Lemma_3_1_iv : BackfillPaper8.Challenge.Lemma_3_1_iv :=
  fun _ a hk => ⟨fun θ => isEigenvalue_iff_char a θ, ncard_eigenvalues a hk⟩

#print axioms check_Lemma_3_1_iv

/-- The statement `Lemma_U1` of version 2 of the statement file (body copied from the draft): every
real root `t` of `R` satisfies `t ≤ b* + k`. -/
theorem lemma_U1 : ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ t : ℝ,
    aeval t (secular (branchMS a)) = 0 → t ≤ (bstar (branchMS a) : ℝ) + k := by
  intro k a _ t ht
  refine not_lt.1 (fun h => ?_)
  have hpos := aeval_secular_pos (branchMS a) t (by rw [card_branchMS]; exact h)
  rw [ht] at hpos
  exact lt_irrefl _ hpos

#print axioms lemma_U1

theorem check_Lemma_U1 : BackfillPaper8.Challenge.Lemma_U1 := lemma_U1

#print axioms check_Lemma_U1

end P8Spec
