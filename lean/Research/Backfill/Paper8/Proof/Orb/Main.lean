import Research.Backfill.Paper8.Proof.Orb.Counts
import Research.Backfill.Paper8.Proof.Orb.Switch
import Research.Backfill.Paper8.Proof.Spec.Secular

/-!
# Paper 8: Lemma 3.3 (a)–(e) and Lemma 3.4 (agent `orb`)

Final statements, each of the exact type of the frozen statement in
`Research.Backfill.Paper8.Challenge`. The proofs are in `Research.Backfill.Paper8.Proof.Orb.Poly` (even and odd parts,
`±f(-x)`, the factor `normH f` of `R`), `Research.Backfill.Paper8.Proof.Orb.Secular` (`R(0) ≠ 0`, `R(b) ≠ 0`, `F(t) = 1`,
Gauss), `Research.Backfill.Paper8.Proof.Orb.Orbits` ((a)–(c)), `Research.Backfill.Paper8.Proof.Orb.Counts` ((d)) and `Research.Backfill.Paper8.Proof.Orb.Switch` ((e), Lemma 3.4).
`Secular_monic`, used for (b) and (d), is `P8Spec.secular_monic` of agent `spec`.
-/

set_option autoImplicit false

open Polynomial BackfillPaper8 BackfillPaper8.Challenge

namespace P8Orb

theorem secularMonic : Secular_monic := fun m hm => P8Spec.secular_monic m hm

theorem branchMS_ne_zero {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k) : branchMS a ≠ 0 := by
  have hcard : Multiset.card (branchMS a) = k := by simp [branchMS]
  intro h
  rw [h, Multiset.card_zero] at hcard
  omega

theorem check_Lemma_3_3_a : BackfillPaper8.Challenge.Lemma_3_3_a := by
  intro k a _ f hf
  exact ⟨comp_neg_ne_neg (orbitFactor_eval_zero_ne hf),
    fun θ hθ he => not_mem_QAdj_of_even hf.1 hf.2.1 he hθ⟩

#print axioms check_Lemma_3_3_a

theorem check_Lemma_3_3_b : BackfillPaper8.Challenge.Lemma_3_3_b := by
  intro k a hk f hf hne
  have h0 := orbitFactor_eval_zero_ne hf
  refine ⟨isOrbitFactor_mirror hf, mirror_ne_self h0 hne, rootSet_mirror hf.1.ne_zero,
    fun θ hθ => ⟨mem_QAdj_of_not_even hf.1 hf.2.1 h0 hne hθ, fun hdeg => ?_,
      fun hdeg => not_rat_of_natDegree_ne_one hf hne hdeg hθ⟩⟩
  exact int_of_natDegree_eq_one (secularMonic _ (branchMS_ne_zero a hk)).1 hf hdeg hθ

#print axioms check_Lemma_3_3_b

theorem check_Lemma_3_3_c : BackfillPaper8.Challenge.Lemma_3_3_c := by
  intro k a _ z hz hsq
  exact even_orbit_of_not_isSquare hz hsq

#print axioms check_Lemma_3_3_c

theorem check_Lemma_3_3_d : BackfillPaper8.Challenge.Lemma_3_3_d := by
  intro k a hk
  exact orbit_count secularMonic (branchMS a) (branchMS_ne_zero a hk)

#print axioms check_Lemma_3_3_d

theorem check_Lemma_3_3_e : BackfillPaper8.Challenge.Lemma_3_3_e := by
  intro k a _ s hs f hf θ hθ θ' hθ' hG
  exact Gs_eq_zero_of_root a hs hf (hf.1.mem_rootSet.1 hθ) (hf.1.mem_rootSet.1 hθ') hG

#print axioms check_Lemma_3_3_e

theorem check_Lemma_3_4 : BackfillPaper8.Challenge.Lemma_3_4 := by
  intro k a hk s hs σ hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rw [← hσ ⟨0, hk⟩]
    exact hs (some ⟨⟨0, hk⟩, none⟩)
  refine ⟨fun θ hθ => ⟨Gs_eq_of_sig a hσ hθ, Ps_mem a hs _⟩, ?_, ?_⟩
  · -- no failure at an even orbit
    intro f hf he θ hθ hG
    have hθ0 : aeval θ f = 0 := hf.1.mem_rootSet.1 hθ
    rw [Gs_eq_of_sig a hσ (isSecular_of_root hf hθ0)] at hG
    apply not_mem_QAdj_of_even hf.1 hf.2.1 he hθ0
    have hP := Ps_mem a hs (θ ^ 2)
    rcases hσ1 with rfl | rfl
    · have e : -Ps a s (θ ^ 2) = θ := by linarith
      have key := neg_mem hP
      rwa [e] at key
    · have e : Ps a s (θ ^ 2) = θ := by linarith
      rwa [e] at hP
  · -- failure at a non-even pair
    intro f hf hne θ hθU
    have hmf := isOrbitFactor_mirror hf
    have hu : ((-1 : ℝ)) ^ f.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
    have hroot : ∀ x : ℝ, x ∈ f.rootSet ℝ ∪ (Challenge.mirror f).rootSet ℝ ↔
        aeval x f = 0 ∨ aeval (-x) f = 0 := by
      intro x
      rw [Set.mem_union, hf.1.mem_rootSet, (monic_mirror hf.1).mem_rootSet, aeval_mirror,
        mul_eq_zero, or_iff_right hu]
    have hsec : ∀ x : ℝ, x ∈ f.rootSet ℝ ∪ (Challenge.mirror f).rootSet ℝ →
        IsSecular (branchMS a) x := by
      intro x hx
      rcases (hroot x).1 hx with h | h
      · exact isSecular_of_root hf h
      · have h1 := isSecular_of_root hf h
        unfold IsSecular at h1 ⊢
        rwa [neg_sq] at h1
    have hsθ := hsec θ hθU
    have hnegU : -θ ∈ f.rootSet ℝ ∪ (Challenge.mirror f).rootSet ℝ := by
      rw [hroot, neg_neg]
      exact ((hroot θ).1 hθU).symm
    have hsnθ := hsec (-θ) hnegU
    constructor
    · rintro ⟨θ', hθ'U, hG'⟩
      have key : Gs a s θ = 0 ∨ Gs a s (-θ) = 0 := by
        rcases (hroot θ').1 hθ'U with h1 | h1
        · rcases (hroot θ).1 hθU with h2 | h2
          · exact Or.inl (Gs_eq_zero_of_root a hs hf h1 h2 hG')
          · exact Or.inr (Gs_eq_zero_of_root a hs hf h1 h2 hG')
        · have h1' : aeval θ' (Challenge.mirror f) = 0 := by rw [aeval_mirror, h1, mul_zero]
          rcases (hroot θ).1 hθU with h2 | h2
          · have h2' : aeval (-θ) (Challenge.mirror f) = 0 := by
              rw [aeval_mirror, neg_neg, h2, mul_zero]
            exact Or.inr (Gs_eq_zero_of_root a hs hmf h1' h2' hG')
          · have h2' : aeval θ (Challenge.mirror f) = 0 := by rw [aeval_mirror, h2, mul_zero]
            exact Or.inl (Gs_eq_zero_of_root a hs hmf h1' h2' hG')
      rcases key with h | h
      · rw [Gs_eq_of_sig a hσ hsθ] at h
        rcases hσ1 with rfl | rfl
        · right
          linarith
        · left
          linarith
      · rw [Gs_eq_of_sig a hσ hsnθ, neg_sq] at h
        rcases hσ1 with rfl | rfl
        · left
          linarith
        · right
          linarith
    · intro hP
      rcases hσ1 with rfl | rfl <;> rcases hP with hP | hP
      · exact ⟨-θ, hnegU, by rw [Gs_eq_of_sig a hσ hsnθ, neg_sq, hP]; ring⟩
      · exact ⟨θ, hθU, by rw [Gs_eq_of_sig a hσ hsθ, hP]; ring⟩
      · exact ⟨θ, hθU, by rw [Gs_eq_of_sig a hσ hsθ, hP]; ring⟩
      · exact ⟨-θ, hnegU, by rw [Gs_eq_of_sig a hσ hsnθ, neg_sq, hP]; ring⟩

#print axioms check_Lemma_3_4

end P8Orb
