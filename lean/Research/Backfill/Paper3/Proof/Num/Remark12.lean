import Research.Backfill.Paper3.Proof.Num.RunR12a
import Research.Backfill.Paper3.Proof.Num.RunR12b

/-!
# Remark 12

At `γ = 1/10`, `G_n = k H_d ∪ r K_{d,d}` beats `m K_{d,d}` for 92 of the `m ∈ [2, 120]` when
`d = 2` (largest `m = 100`) and for 56 of them when `d = 3` (largest `m = 60`). Each comparison is
read off the kernel runs `run_R12a`, `run_R12b` through `cmp_of_run`; the counts are then counts
of the code `0` in the lists `codes2`, `codes3`.
-/

set_option autoImplicit false

namespace P3Num

open Finset BackfillPaper3.Challenge

theorem r12a_cmp (a₁ b₁ a₂ b₂ : Fin 2) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 120) :
    cmpN (iGamma (KddUnion m 2) 2 (1 / 10)) (iGamma (Gn 2 m a₁ b₁ a₂ b₂) 2 (1 / 10)) =
      nthL codes2 m :=
  cmp_of_run 2 K2 H2 Pd_two a₁ b₁ a₂ b₂ (edgePoly_H2 a₁ b₁ a₂ b₂) 97 qR12a 120 run_R12a m hm1 hm
    1 10 (1 / 10) (by norm_num) _ (List.mem_singleton_self _) (by omega)

theorem r12b_cmp (a₁ b₁ a₂ b₂ : Fin 3) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 120) :
    cmpN (iGamma (KddUnion m 3) 3 (1 / 10)) (iGamma (Gn 3 m a₁ b₁ a₂ b₂) 3 (1 / 10)) =
      nthL codes3 m :=
  cmp_of_run 3 K3 H3 Pd_three a₁ b₁ a₂ b₂ (edgePoly_H3 a₁ b₁ a₂ b₂) 217 qR12b 120 run_R12b m hm1
    hm 1 10 (1 / 10) (by norm_num) _ (List.mem_singleton_self _) (by omega)

theorem codes2_count : #((Icc 2 120).filter fun m => nthL codes2 m = 0) = 92 := by
  decide +kernel

theorem codes3_count : #((Icc 2 120).filter fun m => nthL codes3 m = 0) = 56 := by
  decide +kernel

theorem codes2_tail : ∀ m ∈ Icc 101 120, nthL codes2 m = 2 := by
  decide +kernel

theorem codes3_tail : ∀ m ∈ Icc 61 120, nthL codes3 m = 2 := by
  decide +kernel

theorem remark12 : Remark12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← codes2_count]
    congr 1
    refine Finset.filter_congr fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [← cmpN_eq_zero_iff, r12a_cmp _ _ _ _ m (by omega) hm.2]
  · exact (cmpN_eq_zero_iff _ _).1
      ((r12a_cmp _ _ _ _ 100 (by norm_num) (by norm_num)).trans (by decide +kernel))
  · intro m hm
    have hc := codes2_tail m hm
    rw [Finset.mem_Icc] at hm
    exact le_of_lt ((cmpN_eq_two_iff _ _).1 ((r12a_cmp _ _ _ _ m (by omega) hm.2).trans hc))
  · rw [← codes3_count]
    congr 1
    refine Finset.filter_congr fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [← cmpN_eq_zero_iff, r12b_cmp _ _ _ _ m (by omega) hm.2]
  · exact (cmpN_eq_zero_iff _ _).1
      ((r12b_cmp _ _ _ _ 60 (by norm_num) (by norm_num)).trans (by decide +kernel))
  · intro m hm
    have hc := codes3_tail m hm
    rw [Finset.mem_Icc] at hm
    exact le_of_lt ((cmpN_eq_two_iff _ _).1 ((r12b_cmp _ _ _ _ m (by omega) hm.2).trans hc))

end P3Num
