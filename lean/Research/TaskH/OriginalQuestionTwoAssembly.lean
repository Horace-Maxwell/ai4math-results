import Research.TaskH.Bai.OriginalLongZeroCycle
import Research.TaskH.General.OriginalStrongerMinimumDegree
import Research.TaskH.General.GoodCycleLowerBound
import Research.TaskH.General.CriticalConnectivity
import Research.TaskH.MainFour
import Research.TaskH.MainFive

/-! Original all-k Question2 assembly. All long-cycle, connectivity, degree
and short-cycle interfaces are discharged inside the proof. This is an
uncompiled candidate and grants no formal or publication credit. -/
set_option autoImplicit false
universe u
namespace TaskH
open SimpleGraph Challenge

theorem equality_case_original_ge_six (k : ℕ) (hk : 6 ≤ k) :
    EqualityCase.{u} k := by
  intro V _ G hcrit hcount
  classical
  by_contra hnot
  have hconn : G.Connected := General.critical_original_connected hcrit
  let _ : Nonempty V := hconn.nonempty
  have hdeg : ∀ v : V, 2 * k - 1 ≤ G.degree v :=
    General.equality_original_minimum_degree_two_mul_sub_one hk hcrit hcount hnot
  have hs : General.ShortCycles k G :=
    General.GoodCycles.equality_shortCycles_from_critical_count (by omega) hcrit hcount
  obtain ⟨z, p, hp, hdiv, hlong⟩ :=
    Bai.connected_high_degree_original_long_zero_cycle G k (by omega) hconn hdeg
  have heq : p.length = k := hs p hp hdiv
  omega

theorem original_question_two_all_k : Question2.{u} := by
  intro k hk
  by_cases hk4 : k = 4
  · subst k
    exact case_four
  by_cases hk5 : k = 5
  · subst k
    exact case_five
  exact equality_case_original_ge_six k (by omega)

end TaskH
#print axioms TaskH.equality_case_original_ge_six
#print axioms TaskH.original_question_two_all_k
