import Research.TaskH.Five.FiveLightEdgePathLengths

/-! Finite color fibers and the arithmetic used after their actual graph
bounds have been established. These helpers add no original-graph premise. -/

universe u

namespace TaskH.Five

open SimpleGraph

variable {V : Type u}

noncomputable def lightColorFiber (S : Finset V) (c : V → Fin 5) (a : Fin 5) :
    Finset V := by
  classical
  exact S.filter (fun x => c x = a)

theorem light_sum_color_fibers (S : Finset V) (c : V → Fin 5) :
    (∑ a : Fin 5, (lightColorFiber S c a).card) = S.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (s := S) (t := (Finset.univ : Finset (Fin 5)))
    (f := c) (fun _ _ => Finset.mem_univ _)).symm

theorem light_five_color_budget_with_common
    (N A B T : Fin 5 → ℕ) (alpha beta : Fin 5) (hbeta : beta ≠ alpha)
    (n du dv : ℕ) (hzero : 5 ≤ N alpha)
    (hclass : ∀ a : Fin 5, a ≠ alpha →
      A a + B a + 1 + (if a = beta then 1 else 0) ≤ N a + 2 * T a)
    (hdegree : du + dv =
      (∑ a ∈ (Finset.univ : Finset (Fin 5)).erase alpha, (A a + B a)) + 2)
    (htotal : (∑ a : Fin 5, N a) = n) :
    du + dv + 8 ≤ n + 2 * (∑ a : Fin 5, T a) := by
  classical
  let U := (Finset.univ : Finset (Fin 5)).erase alpha
  have hcard : U.card = 4 := by simp [U]
  have hb : beta ∈ U := by simp [U, hbeta]
  have hsum := Finset.sum_le_sum (s := U) (fun a ha =>
    hclass a (Finset.mem_erase.mp ha).1)
  have hbonus : (∑ a ∈ U, if a = beta then 1 else 0 : ℕ) = 1 := by simp [hb]
  have hparts : (∑ a ∈ U, N a) + N alpha = n := by
    simpa only [U, htotal] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 5)))
        (f := N) (Finset.mem_univ alpha))
  have ht : (∑ a ∈ U, T a) ≤ ∑ a : Fin 5, T a := by
    exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have hsleft : (∑ a ∈ U, (A a + B a + 1 + (if a = beta then 1 else 0))) =
      (∑ a ∈ U, (A a + B a)) + 5 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      hcard, hbonus]
  have hsright : (∑ a ∈ U, (N a + 2 * T a)) =
      (∑ a ∈ U, N a) + 2 * (∑ a ∈ U, T a) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsleft, hsright] at hsum
  change du + dv = (∑ a ∈ U, (A a + B a)) + 2 at hdegree
  omega

theorem light_five_color_budget
    (N A B T : Fin 5 → ℕ) (alpha beta : Fin 5) (hbeta : beta ≠ alpha)
    (n du dv : ℕ) (hzero : 5 ≤ N alpha)
    (hclass : ∀ a : Fin 5, a ≠ alpha →
      A a + B a + 1 + (if a = beta then 1 else 0) ≤ N a + 2 * T a)
    (hdegree : du + dv =
      (∑ a ∈ (Finset.univ : Finset (Fin 5)).erase alpha, (A a + B a)) + 2)
    (htotal : (∑ a : Fin 5, N a) = n)
    (hcommon : (∑ a : Fin 5, T a) ≤ 1) : du + dv + 6 ≤ n := by
  have h := light_five_color_budget_with_common N A B T alpha beta hbeta
    n du dv hzero hclass hdegree htotal
  omega

end TaskH.Five

#print axioms TaskH.Five.lightColorFiber
#print axioms TaskH.Five.light_sum_color_fibers
#print axioms TaskH.Five.light_five_color_budget_with_common
#print axioms TaskH.Five.light_five_color_budget
