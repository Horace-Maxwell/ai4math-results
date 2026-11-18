import Research.TaskH.Gao.Progression

/-! Exact Gao concatenation interface. The support intersection is the actual
region-avoidance requirement in the primary lemma, not an assumption on Main.
No toPath or shortening operation is used; every length is the append sum. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

theorem append_isPath_of_only_common_endpoint {u w v : V}
    {p : G.Walk u w} {q : G.Walk w v} (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z : V, z ∈ p.support → z ∈ q.support → z = w) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append]
  refine hp.support_nodup.append hq.support_nodup.tail ?_
  apply List.disjoint_left.mpr
  intro z hzp hzq
  have hzw : z = w := hmeet z hzp (List.mem_of_mem_tail hzq)
  subst z
  have hnodup := hq.support_nodup
  rw [← Walk.cons_tail_support q] at hnodup
  exact hnodup.notMem hzq

/-- Same-graph actual path witnesses for the s+t-1 progression. The second
length list is independent of the selected endpoint, exactly as required by
the original concatenation lemma. -/
theorem admissible_path_concatenation {s t a b d e : ℕ} {u v : V}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hd : d = 1 ∨ d = 2) (he : e = 1 ∨ e = 2)
    (w : Fin s → V) (p : ∀ i : Fin s, G.Walk u (w i))
    (q : ∀ i : Fin s, Fin t → G.Walk (w i) v)
    (hp : ∀ i, (p i).IsPath) (hq : ∀ i j, (q i j).IsPath)
    (hpl : ∀ i, (p i).length = a + i.val * d)
    (hql : ∀ i j, (q i j).length = b + j.val * e)
    (hmeet : ∀ i j z, z ∈ (p i).support → z ∈ (q i j).support → z = w i) :
    HasAdmissiblePaths G u v (s + t - 1) := by
  classical
  obtain ⟨step, hstep, hindices⟩ := admissible_sum_indices hs ht d e hd he
  have hw : ∀ n : Fin (s + t - 1), ∃ i : Fin s, ∃ j : Fin t,
      n.val * step = i.val * d + j.val * e := by
    intro n
    obtain ⟨i, hi, j, hj, hij⟩ := hindices n.val n.isLt
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, hij⟩
  choose leftIndex rightIndex hsum using hw
  refine ⟨a + b, step,
    (fun n => (p (leftIndex n)).append (q (leftIndex n) (rightIndex n))), ?_⟩
  refine ⟨by omega, hstep, ?_⟩
  intro n
  constructor
  · exact append_isPath_of_only_common_endpoint
      (hp (leftIndex n)) (hq (leftIndex n) (rightIndex n))
      (hmeet (leftIndex n) (rightIndex n))
  · rw [Walk.length_append, hpl, hql]
    have hn := hsum n
    omega

#print axioms append_isPath_of_only_common_endpoint
#print axioms admissible_path_concatenation
end TaskH.Gao
