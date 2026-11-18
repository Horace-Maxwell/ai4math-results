import Research.TaskH.General.SingletonBaselineOriginal
import Research.TaskH.Degree

/-! The actual root-neighbor fibers partition N(v). Criticality supplies
nonemptiness of every fiber; only the actual singleton fibers contribute
the one-point correction. Whole deleted color classes are not counted. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge
open scoped BigOperators

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_minimum_degree_two_mul_sub_two [DecidableRel G.Adj]
    (hk : 5 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) : 2 * k - 2 ≤ G.degree v := by
  classical
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedVertex hcrit v
  let F : Fin k → Finset (G.neighborSet v) := fun i =>
    Finset.univ.filter (fun z => _root_.TaskH.neighborColor v c z = i)
  have hpositive : ∀ i, 1 ≤ (F i).card := by
    intro i
    obtain ⟨z, hz⟩ := _root_.TaskH.critical_neighborColor_surjective hcrit v c i
    have hm : z ∈ F i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hp : 0 < (F i).card := Finset.card_pos.mpr ⟨z, hm⟩
    omega
  have hone : ∀ i, (F i).card = 1 → i ∈ originalSingletonPalette c := by
    intro i hFi
    obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hFi
    have hnF : n ∈ F i := by rw [hn]; exact Finset.mem_singleton_self _
    have hni : _root_.TaskH.neighborColor v c n = i := (Finset.mem_filter.mp hnF).2
    have hvn : G.Adj v n.val := (G.mem_neighborSet v n.val).mp n.property
    have hnJ : n.val ∈ originalSingletonCenters c := by
      apply (mem_originalSingletonCenters c).mpr
      refine ⟨hvn, ?_⟩
      intro z hzv hvz hc
      have hzF : (⟨z, hvz⟩ : G.neighborSet v) ∈ F i := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hc.trans hni
      have he : (⟨z, hvz⟩ : G.neighborSet v) = n :=
        Finset.mem_singleton.mp (by rw [← hn]; exact hzF)
      exact congrArg Subtype.val he
    have hpal := original_singleton_color_mem_palette c hnJ hvn.ne.symm
    exact hni ▸ hpal
  have hpoint : ∀ i, 2 ≤ (F i).card + if i ∈ originalSingletonPalette c then 1 else 0 := by
    intro i
    have hp := hpositive i
    by_cases hi : i ∈ originalSingletonPalette c
    · rw [ite_eq_left hi]
      omega
    · rw [ite_eq_right hi]
      have hn : (F i).card ≠ 1 := fun he => hi (hone i he)
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => hpoint i)
  have hdegree : (∑ i : Fin k, (F i).card) = G.degree v := by
    have he := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (G.neighborSet v)))
      (t := (Finset.univ : Finset (Fin k))) (f := _root_.TaskH.neighborColor v c)
      (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ, G.card_neighborSet_eq_degree] using he.symm
  have hindicator : (∑ i : Fin k, if i ∈ originalSingletonPalette c then 1 else 0) =
      (originalSingletonPalette c).card := by
    rw [← Finset.card_filter]
    simp
  rw [Finset.sum_add_distrib, hdegree, hindicator] at hsum
  have hsum' : 2 * k ≤ G.degree v + (originalSingletonPalette c).card := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_comm] using hsum
  have hq := equality_original_singleton_centers_le_two hk hcrit hcount hnot c
  have he := original_singleton_palette_card c
  omega

end TaskH.General

#print axioms TaskH.General.equality_original_minimum_degree_two_mul_sub_two
