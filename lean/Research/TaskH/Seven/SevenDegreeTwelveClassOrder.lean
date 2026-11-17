import Research.TaskH.Seven.SevenDegreeTwelveFrame
import Research.TaskH.Seven.SevenColorClassBudgets

/-! Degree-twelve class capacities and the original order bound obtained from
actual deleted-color classes, without assuming coverage by outside pools. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem deletedColorClass_card_sum (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    (∑ i : Fin 7, (deletedColorClass v c i).card) + 1 = Fintype.card V := by
  cases (inferInstance : DecidableRel G.Adj) v v with
  | isTrue hvv => exact (G.loopless.irrefl v hvv).elim
  | isFalse _ =>
      classical
      have hcol : ∀ z : {x : V // x ≠ v},
          (Finset.univ : Finset (Fin 7)).filter (fun i => c z = i) = {c z} := by
        intro z
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact eq_comm
      have he : (∑ i : Fin 7, (deletedColorClass v c i).card) =
          Fintype.card {x : V // x ≠ v} := by
        calc
          _ = ∑ i : Fin 7, ((Finset.univ : Finset {x : V // x ≠ v}).filter
              (fun z => c z = i)).card := rfl
          _ = ∑ z : {x : V // x ≠ v},
              ((Finset.univ : Finset (Fin 7)).filter (fun i => c z = i)).card := by
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
            exact Finset.sum_comm
          _ = _ := by simp only [hcol, Finset.card_singleton, Finset.sum_const,
              Finset.card_univ, smul_eq_mul, mul_one]
      have hdel : Fintype.card {x : V // x ≠ v} = Fintype.card V - 1 := by
        simpa only [Fintype.card_subtype_eq] using
          (Fintype.card_subtype_compl (fun x : V => x = v))
      have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
      omega

theorem equality_degree_twelve_class_capacities
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12) :
    ∀ i : Fin 7, (deletedColorClass v c i).card ≤
      if i ∈ singletonNeighborColors v c then 5 else 7 := by
  classical
  have hS := (equality_degree_twelve_fiber_pattern hcrit hc hnot v c hv).1
  intro i
  by_cases hi : i ∈ singletonNeighborColors v c
  · rw [ite_eq_left hi]
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega :
      1 < (singletonNeighborColors v c).card) i
    exact equality_singletonColorClass_card_le_five hcrit hc hnot v c
      ⟨j, hj⟩ ⟨i, hi⟩ (fun he => hji (congrArg Subtype.val he))
  · rw [ite_eq_right hi]
    exact equality_deletedColorClass_card_le_seven hcrit hc hnot v c i

theorem equality_degree_twelve_card_le_forty_six
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) (hv : G.degree v = 12) :
    Fintype.card V ≤ 46 := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  let S := singletonNeighborColors v c
  have hS : S.card = 2 := (equality_degree_twelve_fiber_pattern hcrit hc hnot v c hv).1
  have hcap := equality_degree_twelve_class_capacities hcrit hc hnot v c hv
  have hsingle : (∑ i : Fin 7, if i ∈ S then 1 else 0 : ℕ) = S.card := by
    have he : (Finset.univ : Finset (Fin 7)).filter (fun i => i ∈ S) = S := by
      ext i
      simp
    calc
      _ = ((Finset.univ : Finset (Fin 7)).filter (fun i => i ∈ S)).card :=
        Finset.sum_boole _ _
      _ = _ := congrArg Finset.card he
  have hweight : (∑ i : Fin 7, if i ∈ S then 5 else 7 : ℕ) + 2 * S.card = 49 := by
    rw [← hsingle, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hpoint : ∀ i : Fin 7,
        (if i ∈ S then 5 else 7 : ℕ) + 2 * (if i ∈ S then 1 else 0 : ℕ) = 7 := by
      intro i
      split_ifs <;> rfl
    simp only [hpoint, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hsumle : (∑ i : Fin 7, (deletedColorClass v c i).card) ≤
      ∑ i : Fin 7, if i ∈ S then 5 else 7 := Finset.sum_le_sum (fun i _ => hcap i)
  have hn := deletedColorClass_card_sum v c
  omega


theorem equality_degree_twelve_outside_closed_card_le_thirty_three
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) (hv : G.degree v = 12) :
    ((insert v (G.neighborFinset v))ᶜ : Finset V).card ≤ 33 := by
  classical
  have hn := equality_degree_twelve_card_le_forty_six hcrit hc hnot v hv
  have hself : v ∉ G.neighborFinset v := by
    intro hm
    exact ((G.mem_neighborFinset v v).mp hm).ne rfl
  have hclosed : (insert v (G.neighborFinset v)).card = 13 := by
    rw [Finset.card_insert_of_notMem hself, G.card_neighborFinset_eq_degree, hv]
  have hh := Finset.card_add_card_compl (insert v (G.neighborFinset v))
  omega

end TaskH.Seven
#print axioms TaskH.Seven.deletedColorClass_card_sum
#print axioms TaskH.Seven.equality_degree_twelve_class_capacities
#print axioms TaskH.Seven.equality_degree_twelve_card_le_forty_six

#print axioms TaskH.Seven.equality_degree_twelve_outside_closed_card_le_thirty_three
