import Research.TaskH.General.WholeClassCycleBudgetOriginal

/-! Whole-class cardinality consequences of actual original graph incidence. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open SimpleGraph _root_.TaskH.Challenge
open scoped BigOperators
variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

/-- The exact original count is (k+1)h, with h the original edge-family bound. -/
theorem original_bound_eq_successor_half_factorial (hk : 4 ≤ k) :
    bound k = (k + 1) * ((k - 1).factorial / 2) := by
  have hdiv : 2 ∣ (k - 1).factorial := by
    simpa only [Nat.factorial_two] using
      (Nat.factorial_dvd_factorial (show 2 ≤ k - 1 by omega))
  have hh : (k - 1).factorial / 2 * 2 = (k - 1).factorial := Nat.div_mul_cancel hdiv
  have he : k - 1 + 1 = k := by omega
  have hf := Nat.factorial_succ (k - 1)
  rw [he] at hf
  have hb := original_bound_balance (show 3 ≤ k by omega)
  rw [hf, ← hh] at hb
  apply Nat.mul_left_cancel (show 0 < 2 * k by omega)
  nlinarith [hb]

/-- EVERY whole old color class has at most k actual vertices. -/
theorem equality_whole_class_card_le [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k) :
    (wholeDeletedColorClass c γ).card ≤ k := by
  classical
  let W := wholeDeletedColorClass c γ
  let h := (k - 1).factorial / 2
  have hlow : W.card * (h + 1) ≤
      ∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard := by
    calc
      W.card * (h + 1) = ∑ _z ∈ W, (h + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z _ =>
        equality_original_vertex_cycle_incidence_lower hk hcrit hcount z)
  have hbudget := equality_whole_class_incidence_budget hk hcrit hcount c γ
  rw [original_bound_eq_successor_half_factorial hk] at hbudget
  by_contra hn
  change ¬ W.card ≤ k at hn
  have hbad : k + 1 ≤ W.card := by omega
  have hm := Nat.mul_le_mul_right (h + 1) hbad
  change (∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard) ≤ (k + 1) * h
    at hbudget
  nlinarith [hlow, hm, hbudget]

/-- The ENTIRE old singleton color class has at most k-2 vertices. -/
theorem equality_singleton_whole_class_card_le [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩) :
    (wholeDeletedColorClass c (c ⟨a, hva.ne.symm⟩)).card ≤ k - 2 := by
  classical
  let W := wholeDeletedColorClass c (c ⟨a, hva.ne.symm⟩)
  let h := (k - 1).factorial / 2
  have haW : a ∈ W := (mem_wholeDeletedColorClass c _ a).mpr ⟨hva.ne.symm, rfl⟩
  have hlow : (W.erase a).card * (h + 1) ≤
      ∑ z ∈ W.erase a, (_root_.TaskH.modCyclesThrough k G z).ncard := by
    calc
      (W.erase a).card * (h + 1) = ∑ _z ∈ W.erase a, (h + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z _ =>
        equality_original_vertex_cycle_incidence_lower hk hcrit hcount z)
  have hcenter := equality_original_singleton_center_incidence_lower hk hcrit hcount
    hva hvb c haunique hbunique habcolor
  have hsplit := Finset.sum_erase_add W
    (fun z => (_root_.TaskH.modCyclesThrough k G z).ncard) haW
  have hcard := Finset.card_erase_add_one haW
  have hbudget := equality_singleton_whole_class_missing_budget hk hcrit hcount
    hva hvb c haunique hbunique habcolor
  rw [original_bound_eq_successor_half_factorial hk] at hbudget
  by_contra hn
  change ¬ W.card ≤ k - 2 at hn
  have hbad : k - 2 ≤ (W.erase a).card := by omega
  have hm := Nat.mul_le_mul_right (h + 1) hbad
  change (∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard) + h ≤ (k + 1) * h
    at hbudget
  change 2 * h ≤ (_root_.TaskH.modCyclesThrough k G a).ncard at hcenter
  have he : k - 2 + 2 = k := by omega
  have hscale := congrArg (fun n : ℕ => n * (h + 1)) he
  nlinarith [hlow, hcenter, hsplit, hm, hbudget, hscale]

/-- The actual whole old color classes partition precisely V minus the deleted root. -/
theorem sum_wholeDeletedColorClass_card [Fintype V] {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    (∑ γ : Fin k, (wholeDeletedColorClass c γ).card) + 1 = Fintype.card V := by
  classical
  let T : Finset V := Finset.univ.erase v
  have hrow : ∀ z ∈ T,
      ((Finset.univ : Finset (Fin k)).filter (fun γ => z ∈ wholeDeletedColorClass c γ)).card = 1 := by
    intro z hz
    have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
    have he : (Finset.univ : Finset (Fin k)).filter
        (fun γ => z ∈ wholeDeletedColorClass c γ) = {c ⟨z, hzv⟩} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        mem_wholeDeletedColorClass]
      constructor
      · rintro ⟨_, hc⟩
        exact hc.symm
      · intro hc
        exact ⟨hzv, hc.symm⟩
    rw [he, Finset.card_singleton]
  have hcol : ∀ γ : Fin k,
      (T.filter (fun z => z ∈ wholeDeletedColorClass c γ)) = wholeDeletedColorClass c γ := by
    intro γ
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hz
      obtain ⟨hzv, _⟩ := (mem_wholeDeletedColorClass c γ z).mp hz
      exact ⟨Finset.mem_erase.mpr ⟨hzv, Finset.mem_univ z⟩, hz⟩
  have hdc := _root_.TaskH.FiniteBudget.relation_double_count T (Finset.univ : Finset (Fin k))
    (fun z γ => z ∈ wholeDeletedColorClass c γ)
  have hr : (∑ z ∈ T, ((Finset.univ : Finset (Fin k)).filter
      (fun γ => z ∈ wholeDeletedColorClass c γ)).card) = T.card := by
    calc
      _ = ∑ _z ∈ T, 1 := Finset.sum_congr rfl hrow
      _ = T.card := by simp
  have hc : (∑ γ : Fin k, (T.filter (fun z => z ∈ wholeDeletedColorClass c γ)).card) =
      ∑ γ : Fin k, (wholeDeletedColorClass c γ).card := by
    apply Finset.sum_congr rfl
    intro γ _
    rw [hcol γ]
  have hdc' : (∑ z ∈ T, ((Finset.univ : Finset (Fin k)).filter
      (fun γ => z ∈ wholeDeletedColorClass c γ)).card) =
      (∑ γ : Fin k, (T.filter (fun z => z ∈ wholeDeletedColorClass c γ)).card) := by
    convert hdc using 1 <;>
      apply Finset.sum_congr rfl <;>
      intro t _ht <;>
      congr 1 <;>
      ext a <;>
      simp only [Finset.mem_filter]
  have hpartition : T.card = ∑ γ : Fin k, (wholeDeletedColorClass c γ).card :=
    hr.symm.trans (hdc'.trans hc)
  have ht : T.card + 1 = Fintype.card V := by
    simpa only [T, Finset.card_univ] using
      (Finset.card_erase_add_one (Finset.mem_univ v))
  omega

/-- Original count plus TWO actual singleton colors bounds the entire original graph.
The original root/coloring/neighbors are actual local data, not size/cycle oracles. -/
theorem equality_two_singletons_original_order_le [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩) :
    Fintype.card V ≤ k ^ 2 - 3 := by
  classical
  let α := c ⟨a, hva.ne.symm⟩
  let β := c ⟨b, hvb.ne.symm⟩
  let f := fun γ : Fin k => (wholeDeletedColorClass c γ).card
  have hα : f α ≤ k - 2 := equality_singleton_whole_class_card_le hk hcrit hcount
    hva hvb c haunique hbunique habcolor
  have hβ : f β ≤ k - 2 := equality_singleton_whole_class_card_le hk hcrit hcount
    hvb hva c hbunique haunique habcolor.symm
  have hne : α ≠ β := habcolor
  let T : Finset (Fin k) := (Finset.univ.erase α).erase β
  have hβmem : β ∈ (Finset.univ : Finset (Fin k)).erase α :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ β⟩
  have he1 := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) f (Finset.mem_univ α)
  have he2 := Finset.sum_erase_add ((Finset.univ : Finset (Fin k)).erase α) f hβmem
  have hc1 := Finset.card_erase_add_one (Finset.mem_univ α)
  have hc2 := Finset.card_erase_add_one hβmem
  have hcard : T.card + 2 = k := by
    simp only [Finset.card_univ, Fintype.card_fin] at hc1
    change T.card + 1 = ((Finset.univ : Finset (Fin k)).erase α).card at hc2
    omega
  have hrest : (∑ γ ∈ T, f γ) ≤ T.card * k := by
    calc
      _ ≤ ∑ _γ ∈ T, k := Finset.sum_le_sum (fun γ _ =>
        equality_whole_class_card_le hk hcrit hcount c γ)
      _ = T.card * k := by simp
  have hpartition := sum_wholeDeletedColorClass_card c
  change (∑ γ : Fin k, f γ) + 1 = Fintype.card V at hpartition
  change (∑ γ ∈ T, f γ) + f β =
    ∑ γ ∈ (Finset.univ : Finset (Fin k)).erase α, f γ at he2
  have hsub : 3 ≤ k ^ 2 := by nlinarith [hk]
  have he : k - 2 + 2 = k := by omega
  have hTc : T.card = k - 2 := by omega
  rw [hTc] at hrest
  have hscale := congrArg (fun n : ℕ => n * k) he
  have hfin : Fintype.card V + 3 ≤ k ^ 2 := by
    nlinarith [hα, hβ, hrest, he1, he2, hpartition, hscale]
  omega
end TaskH.General
#print axioms TaskH.General.original_bound_eq_successor_half_factorial
#print axioms TaskH.General.equality_whole_class_card_le
#print axioms TaskH.General.equality_singleton_whole_class_card_le
#print axioms TaskH.General.sum_wholeDeletedColorClass_card
#print axioms TaskH.General.equality_two_singletons_original_order_le
