import Research.TaskH.Seven.SevenK5PackingNoSmall
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! Symbolic finite counting for the last K5 branch. No tuple is enumerated.
An ordered star-forest edge has a leaf, and a fixed two-coordinate tuple fiber
has cardinal 6^3. Restricting to six actual points per group gives 30 points. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

noncomputable def orderedStarEdges {A : Type u} [Fintype A]
    (F : SimpleGraph A) (rank : A → ℕ) : Finset (A × A) :=
  Finset.univ.filter (fun e => F.Adj e.1 e.2 ∧ rank e.1 < rank e.2)

theorem ordered_star_edges_card_le {A : Type u} [Fintype A]
    (F : SimpleGraph A) [DecidableRel F.Adj] (rank : A → ℕ)
    (hleaf : ∀ a b, F.Adj a b → F.degree a ≤ 1 ∨ F.degree b ≤ 1) :
    (orderedStarEdges F rank).card ≤ Fintype.card A := by
  classical
  let E := orderedStarEdges F rank
  have hEeq : E = (Finset.univ : Finset (A × A)).filter
      (fun e => F.Adj e.1 e.2 ∧ rank e.1 < rank e.2) :=
    Finset.filter_congr_decidable _ _ _
  have hmemE (e : A × A) : e ∈ E ↔ F.Adj e.1 e.2 ∧ rank e.1 < rank e.2 := by
    rw [hEeq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let R : A → A × A → Prop := fun v e => (v = e.1 ∨ v = e.2) ∧ F.degree v ≤ 1
  have hrow : ∀ v ∈ (Finset.univ : Finset A), (E.filter (R v)).card ≤ 1 := by
    intro v _hv
    apply Finset.card_le_one.mpr
    rintro ⟨a, b⟩ he ⟨c, d⟩ he'
    have hab := (hmemE (a, b)).mp (Finset.mem_filter.mp he).1
    have hcd := (hmemE (c, d)).mp (Finset.mem_filter.mp he').1
    have hv := (Finset.mem_filter.mp he).2
    have hv' := (Finset.mem_filter.mp he').2
    have huniq : ∀ s t, F.Adj v s → F.Adj v t → s = t := by
      intro s t hvs hvt
      apply Finset.card_le_one.mp (show (F.neighborFinset v).card ≤ 1 from by
        simpa only [F.card_neighborFinset_eq_degree] using hv.2)
      · exact (F.mem_neighborFinset v s).mpr hvs
      · exact (F.mem_neighborFinset v t).mpr hvt
    have hp : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      rcases hv.1 with hva | hvb
      · rcases hv'.1 with hvc | hvd
        · exact Or.inl ⟨hva.symm.trans hvc, huniq b d
            (by simpa only [hva] using hab.1) (by simpa only [hvc] using hcd.1)⟩
        · exact Or.inr ⟨hva.symm.trans hvd, huniq b c
            (by simpa only [hva] using hab.1) (by simpa only [hvd] using hcd.1.symm)⟩
      · rcases hv'.1 with hvc | hvd
        · exact Or.inr ⟨huniq a d (by simpa only [hvb] using hab.1.symm)
            (by simpa only [hvc] using hcd.1), hvb.symm.trans hvc⟩
        · exact Or.inl ⟨huniq a c (by simpa only [hvb] using hab.1.symm)
            (by simpa only [hvd] using hcd.1.symm), hvb.symm.trans hvd⟩
    rcases hp with ⟨rfl, rfl⟩ | ⟨had, hbc⟩
    · rfl
    · have hbad := hab.2
      rw [had, hbc] at hbad
      exact (Nat.lt_asymm hbad hcd.2).elim
  have hcol : ∀ e ∈ E, 1 ≤ ((Finset.univ : Finset A).filter (fun v => R v e)).card := by
    rintro ⟨a, b⟩ he
    have hab := ((hmemE (a, b)).mp he).1
    apply Finset.card_pos.mpr
    rcases hleaf a b hab with ha | hb
    · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl, ha⟩⟩
    · exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl, hb⟩⟩
  have hd : (∑ v : A, (E.filter (R v)).card) =
      ∑ e ∈ E, ((Finset.univ : Finset A).filter (fun v => R v e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hl : E.card ≤ ∑ e ∈ E, ((Finset.univ : Finset A).filter (fun v => R v e)).card := by
    calc
      _ = ∑ _e ∈ E, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hcol
  have hh : (∑ v : A, (E.filter (R v)).card) ≤ Fintype.card A := by
    calc
      _ ≤ ∑ _v : A, 1 := Finset.sum_le_sum hrow
      _ = _ := by simp
  exact hl.trans (hd.symm.le.trans hh)

theorem seven_six_tuple_fiber_zero_one (r s : Fin 6) :
    ((Finset.univ : Finset (Fin 5 → Fin 6)).filter
      (fun f => f 0 = r ∧ f 1 = s)).card = 216 := by
  classical
  let e : (Fin 3 → Fin 6) ≃ {f : Fin 5 → Fin 6 // f 0 = r ∧ f 1 = s} :=
    { toFun := fun f => ⟨Fin.cons r (Fin.cons s f), by simp⟩
      invFun := fun f => Fin.tail (Fin.tail f.val)
      left_inv := by intro f; funext i; fin_cases i <;> rfl
      right_inv := by
        intro f
        apply Subtype.ext
        funext i
        fin_cases i
        · exact f.property.1.symm
        · exact f.property.2.symm
        · rfl
        · rfl
        · rfl }
  have hc := Fintype.card_congr e
  have hf := Fintype.card_subtype (fun f : Fin 5 → Fin 6 => f 0 = r ∧ f 1 = s)
  rw [hf] at hc
  norm_num [Fintype.card_fun] at hc
  exact hc.symm

theorem seven_six_tuple_fiber (i j : Fin 5) (hij : i ≠ j) (r s : Fin 6) :
    ((Finset.univ : Finset (Fin 5 → Fin 6)).filter
      (fun f => f i = r ∧ f j = s)).card = 216 := by
  classical
  obtain ⟨π, hπi, hπj⟩ := exists_five_index_order_zero_one i j hij
  have hπ0 : π.symm 0 = i := by rw [← hπi, π.symm_apply_apply]
  have hπ1 : π.symm 1 = j := by rw [← hπj, π.symm_apply_apply]
  let e : {f : Fin 5 → Fin 6 // f i = r ∧ f j = s} ≃
      {f : Fin 5 → Fin 6 // f 0 = r ∧ f 1 = s} :=
    { toFun := fun f => ⟨fun a => f.val (π.symm a), by
        simpa only [hπ0, hπ1] using f.property⟩
      invFun := fun f => ⟨fun a => f.val (π a), by
        simpa only [hπi, hπj] using f.property⟩
      left_inv := by intro f; apply Subtype.ext; funext a; simp only [π.symm_apply_apply]
      right_inv := by intro f; apply Subtype.ext; funext a; simp only [π.apply_symm_apply] }
  have hc := Fintype.card_congr e
  rw [Fintype.card_subtype, Fintype.card_subtype] at hc
  exact hc.trans (seven_six_tuple_fiber_zero_one r s)

theorem thirty_point_independent_transversal
    (E : Finset ((Fin 5 × Fin 6) × (Fin 5 × Fin 6)))
    (hE : E.card ≤ 30) (hsep : ∀ e ∈ E, e.1.1 ≠ e.2.1) :
    ∃ f : Fin 5 → Fin 6, ∀ e ∈ E,
      ¬ (f e.1.1 = e.1.2 ∧ f e.2.1 = e.2.2) := by
  classical
  let A : Finset (Fin 5 → Fin 6) := Finset.univ
  let R : (Fin 5 → Fin 6) → ((Fin 5 × Fin 6) × (Fin 5 × Fin 6)) → Prop :=
    fun f e => f e.1.1 = e.1.2 ∧ f e.2.1 = e.2.2
  by_contra hno
  have hrow : ∀ f ∈ A, 1 ≤ (E.filter (R f)).card := by
    intro f _hf
    apply Finset.card_pos.mpr
    by_contra hempty
    apply hno
    refine ⟨f, ?_⟩
    intro e he hR
    exact hempty ⟨e, Finset.mem_filter.mpr ⟨he, hR⟩⟩
  have hcol : ∀ e ∈ E, (A.filter (fun f => R f e)).card = 216 := by
    intro e he
    exact seven_six_tuple_fiber e.1.1 e.2.1 (hsep e he) e.1.2 e.2.2
  have hd : (∑ f ∈ A, (E.filter (R f)).card) =
      ∑ e ∈ E, (A.filter (fun f => R f e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hlow : 7776 ≤ ∑ f ∈ A, (E.filter (R f)).card := by
    calc
      7776 = ∑ _f ∈ A, 1 := by norm_num [A, Fintype.card_fun]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhigh : (∑ e ∈ E, (A.filter (fun f => R f e)).card) = 216 * E.card := by
    calc
      _ = ∑ _e ∈ E, 216 := Finset.sum_congr rfl hcol
      _ = _ := by simp [Nat.mul_comm]
  have hm := Nat.mul_le_mul_left 216 hE
  omega

end TaskH.Seven
#print axioms TaskH.Seven.orderedStarEdges
#print axioms TaskH.Seven.ordered_star_edges_card_le
#print axioms TaskH.Seven.seven_six_tuple_fiber_zero_one
#print axioms TaskH.Seven.seven_six_tuple_fiber
#print axioms TaskH.Seven.thirty_point_independent_transversal
