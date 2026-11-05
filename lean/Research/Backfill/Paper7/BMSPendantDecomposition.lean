import Research.Backfill.Paper7.BMSWideNegative
import Research.Backfill.Paper7.PendantPathSuffix

/-! A bijection retaining every vertex outside the three terminal vertices.
No connectedness assumption and no component deletion are present. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7BMS
open BackfillPaper7.Challenge

def PendantCore {V : Type} (v : Fin 4 → V) : Type :=
  {u : V // ∀ j : Fin 3, u ≠ v j.succ}
#print axioms Paper7BMS.PendantCore

def pendantRoot {V : Type} (v : Fin 4 → V) (hv : Function.Injective v) :
    PendantCore v := ⟨v 0, by
  intro j h
  have he := congrArg Fin.val (hv h)
  simp only [Fin.val_zero, Fin.val_succ] at he
  omega⟩
#print axioms Paper7BMS.pendantRoot

def pendantEquiv {V : Type} (v : Fin 4 → V) (hv : Function.Injective v) :
    PendantCore v ⊕ Fin 3 ≃ V :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun j => v j.succ)) (by
    constructor
    · intro a b h
      rcases a with a | a <;> rcases b with b | b
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact False.elim (a.property b h)
      · exact False.elim (b.property a h.symm)
      · exact congrArg Sum.inr (Fin.succ_injective 3 (hv h))
    · intro u
      classical
      by_cases h : ∀ j : Fin 3, u ≠ v j.succ
      · exact ⟨Sum.inl ⟨u, h⟩, rfl⟩
      · push Not at h
        obtain ⟨j, hj⟩ := h
        exact ⟨Sum.inr j, hj.symm⟩)
#print axioms Paper7BMS.pendantEquiv

theorem pendant_core_adj {V : Type} (G : SimpleGraph V) (v : Fin 4 → V)
    (hv : Function.Injective v)
    (hN : ∀ i : Fin 4, 0 < i.val → ∀ w : V,
      G.Adj (v i) w ↔ ∃ j : Fin 4,
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ w = v j)
    (u : PendantCore v) (j : Fin 3) :
    G.Adj u.val (v j.succ) ↔ u = pendantRoot v hv ∧ j = 0 := by
  rw [G.adj_comm, hN j.succ (by simp only [Fin.val_succ]; omega)]
  constructor
  · rintro ⟨k, hk, hu⟩
    have hk0 : k.val = 0 := by
      by_contra hzero
      let l : Fin 3 := ⟨k.val-1, by omega⟩
      have hl : l.succ = k := by
        apply Fin.ext
        dsimp [l]
        omega
      exact u.property l (hu.trans (congrArg v hl.symm))
    have hk' : k = 0 := Fin.ext hk0
    subst k
    have hj : j = 0 := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_zero] at hk
      omega
    exact ⟨Subtype.ext hu, hj⟩
  · rintro ⟨hu, hj⟩
    subst u
    subst j
    exact ⟨0, Or.inr rfl, rfl⟩
#print axioms Paper7BMS.pendant_core_adj

theorem pendant_terminal_adj {V : Type} (G : SimpleGraph V) (v : Fin 4 → V)
    (hv : Function.Injective v)
    (hN : ∀ i : Fin 4, 0 < i.val → ∀ w : V,
      G.Adj (v i) w ↔ ∃ j : Fin 4,
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ w = v j)
    (i j : Fin 3) :
    G.Adj (v i.succ) (v j.succ) ↔ i.val+1 = j.val ∨ j.val+1 = i.val := by
  rw [hN i.succ (by simp only [Fin.val_succ]; omega)]
  constructor
  · rintro ⟨k, hk, hvk⟩
    have h : j.succ = k := hv hvk
    subst k
    simp only [Fin.val_succ] at hk
    omega
  · intro h
    exact ⟨j.succ, by simp only [Fin.val_succ]; omega, rfl⟩
#print axioms Paper7BMS.pendant_terminal_adj

theorem pendant_adjacency_reindex {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : Fin 4 → V)
    (hv : Function.Injective v)
    (hN : ∀ i : Fin 4, 0 < i.val → ∀ w : V,
      G.Adj (v i) w ↔ ∃ j : Fin 4,
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ w = v j) :
    (G.adjMatrix ℝ).submatrix (pendantEquiv v hv) (pendantEquiv v hv) =
      wideMatrix ((G.adjMatrix ℝ).submatrix
        (Subtype.val : PendantCore v → V) Subtype.val) (pendantRoot v hv) := by
  let : DecidableEq (PendantCore v) :=
    inferInstanceAs (DecidableEq {u : V // ∀ j : Fin 3, u ≠ v j.succ})
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · change (G.adjMatrix ℝ) i.val (v j.succ) =
      terminalCoupling (pendantRoot v hv) i j
    rw [SimpleGraph.adjMatrix_apply]
    change (if G.Adj i.val (v j.succ) then (1 : ℝ) else 0) =
      (if i = pendantRoot v hv then if j = 0 then 1 else 0 else 0)
    simp only [pendant_core_adj G v hv hN i j]
    by_cases hi : i = pendantRoot v hv
    · rw [ite_eq_left hi]
      by_cases hj : j = 0
      · rw [ite_eq_left (And.intro hi hj), ite_eq_left hj]
      · rw [ite_eq_right (show ¬(i = pendantRoot v hv ∧ j = 0) from fun h => hj h.2), ite_eq_right hj]
    · rw [ite_eq_right (show ¬(i = pendantRoot v hv ∧ j = 0) from fun h => hi h.1), ite_eq_right hi]
  · change (G.adjMatrix ℝ) (v i.succ) j.val =
      terminalCoupling (pendantRoot v hv) j i
    rw [SimpleGraph.adjMatrix_apply]
    change (if G.Adj (v i.succ) j.val then (1 : ℝ) else 0) =
      (if j = pendantRoot v hv then if i = 0 then 1 else 0 else 0)
    have ha : G.Adj (v i.succ) j.val ↔ j = pendantRoot v hv ∧ i = 0 := by
      rw [G.adj_comm]
      exact pendant_core_adj G v hv hN j i
    simp only [ha]
    by_cases hj : j = pendantRoot v hv
    · rw [ite_eq_left hj]
      by_cases hi : i = 0
      · rw [ite_eq_left (And.intro hj hi), ite_eq_left hi]
      · rw [ite_eq_right (show ¬(j = pendantRoot v hv ∧ i = 0) from fun h => hi h.2), ite_eq_right hi]
    · rw [ite_eq_right (show ¬(j = pendantRoot v hv ∧ i = 0) from fun h => hj h.1), ite_eq_right hj]
  · change (G.adjMatrix ℝ) (v i.succ) (v j.succ) = terminalBlock i j
    rw [SimpleGraph.adjMatrix_apply]
    simp only [pendant_terminal_adj G v hv hN i j]
    fin_cases i <;> fin_cases j <;> norm_num [terminalBlock]
#print axioms Paper7BMS.pendant_adjacency_reindex

theorem pendant_eigs_eq_spec {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : Fin 4 → V)
    (hv : Function.Injective v)
    (hN : ∀ i : Fin 4, 0 < i.val → ∀ w : V,
      G.Adj (v i) w ↔ ∃ j : Fin 4,
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ w = v j) :
    eigs (wideMatrix ((G.adjMatrix ℝ).submatrix
      (Subtype.val : PendantCore v → V) Subtype.val) (pendantRoot v hv)) = spec G := by
  let : DecidableEq (PendantCore v) :=
    inferInstanceAs (DecidableEq {u : V // ∀ j : Fin 3, u ≠ v j.succ})
  let : Fintype (PendantCore v) :=
    inferInstanceAs (Fintype {u : V // ∀ j : Fin 3, u ≠ v j.succ})
  let e : PendantCore v ⊕ Fin 3 ≃ V := pendantEquiv v hv
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let M : Matrix (PendantCore v) (PendantCore v) ℝ :=
    A.submatrix (Subtype.val : PendantCore v → V) Subtype.val
  have hmat : A.submatrix e e = wideMatrix M (pendantRoot v hv) :=
    pendant_adjacency_reindex G v hv hN
  have hchar : (A.submatrix e e).charpoly = A.charpoly := by
    exact Matrix.charpoly_reindex (n := V) (m := PendantCore v ⊕ Fin 3)
      (R := ℝ) e.symm A
  have hwide : (wideMatrix M (pendantRoot v hv)).charpoly = A.charpoly :=
    (congrArg (fun B : Matrix (PendantCore v ⊕ Fin 3) (PendantCore v ⊕ Fin 3) ℝ =>
      B.charpoly) hmat).symm.trans hchar
  exact congrArg (fun p : Polynomial ℝ => p.roots) hwide
#print axioms Paper7BMS.pendant_eigs_eq_spec

theorem pendant_three_intervals {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : HasPendantPath G 3) :
    (∃ x ∈ spec G, 1 < x ∧ x ≤ rho) ∧
      (∃ x ∈ spec G, -rho ≤ x ∧ x < -1) := by
  obtain ⟨v, hv, _hedges, hN⟩ := h
  let : DecidableEq (PendantCore v) :=
    inferInstanceAs (DecidableEq {u : V // ∀ j : Fin 3, u ≠ v j.succ})
  let : Fintype (PendantCore v) :=
    inferInstanceAs (Fintype {u : V // ∀ j : Fin 3, u ≠ v j.succ})
  let M : Matrix (PendantCore v) (PendantCore v) ℝ :=
    (G.adjMatrix ℝ).submatrix (Subtype.val : PendantCore v → V) Subtype.val
  have hM : M.IsHermitian :=
    (G.isHermitian_adjMatrix ℝ).submatrix (Subtype.val : PendantCore v → V)
  have hp := wideMatrix_positive_interval (ι := PendantCore v) M (pendantRoot v hv) hM
  have hn := wideMatrix_negative_interval (ι := PendantCore v) M (pendantRoot v hv) hM
  have he : eigs (wideMatrix M (pendantRoot v hv)) = spec G :=
    pendant_eigs_eq_spec G v hv hN
  obtain ⟨x, hx, hxb⟩ := hp
  obtain ⟨y, hy, hyb⟩ := hn
  exact ⟨⟨x, he ▸ hx, hxb⟩, ⟨y, he ▸ hy, hyb⟩⟩
#print axioms Paper7BMS.pendant_three_intervals

theorem bms_general : BMSTheorem21General := by
  intro V _ _ G _ t ht h
  have hi := pendant_three_intervals G (hasPendantPath_tail_three G t ht h)
  exact ⟨hi.1, hi.2, sharp_positive_interval_not_integral G hi.1⟩
#print axioms Paper7BMS.bms_general

end Paper7BMS
