import Research.Backfill.Paper4.Challenge

/-! Complete finite four-point base: every connected simple graph on Fin 4.
Six arbitrary adjacency Booleans cover all graphs, proved by graph extensionality.
The 38 connected modes use actual-distance certificates; the other 26 use explicit cuts.
The distance-certificate argument is reproduced from the accepted HKOTriameter lemma
to avoid importing its unrelated concrete graph certificates. All data checks use
kernel reduction. Generation is not acceptance; compilation receipts are separate. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.DHFourPointBase
open BackfillPaper4 SimpleGraph

def edge (b0 b1 b2 b3 b4 b5 : Bool) (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1 ∧ b0 = true) ∨ (i = 0 ∧ j = 2 ∧ b1 = true) ∨
  (i = 0 ∧ j = 3 ∧ b2 = true) ∨ (i = 1 ∧ j = 2 ∧ b3 = true) ∨
  (i = 1 ∧ j = 3 ∧ b4 = true) ∨ (i = 2 ∧ j = 3 ∧ b5 = true)

def pattern (b0 b1 b2 b3 b4 b5 : Bool) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (edge b0 b1 b2 b3 b4 b5)

instance (b0 b1 b2 b3 b4 b5 : Bool) : DecidableRel (pattern b0 b1 b2 b3 b4 b5).Adj := by
  intro i j
  dsimp [pattern, SimpleGraph.fromRel, edge]
  infer_instance

theorem dist_eq_of_certificate {V : Type*} (G : SimpleGraph V) (D : V → V → ℕ)
    (hself : ∀ x, D x x = 0)
    (hzero : ∀ x y, D x y = 0 → x = y)
    (hstep : ∀ x y, D x y ≠ 0 → ∃ z, G.Adj x z ∧ D z y + 1 = D x y)
    (hlip : ∀ u v w, G.Adj u v → D u w ≤ D v w + 1) :
    ∀ x y, G.dist x y = D x y := by
  have hwalk : ∀ n : ℕ, ∀ x y, D x y = n → ∃ p : G.Walk x y, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro x y h
      obtain rfl := hzero x y h
      exact ⟨Walk.nil, rfl⟩
    | succ n ih =>
      intro x y h
      obtain ⟨z, hxz, hz⟩ := hstep x y (by omega)
      obtain ⟨p, hp⟩ := ih z y (by omega)
      exact ⟨Walk.cons hxz p, by simp [hp]⟩
  have hlow : ∀ x y (p : G.Walk x y), D x y ≤ p.length := by
    intro x y p
    induction p with
    | nil => simp [hself]
    | @cons u v w h p ih =>
      have := hlip u v w h
      simp only [Walk.length_cons]
      omega
  intro x y
  obtain ⟨p, hp⟩ := hwalk _ x y rfl
  apply le_antisymm
  · exact (SimpleGraph.dist_le p).trans hp.le
  · have hr : G.Reachable x y := ⟨p⟩
    obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    exact hq ▸ hlow x y q

theorem cut_not_connected {V : Type*} (G : SimpleGraph V) (C : Finset V)
    (ha : C.Nonempty) (hb : ∃ y, y ∉ C)
    (hsep : ∀ x ∈ C, ∀ y, y ∉ C → ¬ G.Adj x y) : ¬ G.Connected := by
  intro hc
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hclosed : ∀ {x y : V}, G.Adj x y → x ∈ C → y ∈ C := by
    intro x y hxy hx
    by_contra hy
    exact hsep x hx y hy hxy
  have hwalk : ∀ {x y : V}, G.Walk x y → x ∈ C → y ∈ C := by
    intro x y p
    induction p with
    | nil => exact fun hx => hx
    | @cons x y z hxy p ih => exact fun hx => ih (hclosed hxy hx)
  obtain ⟨p⟩ := hc a b
  exact hb (hwalk p ha)

lemma mode_00 : (pattern false false false false false false).Connected → Challenge.FourPointBM (pattern false false false false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false false false false) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_01 : (pattern true false false false false false).Connected → Challenge.FourPointBM (pattern true false false false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false false false false false) ({0, 1} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_02 : (pattern false true false false false false).Connected → Challenge.FourPointBM (pattern false true false false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true false false false false) ({0, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_03 : (pattern true true false false false false).Connected → Challenge.FourPointBM (pattern true true false false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true true false false false false) ({0, 1, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_04 : (pattern false false true false false false).Connected → Challenge.FourPointBM (pattern false false true false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false true false false false) ({0, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_05 : (pattern true false true false false false).Connected → Challenge.FourPointBM (pattern true false true false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false true false false false) ({0, 1, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_06 : (pattern false true true false false false).Connected → Challenge.FourPointBM (pattern false true true false false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true true false false false) ({0, 2, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D07 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 2, 2], [1, 2, 0, 2], [1, 2, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_07 : (pattern true true true false false false).Connected → Challenge.FourPointBM (pattern true true true false false false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true false false false).dist x y = D07 x y :=
    dist_eq_of_certificate (pattern true true true false false false) D07
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_08 : (pattern false false false true false false).Connected → Challenge.FourPointBM (pattern false false false true false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false true false false) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_09 : (pattern true false false true false false).Connected → Challenge.FourPointBM (pattern true false false true false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false false true false false) ({0, 1, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_10 : (pattern false true false true false false).Connected → Challenge.FourPointBM (pattern false true false true false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true false true false false) ({0, 1, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_11 : (pattern true true false true false false).Connected → Challenge.FourPointBM (pattern true true false true false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true true false true false false) ({0, 1, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_12 : (pattern false false true true false false).Connected → Challenge.FourPointBM (pattern false false true true false false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false true true false false) ({0, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D13 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 1, 2], [2, 1, 0, 3], [1, 2, 3, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_13 : (pattern true false true true false false).Connected → Challenge.FourPointBM (pattern true false true true false false) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true true false false).dist x y = D13 x y :=
    dist_eq_of_certificate (pattern true false true true false false) D13
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D14 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 1, 3], [1, 1, 0, 2], [1, 3, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_14 : (pattern false true true true false false).Connected → Challenge.FourPointBM (pattern false true true true false false) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true true false false).dist x y = D14 x y :=
    dist_eq_of_certificate (pattern false true true true false false) D14
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D15 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 1, 2], [1, 1, 0, 2], [1, 2, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_15 : (pattern true true true true false false).Connected → Challenge.FourPointBM (pattern true true true true false false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true true false false).dist x y = D15 x y :=
    dist_eq_of_certificate (pattern true true true true false false) D15
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_16 : (pattern false false false false true false).Connected → Challenge.FourPointBM (pattern false false false false true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false false true false) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_17 : (pattern true false false false true false).Connected → Challenge.FourPointBM (pattern true false false false true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false false false true false) ({0, 1, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_18 : (pattern false true false false true false).Connected → Challenge.FourPointBM (pattern false true false false true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true false false true false) ({0, 2} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D19 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 2, 1], [1, 2, 0, 3], [2, 1, 3, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_19 : (pattern true true false false true false).Connected → Challenge.FourPointBM (pattern true true false false true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false false true false).dist x y = D19 x y :=
    dist_eq_of_certificate (pattern true true false false true false) D19
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_20 : (pattern false false true false true false).Connected → Challenge.FourPointBM (pattern false false true false true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false true false true false) ({0, 1, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_21 : (pattern true false true false true false).Connected → Challenge.FourPointBM (pattern true false true false true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false true false true false) ({0, 1, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D22 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 3, 1], [1, 3, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_22 : (pattern false true true false true false).Connected → Challenge.FourPointBM (pattern false true true false true false) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true false true false).dist x y = D22 x y :=
    dist_eq_of_certificate (pattern false true true false true false) D22
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D23 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 2, 1], [1, 2, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_23 : (pattern true true true false true false).Connected → Challenge.FourPointBM (pattern true true true false true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true false true false).dist x y = D23 x y :=
    dist_eq_of_certificate (pattern true true true false true false) D23
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_24 : (pattern false false false true true false).Connected → Challenge.FourPointBM (pattern false false false true true false) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false true true false) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D25 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 2], [1, 0, 1, 1], [2, 1, 0, 2], [2, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_25 : (pattern true false false true true false).Connected → Challenge.FourPointBM (pattern true false false true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true false false true true false).dist x y = D25 x y :=
    dist_eq_of_certificate (pattern true false false true true false) D25
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D26 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 3], [2, 0, 1, 1], [1, 1, 0, 2], [3, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_26 : (pattern false true false true true false).Connected → Challenge.FourPointBM (pattern false true false true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern false true false true true false).dist x y = D26 x y :=
    dist_eq_of_certificate (pattern false true false true true false) D26
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D27 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 1, 1], [1, 1, 0, 2], [2, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_27 : (pattern true true false true true false).Connected → Challenge.FourPointBM (pattern true true false true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false true true false).dist x y = D27 x y :=
    dist_eq_of_certificate (pattern true true false true true false) D27
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D28 (i j : Fin 4) : ℕ :=
  (([[0, 2, 3, 1], [2, 0, 1, 1], [3, 1, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_28 : (pattern false false true true true false).Connected → Challenge.FourPointBM (pattern false false true true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern false false true true true false).dist x y = D28 x y :=
    dist_eq_of_certificate (pattern false false true true true false) D28
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D29 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 1, 1], [2, 1, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_29 : (pattern true false true true true false).Connected → Challenge.FourPointBM (pattern true false true true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true true true false).dist x y = D29 x y :=
    dist_eq_of_certificate (pattern true false true true true false) D29
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D30 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 1, 1], [1, 1, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_30 : (pattern false true true true true false).Connected → Challenge.FourPointBM (pattern false true true true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true true true false).dist x y = D30 x y :=
    dist_eq_of_certificate (pattern false true true true true false) D30
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D31 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 2], [1, 1, 2, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_31 : (pattern true true true true true false).Connected → Challenge.FourPointBM (pattern true true true true true false) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true true true false).dist x y = D31 x y :=
    dist_eq_of_certificate (pattern true true true true true false) D31
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_32 : (pattern false false false false false true).Connected → Challenge.FourPointBM (pattern false false false false false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false false false true) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_33 : (pattern true false false false false true).Connected → Challenge.FourPointBM (pattern true false false false false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern true false false false false true) ({0, 1} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

lemma mode_34 : (pattern false true false false false true).Connected → Challenge.FourPointBM (pattern false true false false false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true false false false true) ({0, 2, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D35 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 2, 3], [1, 2, 0, 1], [2, 3, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_35 : (pattern true true false false false true).Connected → Challenge.FourPointBM (pattern true true false false false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false false false true).dist x y = D35 x y :=
    dist_eq_of_certificate (pattern true true false false false true) D35
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_36 : (pattern false false true false false true).Connected → Challenge.FourPointBM (pattern false false true false false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false true false false true) ({0, 2, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D37 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 3, 2], [2, 3, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_37 : (pattern true false true false false true).Connected → Challenge.FourPointBM (pattern true false true false false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true false false true).dist x y = D37 x y :=
    dist_eq_of_certificate (pattern true false true false false true) D37
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_38 : (pattern false true true false false true).Connected → Challenge.FourPointBM (pattern false true true false false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false true true false false true) ({0, 2, 3} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D39 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 2, 2], [1, 2, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_39 : (pattern true true true false false true).Connected → Challenge.FourPointBM (pattern true true true false false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true false false true).dist x y = D39 x y :=
    dist_eq_of_certificate (pattern true true true false false true) D39
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_40 : (pattern false false false true false true).Connected → Challenge.FourPointBM (pattern false false false true false true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false true false true) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D41 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 3], [1, 0, 1, 2], [2, 1, 0, 1], [3, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_41 : (pattern true false false true false true).Connected → Challenge.FourPointBM (pattern true false false true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false false true false true).dist x y = D41 x y :=
    dist_eq_of_certificate (pattern true false false true false true) D41
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D42 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 2], [2, 0, 1, 2], [1, 1, 0, 1], [2, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_42 : (pattern false true false true false true).Connected → Challenge.FourPointBM (pattern false true false true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true false true false true).dist x y = D42 x y :=
    dist_eq_of_certificate (pattern false true false true false true) D42
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D43 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 1, 2], [1, 1, 0, 1], [2, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_43 : (pattern true true false true false true).Connected → Challenge.FourPointBM (pattern true true false true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false true false true).dist x y = D43 x y :=
    dist_eq_of_certificate (pattern true true false true false true) D43
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D44 (i j : Fin 4) : ℕ :=
  (([[0, 3, 2, 1], [3, 0, 1, 2], [2, 1, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_44 : (pattern false false true true false true).Connected → Challenge.FourPointBM (pattern false false true true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern false false true true false true).dist x y = D44 x y :=
    dist_eq_of_certificate (pattern false false true true false true) D44
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D45 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 1, 2], [2, 1, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_45 : (pattern true false true true false true).Connected → Challenge.FourPointBM (pattern true false true true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true true false true).dist x y = D45 x y :=
    dist_eq_of_certificate (pattern true false true true false true) D45
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D46 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 1, 2], [1, 1, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_46 : (pattern false true true true false true).Connected → Challenge.FourPointBM (pattern false true true true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true true false true).dist x y = D46 x y :=
    dist_eq_of_certificate (pattern false true true true false true) D46
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D47 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 1, 2], [1, 1, 0, 1], [1, 2, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_47 : (pattern true true true true false true).Connected → Challenge.FourPointBM (pattern true true true true false true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true true false true).dist x y = D47 x y :=
    dist_eq_of_certificate (pattern true true true true false true) D47
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_48 : (pattern false false false false true true).Connected → Challenge.FourPointBM (pattern false false false false true true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false false true true) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D49 (i j : Fin 4) : ℕ :=
  (([[0, 1, 3, 2], [1, 0, 2, 1], [3, 2, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_49 : (pattern true false false false true true).Connected → Challenge.FourPointBM (pattern true false false false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false false false true true).dist x y = D49 x y :=
    dist_eq_of_certificate (pattern true false false false true true) D49
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D50 (i j : Fin 4) : ℕ :=
  (([[0, 3, 1, 2], [3, 0, 2, 1], [1, 2, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_50 : (pattern false true false false true true).Connected → Challenge.FourPointBM (pattern false true false false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true false false true true).dist x y = D50 x y :=
    dist_eq_of_certificate (pattern false true false false true true) D50
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D51 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 2, 1], [1, 2, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_51 : (pattern true true false false true true).Connected → Challenge.FourPointBM (pattern true true false false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false false true true).dist x y = D51 x y :=
    dist_eq_of_certificate (pattern true true false false true true) D51
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D52 (i j : Fin 4) : ℕ :=
  (([[0, 2, 2, 1], [2, 0, 2, 1], [2, 2, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_52 : (pattern false false true false true true).Connected → Challenge.FourPointBM (pattern false false true false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false false true false true true).dist x y = D52 x y :=
    dist_eq_of_certificate (pattern false false true false true true) D52
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D53 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 2, 1], [2, 2, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_53 : (pattern true false true false true true).Connected → Challenge.FourPointBM (pattern true false true false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true false true true).dist x y = D53 x y :=
    dist_eq_of_certificate (pattern true false true false true true) D53
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D54 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 2, 1], [1, 2, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_54 : (pattern false true true false true true).Connected → Challenge.FourPointBM (pattern false true true false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true false true true).dist x y = D54 x y :=
    dist_eq_of_certificate (pattern false true true false true true) D54
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D55 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 2, 1], [1, 2, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_55 : (pattern true true true false true true).Connected → Challenge.FourPointBM (pattern true true true false true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true false true true).dist x y = D55 x y :=
    dist_eq_of_certificate (pattern true true true false true true) D55
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

lemma mode_56 : (pattern false false false true true true).Connected → Challenge.FourPointBM (pattern false false false true true true) := by
  intro hc
  exact False.elim ((cut_not_connected
    (pattern false false false true true true) ({0} : Finset (Fin 4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) hc)

def D57 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 2], [1, 0, 1, 1], [2, 1, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_57 : (pattern true false false true true true).Connected → Challenge.FourPointBM (pattern true false false true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false false true true true).dist x y = D57 x y :=
    dist_eq_of_certificate (pattern true false false true true true) D57
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D58 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 2], [2, 0, 1, 1], [1, 1, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_58 : (pattern false true false true true true).Connected → Challenge.FourPointBM (pattern false true false true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true false true true true).dist x y = D58 x y :=
    dist_eq_of_certificate (pattern false true false true true true) D58
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D59 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 2], [1, 0, 1, 1], [1, 1, 0, 1], [2, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_59 : (pattern true true false true true true).Connected → Challenge.FourPointBM (pattern true true false true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true false true true true).dist x y = D59 x y :=
    dist_eq_of_certificate (pattern true true false true true true) D59
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D60 (i j : Fin 4) : ℕ :=
  (([[0, 2, 2, 1], [2, 0, 1, 1], [2, 1, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_60 : (pattern false false true true true true).Connected → Challenge.FourPointBM (pattern false false true true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false false true true true true).dist x y = D60 x y :=
    dist_eq_of_certificate (pattern false false true true true true) D60
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D61 (i j : Fin 4) : ℕ :=
  (([[0, 1, 2, 1], [1, 0, 1, 1], [2, 1, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_61 : (pattern true false true true true true).Connected → Challenge.FourPointBM (pattern true false true true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true false true true true true).dist x y = D61 x y :=
    dist_eq_of_certificate (pattern true false true true true true) D61
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D62 (i j : Fin 4) : ℕ :=
  (([[0, 2, 1, 1], [2, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_62 : (pattern false true true true true true).Connected → Challenge.FourPointBM (pattern false true true true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern false true true true true true).dist x y = D62 x y :=
    dist_eq_of_certificate (pattern false true true true true true) D62
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

def D63 (i j : Fin 4) : ℕ :=
  (([[0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0]] : List (List ℕ)).getD i.val []).getD j.val 0

lemma mode_63 : (pattern true true true true true true).Connected → Challenge.FourPointBM (pattern true true true true true true) := by
  intro _hc
  have hd : ∀ x y, (pattern true true true true true true).dist x y = D63 x y :=
    dist_eq_of_certificate (pattern true true true true true true) D63
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro u v w x
  simp only [hd]
  unfold Challenge.FP
  revert u v w x
  decide +kernel

theorem all_patterns (b0 b1 b2 b3 b4 b5 : Bool) :
    (pattern b0 b1 b2 b3 b4 b5).Connected → Challenge.FourPointBM (pattern b0 b1 b2 b3 b4 b5) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5
  · exact mode_00
  · exact mode_32
  · exact mode_16
  · exact mode_48
  · exact mode_08
  · exact mode_40
  · exact mode_24
  · exact mode_56
  · exact mode_04
  · exact mode_36
  · exact mode_20
  · exact mode_52
  · exact mode_12
  · exact mode_44
  · exact mode_28
  · exact mode_60
  · exact mode_02
  · exact mode_34
  · exact mode_18
  · exact mode_50
  · exact mode_10
  · exact mode_42
  · exact mode_26
  · exact mode_58
  · exact mode_06
  · exact mode_38
  · exact mode_22
  · exact mode_54
  · exact mode_14
  · exact mode_46
  · exact mode_30
  · exact mode_62
  · exact mode_01
  · exact mode_33
  · exact mode_17
  · exact mode_49
  · exact mode_09
  · exact mode_41
  · exact mode_25
  · exact mode_57
  · exact mode_05
  · exact mode_37
  · exact mode_21
  · exact mode_53
  · exact mode_13
  · exact mode_45
  · exact mode_29
  · exact mode_61
  · exact mode_03
  · exact mode_35
  · exact mode_19
  · exact mode_51
  · exact mode_11
  · exact mode_43
  · exact mode_27
  · exact mode_59
  · exact mode_07
  · exact mode_39
  · exact mode_23
  · exact mode_55
  · exact mode_15
  · exact mode_47
  · exact mode_31
  · exact mode_63

theorem encode_graph (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    G = pattern (decide (G.Adj 0 1)) (decide (G.Adj 0 2)) (decide (G.Adj 0 3))
      (decide (G.Adj 1 2)) (decide (G.Adj 1 3)) (decide (G.Adj 2 3)) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pattern, SimpleGraph.fromRel, edge, G.adj_comm]
  all_goals exact G.adj_comm _ _

theorem fin4_fourPoint (G : SimpleGraph (Fin 4)) (hc : G.Connected) :
    Challenge.FourPointBM G := by
  classical
  have hG := encode_graph G
  rw [hG] at hc ⊢
  exact all_patterns _ _ _ _ _ _ hc

#print axioms fin4_fourPoint
end CodexPaper4.DHFourPointBase
