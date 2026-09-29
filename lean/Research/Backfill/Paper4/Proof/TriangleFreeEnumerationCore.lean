import Research.Backfill.Paper4.Challenge

/-! Semantic coverage of finite connected triangle-free graphs by one-vertex extensions.
LayerStep is the explicit finite certificate obligation, not an extra assumption on any graph
in the frozen target. The data module must discharge all six concrete layer obligations.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.TriangleFreeEnumerationCore
open BackfillPaper4

def codeGraph (n c : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ c.testBit
    (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa only [Nat.max_comm, Nat.min_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance codeGraphDecidable (n c : ℕ) : DecidableRel (codeGraph n c).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ c.testBit
    (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)))

def optionAug {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Option (Fin n)) where
  Adj x y := match x, y with
    | none, none => False
    | none, some j => j ∈ S
    | some i, none => i ∈ S
    | some i, some j => H.Adj i j
  symm := ⟨by
    rintro (_ | i) (_ | j) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | i) h
    · exact h
    · exact H.irrefl h⟩

instance optionAugDecidable {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel H.Adj] : DecidableRel (optionAug H S).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [optionAug] <;> infer_instance

/-- Old labels retain their values and the newly added vertex has label n. -/
def augment {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin (n + 1)) :=
  (optionAug H S).comap (finSuccEquiv' (Fin.last n))

instance augmentDecidable {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel H.Adj] : DecidableRel (augment H S).Adj := by
  unfold augment
  infer_instance

def augmentOptionIso {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    augment H S ≃g optionAug H S where
  toEquiv := finSuccEquiv' (Fin.last n)
  map_rel_iff' := by intro i j; rfl

def Covers {n m : ℕ} (L : Fin m → SimpleGraph (Fin n)) : Prop :=
  ∀ (W : Type) [Fintype W] (G : SimpleGraph W), Fintype.card W = n →
    G.Connected → G.CliqueFree 3 → ∃ i, Nonempty (G ≃g L i)

def LayerStep {n m k : ℕ} (L : Fin m → SimpleGraph (Fin n))
    (M : Fin k → SimpleGraph (Fin (n + 1))) : Prop :=
  ∀ i (S : Finset (Fin n)), S.Nonempty → (L i).IsIndepSet (S : Set (Fin n)) →
    ∃ j, Nonempty (augment (L i) S ≃g M j)

noncomputable def liftedNeighbors {V : Type*} {n : ℕ} (G : SimpleGraph V) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => G.Adj v (e.symm i).val)

theorem mem_liftedNeighbors {V : Type*} {n : ℕ} (G : SimpleGraph V) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) (i : Fin n) :
    i ∈ liftedNeighbors G v H e ↔ G.Adj v (e.symm i).val := by
  classical
  simp only [liftedNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def deletionOptionIso {V : Type*} {n : ℕ} (G : SimpleGraph V) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) :
    optionAug H (liftedNeighbors G v H e) ≃g G := by
  classical
  exact {
    toEquiv := (Equiv.optionCongr e.symm.toEquiv).trans (Equiv.optionSubtypeNe v)
    map_rel_iff' := by
      rintro (_ | i) (_ | j)
      · change G.Adj v v ↔ False
        simp only [SimpleGraph.irrefl, iff_self]
      · change G.Adj v (e.symm j).val ↔ j ∈ liftedNeighbors G v H e
        exact (mem_liftedNeighbors G v H e j).symm
      · change G.Adj (e.symm i).val v ↔ i ∈ liftedNeighbors G v H e
        exact (G.adj_comm _ _).trans (mem_liftedNeighbors G v H e i).symm
      · change G.Adj (e.symm i).val (e.symm j).val ↔ H.Adj i j
        exact e.symm.map_adj_iff }

noncomputable def augmentationIso {V : Type*} {n : ℕ} (G : SimpleGraph V) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) :
    augment H (liftedNeighbors G v H e) ≃g G :=
  (augmentOptionIso H (liftedNeighbors G v H e)).trans (deletionOptionIso G v H e)

theorem liftedNeighbors_nonempty {V : Type*} [Nontrivial V] {n : ℕ}
    (G : SimpleGraph V) (hc : G.Connected) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) :
    (liftedNeighbors G v H e).Nonempty := by
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨x, hvx⟩ := (hc v w).nonempty_neighborSet_left hw.symm
  let xx : ({v}ᶜ : Set V) := ⟨x, hvx.ne'⟩
  refine ⟨e xx, (mem_liftedNeighbors G v H e (e xx)).mpr ?_⟩
  simpa only [RelIso.symm_apply_apply, xx] using (show G.Adj v x from hvx)

theorem liftedNeighbors_independent {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (ht : G.CliqueFree 3) (v : V)
    (H : SimpleGraph (Fin n)) (e : G.induce {v}ᶜ ≃g H) :
    H.IsIndepSet (liftedNeighbors G v H e : Set (Fin n)) := by
  classical
  rw [SimpleGraph.isIndepSet_iff]
  intro i hi j hj _ hij
  have hvi := (mem_liftedNeighbors G v H e i).mp hi
  have hvj := (mem_liftedNeighbors G v H e j).mp hj
  have hij' : G.Adj (e.symm i).val (e.symm j).val := e.symm.map_adj_iff.mpr hij
  exact ht _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hvi, hvj, hij'⟩)

theorem covers_one {m : ℕ} (L : Fin m → SimpleGraph (Fin 1)) (i : Fin m) : Covers L := by
  classical
  intro V _ G hcard _ _
  let e : V ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
  refine ⟨i, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro x y
  have hxy : x = y := e.injective (Subsingleton.elim _ _)
  subst y
  simp only [SimpleGraph.irrefl, iff_self]

theorem covers_succ {n m k : ℕ} (L : Fin m → SimpleGraph (Fin n))
    (M : Fin k → SimpleGraph (Fin (n + 1))) (hn : 1 ≤ n)
    (hL : Covers L) (hstep : LayerStep L M) : Covers M := by
  classical
  intro V _ G hcard hc ht
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := hc.exists_connected_induce_compl_singleton_of_finite_nontrivial
  have hsum : Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
    let e0 : ({v}ᶜ : Set V) ≃ {b : V // b ≠ v} := {
      toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
    have hop : Fintype.card {b : V // b ≠ v} + 1 = Fintype.card V := by
      simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe v)
    exact (congrArg (fun k : ℕ => k + 1) (Fintype.card_congr e0)).trans hop
  have hdel : Fintype.card ({v}ᶜ : Set V) = n := by omega
  have htri : (G.induce {v}ᶜ).CliqueFree 3 := by
    intro t hcl
    exact ht _ ((SimpleGraph.isNClique_induce_iff (G := G) {v}ᶜ t 3).mp hcl)
  obtain ⟨i, ⟨e⟩⟩ := hL ({v}ᶜ : Set V) (G.induce {v}ᶜ) hdel hv htri
  let S := liftedNeighbors G v (L i) e
  have hS : S.Nonempty := liftedNeighbors_nonempty G hc v (L i) e
  have hI : (L i).IsIndepSet (S : Set (Fin n)) := liftedNeighbors_independent G ht v (L i) e
  obtain ⟨j, ⟨f⟩⟩ := hstep i S hS hI
  exact ⟨j, ⟨(augmentationIso G v (L i) e).symm.trans f⟩⟩

theorem covers_through_seven (r : ℕ → ℕ)
    (L : ∀ n : ℕ, Fin (r n) → SimpleGraph (Fin n))
    (hbase : Covers (L 1))
    (hsteps : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → LayerStep (L n) (L (n + 1))) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 7 → Covers (L n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn h7
    cases n with
    | zero => omega
    | succ m =>
      by_cases hm : m = 0
      · subst m
        exact hbase
      · have hm1 : 1 ≤ m := by omega
        exact covers_succ (L m) (L (m + 1)) hm1
          (ih m (by omega) hm1 (by omega)) (hsteps m hm1 (by omega))

#print axioms covers_succ
#print axioms covers_through_seven

end CodexPaper4.TriangleFreeEnumerationCore
