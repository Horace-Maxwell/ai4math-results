import Research.Backfill.Paper8.Proof.Tree.Metric
import Research.Backfill.Paper8.Proof.Basic

/-!
# Paper 8, `TreeStructure`: the trees of diameter at most 4 are the trees `T(a)`

Given a tree `G` and a vertex `c` within distance `2` of every vertex, the branches are the
neighbours `v_i` of `c` (enumerated by `Fin k`) and the leaves of branch `i` are the neighbours of
`v_i` at distance `2` from `c` (enumerated by `Fin (a i)`). The map `phi : T(a) → G` is a graph
isomorphism: parent uniqueness gives injectivity and `d(c, w) ≤ 2` surjectivity. Conversely `T(a)`
is connected with `1 + k + ∑ a_i` vertices and `k + ∑ a_i` edges (degree sum), hence a tree, and
every vertex is within distance `2` of the centre, so `ediam ≤ 4`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge SimpleGraph

namespace P8Tree

section Build

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V)

/-- The neighbours of `c`. -/
abbrev Nbr : Type _ := {y : V // G.Adj c y}

/-- The children of `y`: its neighbours at distance `2` from `c`. -/
abbrev Kids (y : V) : Type _ := {w : V // G.Adj y w ∧ G.dist c w = 2}

/-- The number of branches (the degree of `c`). -/
noncomputable def kOf : ℕ := Fintype.card (Nbr G c)

/-- An enumeration of the neighbours of `c`. -/
noncomputable def eN : Fin (kOf G c) ≃ Nbr G c := (Fintype.equivFin (Nbr G c)).symm

/-- The branch sizes: the number of children of each neighbour of `c`. -/
noncomputable def aOf (i : Fin (kOf G c)) : ℕ := Fintype.card (Kids G c (eN G c i).1)

/-- An enumeration of the children of the `i`-th neighbour of `c`. -/
noncomputable def eK (i : Fin (kOf G c)) : Fin (aOf G c i) ≃ Kids G c (eN G c i).1 :=
  (Fintype.equivFin (Kids G c (eN G c i).1)).symm

/-- The map `T(a) → G`. -/
noncomputable def phi : TV (aOf G c) → V
  | none => c
  | some ⟨i, none⟩ => (eN G c i).1
  | some ⟨i, some j⟩ => (eK G c i j).1

@[simp] theorem phi_none : phi G c none = c := rfl

@[simp] theorem phi_v (i : Fin (kOf G c)) : phi G c (some ⟨i, none⟩) = (eN G c i).1 := rfl

@[simp] theorem phi_l (i : Fin (kOf G c)) (j : Fin (aOf G c i)) :
    phi G c (some ⟨i, some j⟩) = (eK G c i j).1 := rfl

variable {G c}

theorem dist_eN (i : Fin (kOf G c)) : G.dist c (eN G c i).1 = 1 :=
  dist_eq_one_iff_adj.2 (eN G c i).2

theorem dist_eK (i : Fin (kOf G c)) (j : Fin (aOf G c i)) : G.dist c (eK G c i j).1 = 2 :=
  (eK G c i j).2.2

theorem adj_eN_eK (i : Fin (kOf G c)) (j : Fin (aOf G c i)) :
    G.Adj (eN G c i).1 (eK G c i j).1 :=
  (eK G c i j).2.1

/-- A vertex at distance `2` from `c` is adjacent to only one neighbour of `c`. -/
theorem eN_eq_of_adj (hG : G.IsTree) {i i' : Fin (kOf G c)} {w : V} (h : G.Adj (eN G c i).1 w)
    (h' : G.Adj (eN G c i').1 w) (hw : G.dist c w = 2) : i = i' := by
  have := eq_of_adj_of_dist_succ (c := c) hG h h' (by rw [hw, dist_eN]) (by rw [hw, dist_eN])
  exact (eN G c).injective (Subtype.ext this)

theorem not_adj_c_eK (i : Fin (kOf G c)) (j : Fin (aOf G c i)) : ¬ G.Adj c (eK G c i j).1 := by
  intro h
  have := dist_eq_one_iff_adj.2 h
  rw [dist_eK] at this
  omega

theorem not_adj_eN_eN (hG : G.IsTree) (i i' : Fin (kOf G c)) :
    ¬ G.Adj (eN G c i).1 (eN G c i').1 := fun h =>
  hG.dist_ne_of_adj c h (by rw [dist_eN, dist_eN])

theorem not_adj_eK_eK (hG : G.IsTree) (i : Fin (kOf G c)) (j : Fin (aOf G c i))
    (i' : Fin (kOf G c)) (j' : Fin (aOf G c i')) : ¬ G.Adj (eK G c i j).1 (eK G c i' j').1 :=
  fun h => hG.dist_ne_of_adj c h (by rw [dist_eK, dist_eK])

theorem adj_eN_eK_iff (hG : G.IsTree) (i i' : Fin (kOf G c)) (j : Fin (aOf G c i')) :
    G.Adj (eN G c i).1 (eK G c i' j).1 ↔ i = i' := by
  constructor
  · intro h
    exact eN_eq_of_adj hG h (adj_eN_eK i' j) (dist_eK i' j)
  · rintro rfl
    exact adj_eN_eK i j

theorem phi_injective (hG : G.IsTree) : Function.Injective (phi G c) := by
  intro x y hxy
  have hd := congrArg (G.dist c) hxy
  rcases x with _ | ⟨i, _ | j⟩ <;> rcases y with _ | ⟨i', _ | j'⟩ <;>
    simp only [phi_none, phi_v, phi_l, dist_self, dist_eN, dist_eK] at hd hxy <;>
    first
    | rfl
    | (exfalso; omega)
    | skip
  · have : i = i' := (eN G c).injective (Subtype.ext hxy)
    subst this
    rfl
  · have hi : i = i' :=
      eN_eq_of_adj hG (adj_eN_eK i j) (by rw [hxy]; exact adj_eN_eK i' j') (dist_eK i j)
    subst hi
    have : j = j' := (eK G c i).injective (Subtype.ext hxy)
    subst this
    rfl

theorem phi_surjective (hG : G.IsTree) (hc : ∀ w, G.dist c w ≤ 2) :
    Function.Surjective (phi G c) := by
  intro w
  have hw := hc w
  obtain h | h | h : G.dist c w = 0 ∨ G.dist c w = 1 ∨ G.dist c w = 2 := by omega
  · exact ⟨none, by rw [phi_none]; exact hG.connected.dist_eq_zero_iff.1 h⟩
  · have hadj : G.Adj c w := dist_eq_one_iff_adj.1 h
    refine ⟨some ⟨(eN G c).symm ⟨w, hadj⟩, none⟩, ?_⟩
    rw [phi_v, Equiv.apply_symm_apply]
  · have he : G.edist c w = 2 := by
      have := (hG.connected c w).coe_dist_eq_edist
      rw [h] at this
      exact_mod_cast this.symm
    obtain ⟨-, -, ⟨y, hy⟩⟩ := edist_eq_two_iff.1 he
    rw [mem_commonNeighbors] at hy
    obtain ⟨i, hi⟩ : ∃ i, (eN G c i).1 = y :=
      ⟨(eN G c).symm ⟨y, hy.1⟩, by rw [Equiv.apply_symm_apply]⟩
    have hk : G.Adj (eN G c i).1 w ∧ G.dist c w = 2 := ⟨by rw [hi]; exact hy.2.symm, h⟩
    refine ⟨some ⟨i, some ((eK G c i).symm ⟨w, hk⟩)⟩, ?_⟩
    rw [phi_l, Equiv.apply_symm_apply]

theorem phi_adj (hG : G.IsTree) (x y : TV (aOf G c)) :
    G.Adj (phi G c x) (phi G c y) ↔ (treeT (aOf G c)).Adj x y := by
  rcases x with _ | ⟨i, _ | j⟩ <;> rcases y with _ | ⟨i', _ | j'⟩
  · simp
  · simp only [phi_none, phi_v, P8Basic.adj_c_v, iff_true]
    exact (eN G c i').2
  · simp only [phi_none, phi_l, P8Basic.adj_c_l, iff_false]
    exact not_adj_c_eK i' j'
  · simp only [phi_none, phi_v, P8Basic.adj_v_c, iff_true]
    exact (eN G c i).2.symm
  · simp only [phi_v, P8Basic.adj_v_v, iff_false]
    exact not_adj_eN_eN hG i i'
  · simp only [phi_v, phi_l, P8Basic.adj_v_l]
    exact adj_eN_eK_iff hG i i' j'
  · simp only [phi_none, phi_l, P8Basic.adj_l_c, iff_false]
    exact fun h => not_adj_c_eK i j h.symm
  · simp only [phi_v, phi_l, P8Basic.adj_l_v]
    rw [G.adj_comm]
    exact adj_eN_eK_iff hG i' i j
  · simp only [phi_l, P8Basic.adj_l_l, iff_false]
    exact not_adj_eK_eK hG i j i' j'

/-- The isomorphism `T(a) ≃g G` built from a vertex `c` within distance `2` of every vertex. -/
noncomputable def isoOf (hG : G.IsTree) (hc : ∀ w, G.dist c w ≤ 2) : treeT (aOf G c) ≃g G where
  toEquiv := Equiv.ofBijective (phi G c) ⟨phi_injective hG, phi_surjective hG hc⟩
  map_rel_iff' := fun {x y} => phi_adj hG x y

end Build

/-- First half of `TreeStructure`. -/
theorem treeStructure_fwd (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (hT : T.IsTree) (hd : T.ediam ≤ 4) (h3 : 3 ≤ Fintype.card V) :
    ∃ (k : ℕ) (a : Fin k → ℕ), 0 < k ∧ Nonempty (T ≃g treeT a) := by
  classical
  obtain ⟨c, hc⟩ := exists_centre_of_ediam hT hd
  refine ⟨kOf T c, aOf T c, ?_, ⟨(isoOf hT hc).symm⟩⟩
  have hcard := Fintype.card_congr (isoOf hT hc).toEquiv
  rw [P8Basic.card_TV] at hcard
  by_contra h0
  have hk : kOf T c = 0 := by omega
  have hsum : ∑ i, aOf T c i = 0 :=
    Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
  omega

section Converse

variable {k : ℕ} (a : Fin k → ℕ)

theorem treeT_reach (x : TV a) : (treeT a).Reachable none x := by
  rcases x with _ | ⟨i, _ | j⟩
  · exact Reachable.refl _
  · exact (P8Basic.adj_c_v a i).reachable
  · exact (P8Basic.adj_c_v a i).reachable.trans ((P8Basic.adj_v_l a i i j).2 rfl).reachable

theorem treeT_connected : (treeT a).Connected :=
  ⟨fun x y => (treeT_reach a x).symm.trans (treeT_reach a y)⟩

theorem treeT_degree (x : TV a) :
    (treeT a).degree x = ∑ y, if (treeT a).Adj x y then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

theorem treeT_degree_c : (treeT a).degree none = k := by
  rw [treeT_degree, P8Basic.sum_TV]
  simp

theorem treeT_degree_v (i : Fin k) : (treeT a).degree (some ⟨i, none⟩) = 1 + a i := by
  rw [treeT_degree, P8Basic.sum_TV]
  have inner : ∀ i' : Fin k,
      (∑ j : Fin (a i'), if (treeT a).Adj (some ⟨i, none⟩) (some ⟨i', some j⟩) then 1 else 0) =
        if i = i' then a i' else 0 := by
    intro i'
    by_cases h : i = i'
    · subst h
      simp
    · simp [h]
  simp only [inner, P8Basic.adj_v_c, P8Basic.adj_v_v, ite_true, ite_false, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ]

theorem treeT_degree_l (i : Fin k) (j : Fin (a i)) : (treeT a).degree (some ⟨i, some j⟩) = 1 := by
  rw [treeT_degree, P8Basic.sum_TV]
  simp only [P8Basic.adj_l_c, P8Basic.adj_l_v, P8Basic.adj_l_l, ite_false, zero_add,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    simp [hi']
  · simp

theorem treeT_card_edges : (treeT a).edgeFinset.card = k + ∑ i, a i := by
  have h := (treeT a).sum_degrees_eq_twice_card_edges
  rw [P8Basic.sum_TV] at h
  simp only [treeT_degree_c, treeT_degree_v, treeT_degree_l, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_add_distrib] at h
  omega

theorem treeT_isTree : (treeT a).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨treeT_connected a, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, treeT_card_edges,
    P8Basic.card_TV]
  omega

theorem treeT_edist_c (x : TV a) : (treeT a).edist none x ≤ 2 := by
  rcases x with _ | ⟨i, _ | j⟩
  · simp
  · calc (treeT a).edist none (some ⟨i, none⟩)
        ≤ (Walk.cons (P8Basic.adj_c_v a i) Walk.nil).length := edist_le _
      _ ≤ 2 := by norm_num
  · calc (treeT a).edist none (some ⟨i, some j⟩)
        ≤ (Walk.cons (P8Basic.adj_c_v a i)
            (Walk.cons ((P8Basic.adj_v_l a i i j).2 rfl) Walk.nil)).length := edist_le _
      _ ≤ 2 := by norm_num

theorem treeT_ediam : (treeT a).ediam ≤ 4 := by
  rw [ediam_le_iff]
  intro x y
  calc (treeT a).edist x y ≤ (treeT a).edist x none + (treeT a).edist none y :=
        SimpleGraph.edist_triangle
    _ = (treeT a).edist none x + (treeT a).edist none y := by rw [edist_comm]
    _ ≤ 2 + 2 := add_le_add (treeT_edist_c a x) (treeT_edist_c a y)
    _ = 4 := by norm_num

end Converse

/-- The statement `TreeStructure`. -/
theorem treeStructure : TreeStructure :=
  ⟨fun V _ _ T hT hd h3 => treeStructure_fwd V T hT hd h3,
    fun _ a _ => ⟨treeT_isTree a, treeT_ediam a, P8Basic.card_TV a⟩⟩

end P8Tree
