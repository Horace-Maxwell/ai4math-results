import Research.Backfill.Paper8.Proof.Tree.Thm1

/-!
# Paper 8, the signature version of Theorem 1

Every signature `σ` of a tree (symmetric, `±1` on each edge) is a switching of the all-positive
one: `σ u v = t u * t v`, where `t v` is the product of `σ` along the path from a fixed root to `v`
(in a tree the path to a neighbour extends or shortens the path by one edge,
`IsAcyclic.path_concat`). Then `D_{st} (σ ∘ A) D_{st} = D_s A D_s`, so a good switching `s` of
`A(T)` (Theorem 1) gives the switching `s * t` of the signed tree.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge SimpleGraph Matrix

namespace P8Tree

section Signature

variable {V : Type*} {T : SimpleGraph V}

/-- The product of `σ` over the darts of a walk. -/
noncomputable def wsign (σ : V → V → ℝ) {u v : V} (p : T.Walk u v) : ℝ :=
  (p.darts.map fun d => σ d.fst d.snd).prod

theorem wsign_concat (σ : V → V → ℝ) {u v w : V} (p : T.Walk u v) (h : T.Adj v w) :
    wsign σ (p.concat h) = wsign σ p * σ v w := by
  simp [wsign, Walk.darts_concat, List.concat_eq_append]

theorem wsign_mul_self (σ : V → V → ℝ) (hσ1 : ∀ u v, T.Adj u v → σ u v = 1 ∨ σ u v = -1)
    {u v : V} (p : T.Walk u v) : wsign σ p * wsign σ p = 1 := by
  induction p with
  | nil => simp [wsign]
  | @cons x y z h q ih =>
    have e : wsign σ (Walk.cons h q) = σ x y * wsign σ q := by simp [wsign]
    have hxy : σ x y * σ x y = 1 := by
      rcases hσ1 x y h with h' | h' <;> simp [h']
    rw [e]
    calc σ x y * wsign σ q * (σ x y * wsign σ q)
        = (σ x y * σ x y) * (wsign σ q * wsign σ q) := by ring
      _ = 1 := by rw [hxy, ih, one_mul]

/-- Every signature of a tree is a switching of the all-positive signature. -/
theorem exists_switch_of_signature (hT : T.IsTree) (σ : V → V → ℝ)
    (hσ : ∀ u v, σ u v = σ v u) (hσ1 : ∀ u v, T.Adj u v → σ u v = 1 ∨ σ u v = -1) :
    ∃ t : V → ℝ, (∀ v, t v = 1 ∨ t v = -1) ∧ ∀ u v, T.Adj u v → σ u v = t u * t v := by
  obtain ⟨r⟩ := hT.connected.nonempty
  have hex : ∀ v, ∃ p : T.Walk r v, p.IsPath := fun v => by
    obtain ⟨p, hp, -⟩ := (hT.connected r v).exists_path_of_dist
    exact ⟨p, hp⟩
  choose P hP using hex
  have hsq : ∀ v, wsign σ (P v) * wsign σ (P v) = 1 := fun v => wsign_mul_self σ hσ1 (P v)
  have key : ∀ u v, T.Adj u v → u ∈ (P v).support →
      σ u v = wsign σ (P u) * wsign σ (P v) := by
    intro u v huv hmem
    have hPv : P v = (P u).concat huv := hT.isAcyclic.path_concat (hP u) (hP v) huv hmem
    rw [hPv, wsign_concat, ← mul_assoc, hsq u, one_mul]
  refine ⟨fun v => wsign σ (P v), fun v => mul_self_eq_one_iff.1 (hsq v), ?_⟩
  intro u v huv
  by_cases hmem : u ∈ (P v).support
  · exact key u v huv hmem
  · have hv : v ∈ (P u).support :=
      hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hP u) (hP v) huv hmem
    rw [hσ u v, key v u huv.symm hv, mul_comm]

end Signature

/-- Body of `Theorem1_signed` (statement file, version 2) from `Theorem1`. -/
theorem theorem1_signed_of (h : Theorem1) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → T.ediam ≤ 4 → IsEmpty (T ≃g (⊤ : SimpleGraph (Fin 2))) →
    ∀ σ : V → V → ℝ, (∀ u v, σ u v = σ v u) → (∀ u v, T.Adj u v → σ u v = 1 ∨ σ u v = -1) →
      ∃ s : V → ℝ, IsSwitching s ∧
        AllEigenvaluesMain (switchMatrix (Matrix.of fun u v => σ u v * T.adjMatrix ℝ u v) s) := by
  intro V _ _ T _ hT hd hK2 σ hσ hσ1
  obtain ⟨s, hs, hmain⟩ := h V T hT hd hK2
  obtain ⟨t, ht1, ht⟩ := exists_switch_of_signature hT σ hσ hσ1
  have htt : ∀ v, t v * t v = 1 := fun v => by
    rcases ht1 v with h' | h' <;> simp [h']
  refine ⟨fun v => s v * t v, ?_, ?_⟩
  · intro v
    rcases hs v with h1 | h1 <;> rcases ht1 v with h2 | h2 <;> simp [h1, h2]
  · have hM : switchMatrix (Matrix.of fun u v => σ u v * T.adjMatrix ℝ u v)
        (fun v => s v * t v) = switchMatrix (T.adjMatrix ℝ) s := by
      ext u v
      simp only [switchMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
      by_cases huv : T.Adj u v
      · simp only [adjMatrix_apply, huv, ite_true, mul_one]
        rw [ht u v huv]
        linear_combination (s u * s v * (t v * t v)) * htt u + (s u * s v) * htt v
      · simp [adjMatrix_apply, huv]
    rw [hM]
    exact hmain

/-- The signature version, with the hypotheses of `theorem1`. -/
theorem theorem1_signed (h21 : Lemma_2_1_good) (h53 : Prop_5_3) (h44 : Cor_4_4)
    (h54 : Lemma_5_4) (h55 : Prop_5_5) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → T.ediam ≤ 4 → IsEmpty (T ≃g (⊤ : SimpleGraph (Fin 2))) →
    ∀ σ : V → V → ℝ, (∀ u v, σ u v = σ v u) → (∀ u v, T.Adj u v → σ u v = 1 ∨ σ u v = -1) →
      ∃ s : V → ℝ, IsSwitching s ∧
        AllEigenvaluesMain (switchMatrix (Matrix.of fun u v => σ u v * T.adjMatrix ℝ u v) s) :=
  theorem1_signed_of (theorem1 h21 h53 h44 h54 h55)

end P8Tree
