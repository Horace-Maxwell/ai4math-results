import Research.Backfill.Paper7.PathSunPolynomial

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Classical

def interiorIndex (n : ℕ) (i : Fin n) : Fin (n+2) := ⟨i.val+1, by omega⟩
#print axioms Paper7Schwenk.interiorIndex

theorem interiorIndex_injective (n : ℕ) : Function.Injective (interiorIndex n) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  change i.val+1=j.val+1 at h
  omega
#print axioms Paper7Schwenk.interiorIndex_injective

theorem interiorIndex_ne_endpoints (n : ℕ) (i : Fin n) :
    interiorIndex n i ≠ 0 ∧ interiorIndex n i ≠ Fin.last (n+1) := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change i.val+1=0 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val+1=n+1 at hv
    omega
#print axioms Paper7Schwenk.interiorIndex_ne_endpoints

def endpointComplementEquiv (n : ℕ) (L : Fin (n+2) → List ℕ) :
    {z : SunV (n+2) L // z ∉
      ({Sum.inl 0, Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))} ≃
      Fin n ⊕ ArmV (n+2) L where
  toFun := fun z => by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl i =>
      have hi0 : i.val ≠ 0 := by
        intro h
        exact hz (Or.inl (congrArg Sum.inl (Fin.ext h)))
      have hil : i.val ≠ n+1 := by
        intro h
        exact hz (Or.inr (congrArg Sum.inl (Fin.ext h)))
      exact Sum.inl ⟨i.val-1, by omega⟩
    | inr a => exact Sum.inr a
  invFun := fun z => by
    cases z with
    | inl i =>
      refine ⟨Sum.inl (interiorIndex n i), ?_⟩
      intro h
      rcases h with h | h
      · exact (interiorIndex_ne_endpoints n i).1 (Sum.inl.inj h)
      · exact (interiorIndex_ne_endpoints n i).2 (Sum.inl.inj h)
    | inr a =>
      refine ⟨Sum.inr a, ?_⟩
      intro h
      rcases h with h | h <;> cases h
  left_inv := by
    rintro ⟨z,hz⟩
    cases z with
    | inl i =>
      have hi0 : i.val ≠ 0 := by
        intro h
        exact hz (Or.inl (congrArg Sum.inl (Fin.ext h)))
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Fin.ext
      change (i.val-1)+1=i.val
      omega
    | inr a => rfl
  right_inv := by
    intro z
    cases z with
    | inl i =>
      apply congrArg Sum.inl
      apply Fin.ext
      change i.val+1-1=i.val
      omega
    | inr a => rfl
#print axioms Paper7Schwenk.endpointComplementEquiv

theorem interior_sun_root_adj (n : ℕ) (L : Fin (n+2) → List ℕ) (hn : 1 ≤ n)
    (i j : Fin n) :
    (sunGraph (n+2) L).Adj (Sum.inl (interiorIndex n i)) (Sum.inl (interiorIndex n j)) ↔
      i.val+1=j.val ∨ j.val+1=i.val := by
  have h := sunDeleteEdge_root_adj (n+2) L (by omega) 0 (Fin.last (n+1))
    rfl rfl (interiorIndex n i) (interiorIndex n j)
  have hi := interiorIndex_ne_endpoints n i
  have he : s(Sum.inl (interiorIndex n i), Sum.inl (interiorIndex n j)) ≠
      s((Sum.inl 0 : SunV (n+2) L), Sum.inl (Fin.last (n+1))) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact hi.1 (Sum.inl.inj h.1)
    · exact hi.2 (Sum.inl.inj h.1)
  rw [sunDeleteEdge, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
  rw [and_iff_left he] at h
  simpa only [interiorIndex, Nat.add_right_cancel_iff] using h
#print axioms Paper7Schwenk.interior_sun_root_adj

/-- Deleting the endpoints removes no arm vertex. The remaining core is the
open interior path and attachment rows are restricted by interiorIndex. -/
theorem endpointDelete_shift_blocks {K : Type*} [CommRing K]
    (n : ℕ) (L : Fin (n+2) → List ℕ) (hn : 1 ≤ n) (x : K) :
    (x • (1 : Matrix _ _ K) -
      (deleteVertices (sunGraph (n+2) L)
        ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))).adjMatrix K).reindex
        (endpointComplementEquiv n L) (endpointComplementEquiv n L) =
      Matrix.fromBlocks (pathShift x n)
        ((attachment (n+2) L).submatrix (interiorIndex n) id)
        (((attachment (n+2) L).submatrix (interiorIndex n) id).transpose)
        (pendantShift (n+2) L x) := by
  let V' := {z : SunV (n+2) L // z ∉
    ({Sum.inl 0, Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))}
  apply Matrix.ext
  intro a c
  cases a with
  | inl i =>
    cases c with
    | inl j =>
      change (x • (1 : Matrix V' V' K) -
        (deleteVertices (sunGraph (n+2) L)
          ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))).adjMatrix K)
        ⟨Sum.inl (interiorIndex n i),_⟩ ⟨Sum.inl (interiorIndex n j),_⟩ = _
      by_cases hij : i=j <;>
        simp [Matrix.fromBlocks_apply₁₁, pathShift, Matrix.sub_apply, Matrix.smul_apply,
          SimpleGraph.adjMatrix, Matrix.of_apply, deleteVertices,
          interior_sun_root_adj n L hn,
          (interiorIndex_injective n).eq_iff, hij]
    | inr z =>
      rcases z with ⟨k,j,t⟩
      change (x • (1 : Matrix V' V' K) -
        (deleteVertices (sunGraph (n+2) L)
          ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))).adjMatrix K)
        ⟨Sum.inl (interiorIndex n i),_⟩ ⟨Sum.inr ⟨k,j,t⟩,_⟩ = _
      simp [Matrix.fromBlocks_apply₁₂, Matrix.submatrix_apply, attachment,
        Matrix.sub_apply, Matrix.smul_apply, SimpleGraph.adjMatrix, Matrix.of_apply,
        deleteVertices, sun_root_arm_adj_iff]
      split_ifs <;> simp
  | inr z =>
    rcases z with ⟨k,j,t⟩
    cases c with
    | inl i =>
      change (x • (1 : Matrix V' V' K) -
        (deleteVertices (sunGraph (n+2) L)
          ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))).adjMatrix K)
        ⟨Sum.inr ⟨k,j,t⟩,_⟩ ⟨Sum.inl (interiorIndex n i),_⟩ = _
      simp [Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply, Matrix.transpose_apply,
        attachment, Matrix.sub_apply, Matrix.smul_apply, SimpleGraph.adjMatrix, Matrix.of_apply,
        deleteVertices, sun_arm_root_adj_iff]
      split_ifs <;> simp
    | inr z' =>
      rcases z' with ⟨k',j',t'⟩
      change (x • (1 : Matrix V' V' K) -
        (deleteVertices (sunGraph (n+2) L)
          ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) L))).adjMatrix K)
        ⟨Sum.inr ⟨k,j,t⟩,_⟩ ⟨Sum.inr ⟨k',j',t'⟩,_⟩ = _
      have h := sun_leaf_shift_entry (n+2) L x k k' j j' t t'
      simpa only [Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, SimpleGraph.adjMatrix, Matrix.of_apply, deleteVertices,
        SimpleGraph.induce_adj, Subtype.mk.injEq] using h
#print axioms Paper7Schwenk.endpointDelete_shift_blocks

end Paper7Schwenk
