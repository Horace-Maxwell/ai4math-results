import Research.Backfill.Paper7.WeightedSchurChain
import Research.Backfill.Paper7.SunSchurPolynomial

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Classical

theorem sunDeleteEdge_root_adj (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (u v : Fin b) (hu : u.val = 0) (hv : v.val+1 = b) (i j : Fin b) :
    (sunDeleteEdge b L u v).Adj (Sum.inl i) (Sum.inl j) ↔
      i.val+1 = j.val ∨ j.val+1 = i.val := by
  rw [sunDeleteEdge, SimpleGraph.deleteEdges_adj]
  change ((Sum.inl i ≠ (Sum.inl j : SunV b L) ∧
    (j.val = (i.val+1)%b ∨ i.val = (j.val+1)%b)) ∧
    s(Sum.inl i,Sum.inl j) ∉ ({s(Sum.inl u,Sum.inl v)} : Set (Sym2 (SunV b L)))) ↔ _
  simp only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq, Fin.ext_iff]
  have hmod (k : Fin b) : (k.val+1)%b = if k.val+1=b then 0 else k.val+1 := by
    by_cases hk : k.val+1=b
    · simp [hk]
    · rw [ite_eq_right hk, Nat.mod_eq_of_lt (by omega)]
  have hi : i.val < b := i.isLt
  have hj : j.val < b := j.isLt
  have hne : ((Sum.inl i : SunV b L) ≠ Sum.inl j) ↔ i.val ≠ j.val := by
    constructor
    · intro h he
      exact h (congrArg Sum.inl (Fin.ext he))
    · intro h he
      exact h (congrArg Fin.val (Sum.inl.inj he))
  rw [hne]
  change ((i.val ≠ j.val ∧
    (j.val = (i.val+1)%b ∨ i.val = (j.val+1)%b)) ∧
    ¬ ((i.val = u.val ∧ j.val = v.val) ∨ (i.val = v.val ∧ j.val = u.val))) ↔
      i.val+1 = j.val ∨ j.val+1 = i.val
  simp only [hu]
  rw [hmod i, hmod j]
  split_ifs <;> omega
#print axioms Paper7Schwenk.sunDeleteEdge_root_adj

theorem pathShift_eq_weightedPath {K : Type*} [CommRing K] (n : ℕ) (x : K) :
    pathShift x n = weightedPath (fun _ => x) (fun _ => 1) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp [pathShift, weightedPath]
  · by_cases ha : i.val+1=j.val ∨ j.val+1=i.val <;>
      simp [pathShift, weightedPath, hij, ha]
#print axioms Paper7Schwenk.pathShift_eq_weightedPath

/-- The actual full deletion graph, with all dependent arm vertices intact. -/
theorem sunDeleteEdge_shift_blocks {K : Type*} [CommRing K]
    (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (u v : Fin b) (hu : u.val=0) (hv : v.val+1=b) (x : K) :
    x • (1 : Matrix (SunV b L) (SunV b L) K) - (sunDeleteEdge b L u v).adjMatrix K =
      Matrix.fromBlocks (pathShift x b) (attachment b L)
        (attachment b L).transpose (pendantShift b L x) := by
  have hadj (a c : SunV b L)
      (he : s(a, c) ≠ s(Sum.inl u, Sum.inl v)) :
      (sunDeleteEdge b L u v).Adj a c ↔ (sunGraph b L).Adj a c := by
    rw [sunDeleteEdge, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    exact and_iff_left he
  have hmatrix (a c : SunV b L)
      (he : s(a, c) ≠ s(Sum.inl u, Sum.inl v)) :
      (sunDeleteEdge b L u v).adjMatrix K a c = (sunGraph b L).adjMatrix K a c := by
    simp only [SimpleGraph.adjMatrix, Matrix.of_apply]
    by_cases ha : (sunGraph b L).Adj a c
    · have hd := (hadj a c he).mpr ha
      exact (ite_eq_left hd).trans (ite_eq_left ha).symm
    · have hd : ¬ (sunDeleteEdge b L u v).Adj a c := fun h => ha ((hadj a c he).mp h)
      exact (ite_eq_right hd).trans (ite_eq_right ha).symm
  apply Matrix.ext
  intro a c
  cases a with
  | inl i =>
    cases c with
    | inl j =>
      simp only [Matrix.fromBlocks_apply₁₁, pathShift, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix, Matrix.of_apply,
        Sum.inl.injEq, sunDeleteEdge_root_adj b L hb u v hu hv,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
    | inr z =>
      have he : s(Sum.inl i, Sum.inr z) ≠ s(Sum.inl u, Sum.inl v) := by
        simp
      have h := congrArg (fun M : Matrix (SunV b L) (SunV b L) K =>
        M (Sum.inl i) (Sum.inr z)) (sun_shift_fromBlocks b L hb x)
      change _ = attachment b L i z at h
      change _ = attachment b L i z
      rw [Matrix.sub_apply, hmatrix _ _ he]
      exact h
  | inr z =>
    cases c with
    | inl i =>
      have he : s(Sum.inr z, Sum.inl i) ≠ s(Sum.inl u, Sum.inl v) := by
        simp
      have h := congrArg (fun M : Matrix (SunV b L) (SunV b L) K =>
        M (Sum.inr z) (Sum.inl i)) (sun_shift_fromBlocks b L hb x)
      change _ = (attachment b L).transpose z i at h
      change _ = (attachment b L).transpose z i
      rw [Matrix.sub_apply, hmatrix _ _ he]
      exact h
    | inr z' =>
      have he : s(Sum.inr z, Sum.inr z') ≠ s(Sum.inl u, Sum.inl v) := by
        simp
      change _ = pendantShift b L x z z'
      rw [Matrix.sub_apply, hmatrix _ _ he]
      rcases z with ⟨k, j, t⟩
      rcases z' with ⟨k', j', t'⟩
      exact sun_leaf_shift_entry b L x k k' j j' t t'

#print axioms Paper7Schwenk.sunDeleteEdge_shift_blocks

theorem pathShift_schur {K : Type*} [Field K] (b : ℕ) (p q : Fin b → ℕ) (x : K) :
    pathShift x b - Matrix.diagonal (fun i => (p i : K)/x+(q i : K)*x/(x^2-1)) =
      weightedPath (fun i => x-(p i : K)/x-(q i : K)*x/(x^2-1)) (fun _ => 1) := by
  rw [pathShift_eq_weightedPath]
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, weightedPath,
      ite_true]
    ring
  · simp [Matrix.sub_apply, weightedPath, hij]
#print axioms Paper7Schwenk.pathShift_schur

end Paper7Schwenk
