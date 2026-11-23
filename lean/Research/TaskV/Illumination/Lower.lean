import Research.TaskV.Illumination.Challenge
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PrismIllumination

private theorem strictCoord {K : Set Space} (hQ : K ⊆ cube)
    {p : Space} (hp : p ∈ interior K) (i : Fin 3) : 0 < p i ∧ p i < 1 := by
  have hcube : cube = Set.univ.pi (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · intro h j _
      exact h j
    · intro h j
      exact h j (Set.mem_univ j)
  have hx := interior_mono hQ hp
  rw [hcube, interior_pi_set Set.finite_univ] at hx
  simpa only [interior_Icc, Set.mem_Ioo] using hx i (Set.mem_univ i)

private theorem boundaryAt {K : Set Space} (hQ : K ⊆ cube) {p : Space}
    (hp : p ∈ K) (hs : p 0 = 0 ∨ p 0 = 1) : p ∈ frontier K := by
  apply (mem_frontier_iff_notMem_interior hp).2
  intro hint
  obtain ⟨hl, hr⟩ := strictCoord hQ hint 0
  rcases hs with h | h <;> linarith

private theorem signsAt {K : Set Space} (hQ : K ⊆ cube) {u p : Space}
    (hu : Illuminates K u p) (k : Fin 3) :
    (p k = 0 → 0 < u k) ∧ (p k = 1 → u k < 0) := by
  obtain ⟨t, ht, hint⟩ := hu
  obtain ⟨hlo, hhi⟩ := strictCoord hQ hint k
  change 0 < p k + t * u k at hlo
  change p k + t * u k < 1 at hhi
  constructor
  · intro h
    have hprod : 0 < t * u k := by linarith
    exact (mul_pos_iff_of_pos_left ht).1 hprod
  · intro h
    have hprod : t * u k < 0 := by linarith
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg ht.le (not_lt.mp hn))) hprod

/-- Binary addresses of the cube corners; their digit order groups vertical pairs. -/
private def address (v : ℕ) (k : Fin 3) : Bool :=
  v.testBit (if k = 0 then 1 else if k = 1 then 2 else 0)

private def corner (v : ℕ) : Space :=
  fun k => if address v k then 1 else 0

private theorem corner_mem (v : ℕ) : corner v ∈ cube := by
  intro k
  dsimp [corner]
  split <;> norm_num

private theorem corner_boundary {K : Set Space} (hQ : K ⊆ cube)
    (v : ℕ) (hv : corner v ∈ K) : corner v ∈ frontier K := by
  apply boundaryAt hQ hv
  dsimp [corner]
  split <;> simp

private theorem sixCorners (i : Fin 6) : corner i.val ∈ prism := by
  refine ⟨corner_mem i.val, ?_⟩
  fin_cases i <;> norm_num [corner, address, Nat.testBit]

/-- A masked address omits only the height digit of the additional point on the edge. -/
private def valid (masked : Bool) (v : ℕ) (k : Fin 3) : Prop :=
  masked = false ∨ v ≠ 6 ∨ k ≠ 2

private instance (masked : Bool) (v : ℕ) (k : Fin 3) : Decidable (valid masked v k) := by
  unfold valid
  infer_instance

private def distinguish (n : ℕ) (masked : Bool) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∃ k : Fin 3,
    valid masked i.val k ∧ valid masked j.val k ∧ address i.val k ≠ address j.val k

private instance (n : ℕ) (masked : Bool) : Decidable (distinguish n masked) := by
  unfold distinguish
  infer_instance

private theorem addressBound {n m : ℕ} {K : Set Space} (hQ : K ⊆ cube)
    (masked : Bool) (points : Fin n → Space) (hb : ∀ i, points i ∈ frontier K)
    (hd : ∀ i k, valid masked i.val k → points i k = corner i.val k)
    (hs : distinguish n masked) (hl : CanLight K m) : n ≤ m := by
  classical
  obtain ⟨u, _, hc⟩ := hl
  choose idx lit using fun i => hc (points i) (hb i)
  have inj : Function.Injective idx := by
    intro i j hij
    by_contra hne
    obtain ⟨k, vi, vj, hdiff⟩ := hs i j hne
    have si := signsAt hQ (lit i) k
    have sj := signsAt hQ (lit j) k
    rw [hd i k vi, hij] at si
    rw [hd j k vj] at sj
    cases hi : address i.val k <;> cases hj : address j.val k <;>
      simp [corner, hi, hj] at si sj hdiff <;> linarith
  simpa using Fintype.card_le_of_injective idx inj

theorem lowerSix {K : Set Space} (hP : prism ⊆ K) (hQ : K ⊆ cube)
    (m : ℕ) (h : CanLight K m) : 6 ≤ m := by
  apply addressBound hQ false (fun i : Fin 6 => corner i.val)
  · intro i
    exact corner_boundary hQ _ (hP (sixCorners i))
  · intro i k _
    rfl
  · decide
  · exact h

theorem lowerSeven {K : Set Space} (hP : prism ⊆ K) (hQ : K ⊆ cube)
    (he : ¬ Disjoint K edge) (m : ℕ) (h : CanLight K m) : 7 ≤ m := by
  obtain ⟨p, hp, hedge⟩ := Set.not_disjoint_iff.mp he
  have hx : p 0 = 1 := hedge.2.1
  have hy : p 1 = 1 := hedge.2.2
  let pts : Fin 7 → Space := fun i => if i.val = 6 then p else corner i.val
  apply addressBound hQ true pts
  · intro i
    dsimp [pts]
    split
    · exact boundaryAt hQ hp (Or.inr hx)
    · exact corner_boundary hQ _ (hP (sixCorners ⟨i.val, by omega⟩))
  · intro i k hk
    dsimp [pts]
    split
    next h6 =>
      have h2 : k ≠ 2 := by simpa [valid, h6] using hk
      fin_cases k <;> simp_all [corner, address, Nat.testBit]
    next => rfl
  · decide
  · exact h

theorem lowerEight (m : ℕ) (h : CanLight cube m) : 8 ≤ m := by
  apply addressBound (Set.Subset.rfl : cube ⊆ cube) false (fun i : Fin 8 => corner i.val)
  · intro i
    exact corner_boundary Set.Subset.rfl _ (corner_mem _)
  · intro i k _
    rfl
  · decide
  · exact h

end PrismIllumination
