import Research.Backfill.Paper7.CyclicRecurrenceUnique

/-! Finite ordered transfer products. The imported successor helper has Root's
actual development receipt; this candidate itself has not been compiled. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Periodic
open BackfillPaper7.Challenge

def transfer (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, -1; 1, 0]
#print axioms Paper7Lemma22Periodic.transfer

def monodromy (b : ℕ) (c : Fin b → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((List.finRange b).reverse.map (fun k => transfer (c k))).prod
#print axioms Paper7Lemma22Periodic.monodromy

def transferPrefix (b : ℕ) (c : Fin b → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (((List.finRange b).take n).reverse.map (fun k => transfer (c k))).prod
#print axioms Paper7Lemma22Periodic.transferPrefix

def state (b : ℕ) (c : Fin b → ℝ) (n : ℕ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  transferPrefix b c n *ᵥ v
#print axioms Paper7Lemma22Periodic.state

theorem prefix_zero (b : ℕ) (c : Fin b → ℝ) : transferPrefix b c 0 = 1 := by
  simp [transferPrefix]
#print axioms Paper7Lemma22Periodic.prefix_zero

theorem prefix_all (b : ℕ) (c : Fin b → ℝ) : transferPrefix b c b = monodromy b c := by
  unfold transferPrefix
  rw [List.take_of_length_le (by simp)]
  rfl
#print axioms Paper7Lemma22Periodic.prefix_all

theorem prefix_succ (b : ℕ) (c : Fin b → ℝ) (n : ℕ) (hn : n < b) :
    transferPrefix b c (n + 1) = transfer (c ⟨n, hn⟩) * transferPrefix b c n := by
  unfold transferPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using hn)]
  simp only [List.reverse_append, List.reverse_singleton, List.map_append,
    List.map_singleton, List.prod_append, List.prod_singleton, List.getElem_finRange]
  congr 3
#print axioms Paper7Lemma22Periodic.prefix_succ

theorem state_zero (b : ℕ) (c : Fin b → ℝ) (v : Fin 2 → ℝ) : state b c 0 v = v := by
  simp only [state, prefix_zero, Matrix.one_mulVec]
#print axioms Paper7Lemma22Periodic.state_zero

theorem state_all (b : ℕ) (c : Fin b → ℝ) (v : Fin 2 → ℝ) :
    state b c b v = monodromy b c *ᵥ v := by
  simp only [state, prefix_all]
#print axioms Paper7Lemma22Periodic.state_all

theorem state_succ (b : ℕ) (c : Fin b → ℝ) (n : ℕ) (hn : n < b)
    (v : Fin 2 → ℝ) :
    state b c (n + 1) v =
      ![c ⟨n, hn⟩ * state b c n v 0 - state b c n v 1, state b c n v 0] := by
  change transferPrefix b c (n + 1) *ᵥ v = _
  rw [prefix_succ b c n hn, ← Matrix.mulVec_mulVec]
  change transfer (c ⟨n, hn⟩) *ᵥ state b c n v = _
  funext i
  fin_cases i <;> simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]
#print axioms Paper7Lemma22Periodic.state_succ

def cyclicSpace (b : ℕ) (c : Fin b → ℝ) : Submodule ℝ (Fin b → ℝ) where
  carrier := {y | ∀ k, y (prv b k) + y (nxt b k) = c k * y k}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro y z hy hz k
    change (y (prv b k) + z (prv b k)) + (y (nxt b k) + z (nxt b k)) =
      c k * (y k + z k)
    rw [mul_add]
    linarith [hy k, hz k]
  smul_mem' := by
    intro a y hy k
    change a * y (prv b k) + a * y (nxt b k) = c k * (a * y k)
    rw [← mul_add, hy k]
    ring
#print axioms Paper7Lemma22Periodic.cyclicSpace

def fixedSpace (b : ℕ) (c : Fin b → ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  LinearMap.ker (Matrix.toLin' (monodromy b c - 1))
#print axioms Paper7Lemma22Periodic.fixedSpace

theorem mem_fixedSpace_iff (b : ℕ) (c : Fin b → ℝ) (v : Fin 2 → ℝ) :
    v ∈ fixedSpace b c ↔ monodromy b c *ᵥ v = v := by
  simp only [fixedSpace, LinearMap.mem_ker, Matrix.toLin'_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
#print axioms Paper7Lemma22Periodic.mem_fixedSpace_iff

theorem nxt_last_eq_zero (b : ℕ) (hb : 3 ≤ b) :
    nxt b ⟨b - 1, by omega⟩ = ⟨0, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  change finRotate (n + 1) (Fin.last n) = 0
  exact finRotate_last
#print axioms Paper7Lemma22Periodic.nxt_last_eq_zero

theorem prv_zero_eq_last (b : ℕ) (hb : 3 ≤ b) :
    prv b ⟨0, by omega⟩ = ⟨b - 1, by omega⟩ := by
  exact (finRotate b).symm_apply_eq.mpr (nxt_last_eq_zero b hb).symm
#print axioms Paper7Lemma22Periodic.prv_zero_eq_last

theorem prv_mk_succ_eq (b n : ℕ) (hn : n < b) (hn1 : n + 1 < b) :
    prv b ⟨n + 1, hn1⟩ = ⟨n, hn⟩ := by
  exact (finRotate b).symm_apply_eq.mpr (nxt_mk_eq b n hn hn1).symm
#print axioms Paper7Lemma22Periodic.prv_mk_succ_eq

def initial (b : ℕ) (hb : 3 ≤ b) (y : Fin b → ℝ) : Fin 2 → ℝ :=
  ![y ⟨0, by omega⟩, y ⟨b - 1, by omega⟩]
#print axioms Paper7Lemma22Periodic.initial

def realize (b : ℕ) (c : Fin b → ℝ) (v : Fin 2 → ℝ) : Fin b → ℝ :=
  fun k => state b c k.val v 0
#print axioms Paper7Lemma22Periodic.realize

end Paper7Lemma22Periodic
