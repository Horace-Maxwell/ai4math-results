import Research.Backfill.Paper7.CyclicTransferPrefix

/-! Both directions, both wrap equations and both inverse identities.
No dimensional shortcut or conditional surjectivity assumption is used. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Periodic
open BackfillPaper7.Challenge

theorem state_initial (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (y : cyclicSpace b c) : ∀ n (hn : n < b),
    state b c n (initial b hb y.1) = ![y.1 ⟨n, hn⟩, y.1 (prv b ⟨n, hn⟩)] := by
  intro n
  induction n with
  | zero =>
    intro hn
    simp only [state_zero, initial, prv_zero_eq_last b hb]
  | succ n ih =>
    intro hn
    have hn0 : n < b := by omega
    have hr := y.property ⟨n, hn0⟩
    rw [nxt_mk_eq b n hn0 hn] at hr
    rw [state_succ b c n hn0, ih hn0]
    funext i
    fin_cases i
    · change c ⟨n, hn0⟩ * y.1 ⟨n, hn0⟩ - y.1 (prv b ⟨n, hn0⟩) = y.1 ⟨n + 1, hn⟩
      linarith
    · change y.1 ⟨n, hn0⟩ = y.1 (prv b ⟨n + 1, hn⟩)
      rw [prv_mk_succ_eq b n hn0 hn]
#print axioms Paper7Lemma22Periodic.state_initial

theorem initial_fixed (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (y : cyclicSpace b c) :
    monodromy b c *ᵥ initial b hb y.1 = initial b hb y.1 := by
  rw [← state_all b c (initial b hb y.1)]
  have hn : b - 1 < b := by omega
  have hs := state_succ b c (b - 1) hn (initial b hb y.1)
  have he : b - 1 + 1 = b := by omega
  rw [he, state_initial b hb c y (b - 1) hn] at hs
  have hr := y.property ⟨b - 1, hn⟩
  rw [nxt_last_eq_zero b hb] at hr
  funext i
  fin_cases i
  · have h0 := congrFun hs 0
    change state b c b (initial b hb y.1) 0 =
      c ⟨b - 1, hn⟩ * y.1 ⟨b - 1, hn⟩ - y.1 (prv b ⟨b - 1, hn⟩) at h0
    change state b c b (initial b hb y.1) 0 = y.1 ⟨0, by omega⟩
    rw [h0]
    linarith
  · exact congrFun hs 1
#print axioms Paper7Lemma22Periodic.initial_fixed

theorem fixed_state_all (b : ℕ) (c : Fin b → ℝ) (v : fixedSpace b c) :
    state b c b v.1 = v.1 :=
  (state_all b c v.1).trans ((mem_fixedSpace_iff b c v.1).mp v.property)
#print axioms Paper7Lemma22Periodic.fixed_state_all

theorem realize_zero (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ) (v : Fin 2 → ℝ) :
    realize b c v ⟨0, by omega⟩ = v 0 := by
  simp only [realize, state_zero]
#print axioms Paper7Lemma22Periodic.realize_zero

theorem realize_last (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ) (v : fixedSpace b c) :
    realize b c v.1 ⟨b - 1, by omega⟩ = v.1 1 := by
  have hn : b - 1 < b := by omega
  have hs := congrFun (state_succ b c (b - 1) hn v.1) 1
  change state b c (b - 1 + 1) v.1 1 = state b c (b - 1) v.1 0 at hs
  rw [show b - 1 + 1 = b by omega, fixed_state_all b c v] at hs
  exact hs.symm
#print axioms Paper7Lemma22Periodic.realize_last

theorem realize_prev (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (v : fixedSpace b c) (k : Fin b) :
    realize b c v.1 (prv b k) = state b c k.val v.1 1 := by
  rcases k with ⟨n, hn⟩
  cases n with
  | zero =>
    simpa only [prv_zero_eq_last b hb, state_zero] using realize_last b hb c v
  | succ n =>
    have hn0 : n < b := by omega
    rw [prv_mk_succ_eq b n hn0 hn]
    change state b c n v.1 0 = state b c (n + 1) v.1 1
    exact (congrFun (state_succ b c n hn0 v.1) 1).symm
#print axioms Paper7Lemma22Periodic.realize_prev

theorem realize_next (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (v : fixedSpace b c) (k : Fin b) :
    realize b c v.1 (nxt b k) = state b c (k.val + 1) v.1 0 := by
  by_cases hn : k.val + 1 < b
  · have hk : nxt b k = ⟨k.val + 1, hn⟩ := nxt_mk_eq b k.val k.isLt hn
    rw [hk]
    rfl
  · have hv : k.val = b - 1 := by omega
    have hk : k = ⟨b - 1, by omega⟩ := Fin.ext hv
    rw [hk, nxt_last_eq_zero b hb, realize_zero b hb c v.1]
    simp only [show b - 1 + 1 = b by omega, fixed_state_all b c v]
#print axioms Paper7Lemma22Periodic.realize_next

theorem realize_mem_cyclicSpace (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (v : fixedSpace b c) : realize b c v.1 ∈ cyclicSpace b c := by
  intro k
  rw [realize_prev b hb c v k, realize_next b hb c v k]
  have hs := congrFun (state_succ b c k.val k.isLt v.1) 0
  change state b c (k.val + 1) v.1 0 =
    c k * state b c k.val v.1 0 - state b c k.val v.1 1 at hs
  change state b c k.val v.1 1 + state b c (k.val + 1) v.1 0 =
    c k * state b c k.val v.1 0
  linarith
#print axioms Paper7Lemma22Periodic.realize_mem_cyclicSpace

theorem realize_initial (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (y : cyclicSpace b c) : realize b c (initial b hb y.1) = y.1 := by
  funext k
  exact congrFun (state_initial b hb c y k.val k.isLt) 0
#print axioms Paper7Lemma22Periodic.realize_initial

theorem initial_realize (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ)
    (v : fixedSpace b c) : initial b hb (realize b c v.1) = v.1 := by
  funext i
  fin_cases i
  · exact realize_zero b hb c v.1
  · exact realize_last b hb c v
#print axioms Paper7Lemma22Periodic.initial_realize

def cycleEquivFixed (b : ℕ) (hb : 3 ≤ b) (c : Fin b → ℝ) :
    cyclicSpace b c ≃ₗ[ℝ] fixedSpace b c where
  toFun y := ⟨initial b hb y.1, (mem_fixedSpace_iff b c _).mpr (initial_fixed b hb c y)⟩
  invFun v := ⟨realize b c v.1, realize_mem_cyclicSpace b hb c v⟩
  left_inv y := by
    apply Subtype.ext
    exact realize_initial b hb c y
  right_inv v := by
    apply Subtype.ext
    exact initial_realize b hb c v
  map_add' y z := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  map_smul' a y := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
#print axioms Paper7Lemma22Periodic.cycleEquivFixed

theorem monodromy_eq_Mono (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    monodromy b (fun k => m - fk b p q m k) = Mono b p q m := by
  rfl
#print axioms Paper7Lemma22Periodic.monodromy_eq_Mono

def cycleEquivMono (b : ℕ) (hb : 3 ≤ b) (p q : Fin b → ℕ) (m : ℝ) :
    cyclicSpace b (fun k => m - fk b p q m k) ≃ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (Mono b p q m - 1)) := by
  exact cycleEquivFixed b hb (fun k => m - fk b p q m k)
#print axioms Paper7Lemma22Periodic.cycleEquivMono

end Paper7Lemma22Periodic
