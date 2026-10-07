import Research.Backfill.Paper5.Proof.CycleRemarks

set_option autoImplicit false

namespace CodexPaper5.SignSmall

open BackfillPaper5

/-- The concrete parity representatives are the identity and the frozen transposition. -/
def rep (r : ℕ) (u : ZMod 2) : Challenge.Sym r :=
  if u = 0 then 1 else Challenge.swap12 r

@[simp] theorem rep_zero (r : ℕ) : rep r 0 = 1 := by simp [rep]

@[simp] theorem rep_one (r : ℕ) : rep r 1 = Challenge.swap12 r := by simp [rep]

/-- The two explicitly different points in the frozen `swap12` give odd sign. -/
theorem sgn_swap12 {r : ℕ} (hr : 2 ≤ r) : Challenge.sgn (Challenge.swap12 r) = 1 := by
  have hs : Equiv.Perm.sign (MulOpposite.unop (Challenge.swap12 r)) = -1 := by
    simp only [Challenge.swap12, dite_eq_left hr, MulOpposite.unop_op]
    apply Equiv.Perm.sign_swap
    intro h
    have hv := congrArg Fin.val h
    exact Nat.zero_ne_one hv
  rw [Challenge.sgn, hs]
  decide +kernel

/-- A parity section for every degree at least two. -/
theorem sgn_rep {r : ℕ} (hr : 2 ≤ r) (u : ZMod 2) : Challenge.sgn (rep r u) = u := by
  have hu : u = 0 ∨ u = 1 := by
    fin_cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hu with rfl | rfl
  · simp [CycleRemarks.sgn_one]
  · simpa using sgn_swap12 hr

/-- The frozen additive sign kernel is the usual alternating subgroup, after `unop`. -/
theorem sgn_zero_iff_even {r : ℕ} (g : Challenge.Sym r) :
    Challenge.sgn g = 0 ↔ MulOpposite.unop g ∈ alternatingGroup (Fin r) := by
  by_cases hs : Equiv.Perm.sign (MulOpposite.unop g) = 1 <;>
    simp [Challenge.sgn, Equiv.Perm.mem_alternatingGroup, hs]

/-- In degrees two and three the even subgroup has odd order (one and three, respectively). -/
theorem even_card_coprime_two {r : ℕ} (hr : r = 2 ∨ r = 3) :
    (Nat.card (alternatingGroup (Fin r))).Coprime 2 := by
  rcases hr with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num

/-- Squaring is injective on the actual even-sign kernel of `Sym 2` or `Sym 3`.
The proof uses the exact alternating-group order, so no sign evaluation oracle is needed. -/
theorem square_injective_even {r : ℕ} (hr : r = 2 ∨ r = 3)
    {g h : Challenge.Sym r} (hg : Challenge.sgn g = 0) (hh : Challenge.sgn h = 0)
    (hsq : g * g = h * h) : g = h := by
  let a : alternatingGroup (Fin r) := ⟨MulOpposite.unop g, (sgn_zero_iff_even g).mp hg⟩
  let b : alternatingGroup (Fin r) := ⟨MulOpposite.unop h, (sgn_zero_iff_even h).mp hh⟩
  have habsq : a ^ 2 = b ^ 2 := by
    apply Subtype.ext
    change (MulOpposite.unop g) ^ 2 = (MulOpposite.unop h) ^ 2
    simpa only [pow_two, MulOpposite.unop_mul] using congrArg MulOpposite.unop hsq
  have hinj : Function.Injective (fun x : alternatingGroup (Fin r) => x ^ 2) :=
    (even_card_coprime_two hr).pow_left_bijective.1
  have hab : a = b := hinj habsq
  apply MulOpposite.unop_injective
  exact congrArg Subtype.val hab

/-- The even component in the lifting construction, with multiplication in frozen `Sym r`. -/
def evenPart {r : ℕ} (g : Challenge.Sym r) : Challenge.Sym r :=
  (rep r (Challenge.sgn g))⁻¹ * g

theorem sgn_evenPart {r : ℕ} (hr : 2 ≤ r) (g : Challenge.Sym r) :
    Challenge.sgn (evenPart g) = 0 := by
  rw [evenPart, CycleRemarks.sgn_mul, CycleRemarks.sgn_inv, sgn_rep hr]
  exact CharTwo.add_self_eq_zero _

/-- The decomposition used by the actual Rees lift, without reversing the paper's product. -/
theorem rep_mul_evenPart {r : ℕ} (g : Challenge.Sym r) :
    rep r (Challenge.sgn g) * evenPart g = g := by
  simp [evenPart]

#print axioms CodexPaper5.SignSmall.sgn_rep
#print axioms CodexPaper5.SignSmall.square_injective_even
#print axioms CodexPaper5.SignSmall.sgn_evenPart
#print axioms CodexPaper5.SignSmall.rep_mul_evenPart

end CodexPaper5.SignSmall
