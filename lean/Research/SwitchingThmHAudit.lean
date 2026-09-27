import Research.SwitchingThmH

/-! Audit: the exact statements used in PROOF.md §9.22, restated and checked against the library file. -/

example (b sq g NI NII : ℕ) (hb : 13 ≤ b) (hsq : sq ≤ Nat.sqrt (b - 1)) (hsqg : sq ≤ g)
    (hNI : NI ≤ sq + 1) (hr : NI + 2 * NII + g ≤ b + 1) : 2 * NI + NII + 1 ≤ b - 1 :=
  SwitchingThmH.row_budget b sq g NI NII hb hsq hsqg hNI hr

example {K : Type*} [Field K] [CharZero K] (w u : K) (hw : ∀ q : ℚ, (q : K) ≠ w) :
    Set.Subsingleton {p : ℤ × ℤ | (p.1 : K) + (p.2 : K) * w = u} :=
  SwitchingThmH.sol_subsingleton w u (SwitchingThmH.indep_of_irrational w hw)

#print axioms SwitchingThmH.row_budget
#print axioms SwitchingThmH.sol_subsingleton
