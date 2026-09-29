import Research.Backfill.Paper3.Proof.L67.BPrime
import Research.Backfill.Paper3.Proof.L67.Lemma7

/-!
# Lemmas 6 and 7, Theorem B′

The statements `WSymm`, `Lemma7`, `Lemma6`, `TheoremBprime`, `Neg_8_2` and `Neg_12_3_bip` of
`Research.Backfill.Paper3.Challenge`, proved in the modules `Research.Backfill.Paper3.Proof.L67.*` (on top of `Research.Backfill.Paper3.Proof.Basic`
and `Research.Backfill.Paper3.Proof.Poly`) with no hypotheses.
-/

set_option autoImplicit false

namespace P3L67

open BackfillPaper3.Challenge

theorem check_WSymm : WSymm := wSymm

#print axioms check_WSymm

theorem check_Lemma7 : Lemma7 := lemma7

#print axioms check_Lemma7

theorem check_Lemma6 : Lemma6 := fun d hd a₁ b₁ a₂ b₂ =>
  ⟨lemma6_poly d hd a₁ b₁ a₂ b₂, fun W _ _ F _ t => lemma6_count d hd a₁ b₁ a₂ b₂ W F t⟩

#print axioms check_Lemma6

theorem check_TheoremBprime : TheoremBprime := theoremBprime

#print axioms check_TheoremBprime

theorem check_Neg_8_2 : Neg_8_2 := neg_8_2

#print axioms check_Neg_8_2

theorem check_Neg_12_3_bip : Neg_12_3_bip := neg_12_3_bip

#print axioms check_Neg_12_3_bip

end P3L67
