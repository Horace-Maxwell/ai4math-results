import Research.Backfill.Paper8.Proof.Main.Lemma32
import Research.Backfill.Paper8.Proof.Main.Prop56
import Research.Backfill.Paper8.Proof.Main.Pointwise

/-!
# Paper 8, agent `main`: deliverables

`check_Lemma_3_2` (Lemma 3.2), `check_Prop_5_6` (Proposition 5.6) and
`check_Lemma_3_2_pointwise` (per-eigenvalue form of (S)). All three are proved from equation (3.1)
of the paper (`P8Basic.mulVec_eq_smul_iff`) without any hypothesis; in particular neither
Lemma 3.1 nor `Lemma_2_1` is assumed.
-/

set_option autoImplicit false

namespace P8Main

theorem check_Lemma_3_2 : BackfillPaper8.Challenge.Lemma_3_2 :=
  fun _ a _ s _ => lemma_3_2 a s

#print axioms check_Lemma_3_2

theorem check_Prop_5_6 : BackfillPaper8.Challenge.Prop_5_6 :=
  prop_5_6

#print axioms check_Prop_5_6

theorem check_Lemma_3_2_pointwise : BackfillPaper8.Challenge.Lemma_3_2_pointwise :=
  fun _ a _ s hs θ hθ => lemma_3_2_pointwise a s hs θ hθ

#print axioms check_Lemma_3_2_pointwise

end P8Main
