import Research.TaskE.CComplete
import Research.TaskE.FComplete
import Research.TaskE.SUniform

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open BackfillPaper1.Challenge

lemma prime_domain {q : ℕ} (hq : q.Prime) (ho : Odd q) (hne : q ≠ 3) :
    CodexPaper1.TaskE.Challenge.FPrimeDomain (q : ℝ) := by
  have hq3 : 3 ≤ q := hq.odd_iff.mp ho
  have hq4 : q ≠ 4 := by intro h; subst q; norm_num at hq
  have hq6 : q ≠ 6 := by intro h; subst q; norm_num at hq
  have hh : q = 5 ∨ q = 7 ∨ 8 ≤ q := by omega
  rcases hh with hh | hh | hh
  · left; exact_mod_cast hh
  · right; left; exact_mod_cast hh
  · right; right; exact_mod_cast hh

lemma prime_conditions {a q : ℕ} (ha : 3 ≤ a) (hq : q.Prime) (ho : Odd q) (hne : q ≠ 3) :
    CondAll a 3 q 4 := by
  have hd := prime_domain hq ho hne
  exact ⟨CodexPaper1.TaskE.SProof.condS_four (by omega) (by norm_num),
    full_F a ha q hd, full_C ha (domain_ge_five hd)⟩

lemma prime_sign_conclusion {a q : ℕ} (ha : 3 ≤ a)
    (hq : q.Prime) (ho : Odd q) (hne : q ≠ 3) : SignConclusion a 3 q := by
  have hq5 := domain_ge_five (prime_domain hq ho hne)
  exact CodexPaper1.Prop31.sign_conclusion (by omega) (Or.inr ⟨rfl, hq5⟩)
    (by linarith) (prime_conditions ha hq ho hne)

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.prime_conditions
#print axioms CodexPaper1.TaskE.FCProof.prime_sign_conclusion
