import Research.WordRepTensor.Challenge
import Research.WordRepTensor.Proof.WRMain

/-!
# Word-representability: every frozen statement is proved

Frozen statement file: version 2, SHA-256
`40c8efd69f8499c9874f07163043c0793c94c8597b7a3902d5aeb0a2ce0c9b58`, frozen 2026-09-27 22:04 UTC.
Every theorem below has as its type exactly one frozen `def … : Prop` of that file.
-/

set_option autoImplicit false

namespace WordRepTensor.Check

theorem check_Problem1Mu : WordRepTensor.Challenge.Problem1Mu := ClaudeWordRep.problem1Mu
theorem check_Problem1MuExt : WordRepTensor.Challenge.Problem1MuExt := ClaudeWordRep.problem1MuExt
theorem check_Problem5_1 : WordRepTensor.Challenge.Problem5_1 := ClaudeWordRep.problem5_1
theorem check_MycielskiOddCycleNotWR : WordRepTensor.Challenge.MycielskiOddCycleNotWR :=
  ClaudeWordRep.mycielskiOddCycleNotWR
theorem check_ExtMycielskiOddCycleNotWR : WordRepTensor.Challenge.ExtMycielskiOddCycleNotWR :=
  ClaudeWordRep.extMycielskiOddCycleNotWR
theorem check_WordRepresentableOfEmbedding : WordRepTensor.Challenge.WordRepresentableOfEmbedding :=
  ClaudeWordRep.wordRepresentableOfEmbedding
theorem check_EmbeddingOfHom : WordRepTensor.Challenge.EmbeddingOfHom := ClaudeWordRep.embeddingOfHom
theorem check_Lemma1Mu : WordRepTensor.Challenge.Lemma1Mu := ClaudeWordRep.lemma1Mu
theorem check_Lemma1MuExt : WordRepTensor.Challenge.Lemma1MuExt := ClaudeWordRep.lemma1MuExt
theorem check_Lemma2Mu : WordRepTensor.Challenge.Lemma2Mu := ClaudeWordRep.lemma2Mu
theorem check_Lemma2MuExt : WordRepTensor.Challenge.Lemma2MuExt := ClaudeWordRep.lemma2MuExt

#print axioms check_Problem1Mu
#print axioms check_Problem1MuExt
#print axioms check_Problem5_1
#print axioms check_MycielskiOddCycleNotWR
#print axioms check_ExtMycielskiOddCycleNotWR
#print axioms check_WordRepresentableOfEmbedding
#print axioms check_EmbeddingOfHom
#print axioms check_Lemma1Mu
#print axioms check_Lemma1MuExt
#print axioms check_Lemma2Mu
#print axioms check_Lemma2MuExt

end WordRepTensor.Check
