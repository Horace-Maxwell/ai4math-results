import Research.WordRepTensor.Challenge

/-!
# Comparator challenge for the word-representability paper (tensor products of Mycielskians
of odd cycles with odd wheels)

For the comparator (https://github.com/leanprover/comparator). Every theorem below
states, with a `sorry` proof, exactly the type of the theorem of the same name in
`Research/WordRepTensor/Check.lean`, which is the solution module. The statements refer
only to the frozen statement file `Research/WordRepTensor/Challenge.lean` (SHA-256
`40c8efd6…9b58`), which imports only Mathlib.

The `sorry`s are intentional: comparator checks that the solution proves the same
statements, using only the permitted axioms, and replays it in the Lean kernel and in
the independent kernel nanoda. This module is not imported by `Research.lean`.
-/

set_option autoImplicit false

namespace WordRepTensor.Check

theorem check_Problem1Mu : WordRepTensor.Challenge.Problem1Mu := sorry

theorem check_Problem1MuExt : WordRepTensor.Challenge.Problem1MuExt := sorry

theorem check_Problem5_1 : WordRepTensor.Challenge.Problem5_1 := sorry

theorem check_MycielskiOddCycleNotWR : WordRepTensor.Challenge.MycielskiOddCycleNotWR := sorry

theorem check_ExtMycielskiOddCycleNotWR : WordRepTensor.Challenge.ExtMycielskiOddCycleNotWR := sorry

theorem check_WordRepresentableOfEmbedding : WordRepTensor.Challenge.WordRepresentableOfEmbedding := sorry

theorem check_EmbeddingOfHom : WordRepTensor.Challenge.EmbeddingOfHom := sorry

theorem check_Lemma1Mu : WordRepTensor.Challenge.Lemma1Mu := sorry

theorem check_Lemma1MuExt : WordRepTensor.Challenge.Lemma1MuExt := sorry

theorem check_Lemma2Mu : WordRepTensor.Challenge.Lemma2Mu := sorry

theorem check_Lemma2MuExt : WordRepTensor.Challenge.Lemma2MuExt := sorry

end WordRepTensor.Check
