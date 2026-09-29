import Research.WordRepTensor.Proof.WRMycielski
import Research.WordRepTensor.Proof.WREmbed
import Research.WordRepTensor.Proof.WRFold

/-!
# Problem 5.1 of arXiv:2609.20881v1: `mu (2n+1) × W (2m+1)` and `muExt (2n+1) × W (2m+1)` are not
word-representable (`Problem1Mu`, `Problem1MuExt`, `Problem5_1`)

(Written by Claude, 2026-09-28.) If `n ≥ m`, the graph of the homomorphism of Lemma 1 embeds the
first factor as an induced subgraph; if `n ≤ m`, Lemma 2 embeds `mu (2m+1)`. Both are not
word-representable, and word-representability passes to induced subgraphs.
-/

set_option autoImplicit false

namespace ClaudeWordRep

open WordRepTensor.Challenge

theorem problem1Mu : Problem1Mu := by
  intro n m hn hm hWR
  rcases le_total m n with hmn | hnm
  · obtain ⟨h⟩ := lemma1Mu n m hm hmn
    exact mycielskiOddCycleNotWR n hn
      (wordRepresentableOfEmbedding _ _ _ _ (embeddingOfHom _ _ _ _ ⟨h⟩) hWR)
  · exact mycielskiOddCycleNotWR m (by omega)
      (wordRepresentableOfEmbedding _ _ _ _ (lemma2Mu n m hn hnm hm) hWR)

theorem problem1MuExt : Problem1MuExt := by
  intro n m hn hm hWR
  rcases le_total m n with hmn | hnm
  · obtain ⟨h⟩ := lemma1MuExt n m hm hmn
    exact extMycielskiOddCycleNotWR n hn
      (wordRepresentableOfEmbedding _ _ _ _ (embeddingOfHom _ _ _ _ ⟨h⟩) hWR)
  · exact mycielskiOddCycleNotWR m (by omega)
      (wordRepresentableOfEmbedding _ _ _ _ (lemma2MuExt n m hn hnm hm) hWR)

theorem problem5_1 : Problem5_1 := ⟨problem1Mu, problem1MuExt⟩

end ClaudeWordRep
