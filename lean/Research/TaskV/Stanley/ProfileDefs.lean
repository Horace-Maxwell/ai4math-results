import Research.TaskV.Stanley.ChallengeA

namespace StanleyContinuation

noncomputable section
/-- Oriented connected partitions of a specified profile, with the k blocks named by Fin k.
A connected induced subgraph is nonempty, so profiles with an empty block have count zero. -/
def connectedCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (sizes : Fin k → ℕ) : ℕ :=
  Nat.card {f : Fin n → Fin k //
    (∀ c, Nat.card {i : Fin n // f i = c} = sizes c) ∧
    ∀ c, (G.induce {i : Fin n | f i = c}).Connected}

def SameConnected {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) : Prop :=
  ∀ k sizes, connectedCoefficient G k sizes = connectedCoefficient H k sizes

end
end StanleyContinuation
