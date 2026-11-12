import Research.WordRepTensor.Challenge

/-! Task F, arXiv:2609.20881v1, Conclusion Problems 5.2 and 5.3.
The graphs and word-representability are those of the unchanged Paper 10 challenge. -/

set_option autoImplicit false

namespace WordRepTensor.TaskF.Challenge

open WordRepTensor.Challenge

/-- The affirmative answer to Alshammari Problem 5.2. -/
def Problem5_2 : Prop :=
  ∀ n m : ℕ, 1 ≤ n → n < m →
    ¬ WordRepresentable (tensorProd (mu (2 * n + 1)) (muExt (2 * m + 1)))

/-- The affirmative answer to Alshammari Problem 5.3. -/
def Problem5_3 : Prop :=
  ∀ n m : ℕ, 1 ≤ n → n < m →
    ¬ WordRepresentable (tensorProd (muExt (2 * n + 1)) (muExt (2 * m + 1)))

end WordRepTensor.TaskF.Challenge
