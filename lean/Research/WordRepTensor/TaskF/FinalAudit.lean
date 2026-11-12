import Research.WordRepTensor.TaskF.Main
import Research.WordRepTensor.Check
import Research.WordRepTensor.ChallengeTests

set_option autoImplicit false

open WordRepTensor.Challenge WordRepTensor.TaskF.Proof

example : WordRepTensor.TaskF.Challenge.Problem5_2 := check_Problem5_2
example : WordRepTensor.TaskF.Challenge.Problem5_3 := check_Problem5_3

example : ¬ WordRepresentable (tensorProd (mu 3) (muExt 5)) :=
  check_Problem5_2 1 2 (by decide) (by decide)
example : ¬ WordRepresentable (tensorProd (muExt 3) (muExt 5)) :=
  check_Problem5_3 1 2 (by decide) (by decide)

example : ¬ WordRepresentable (tensorProd (mu 5) (muExt 51)) :=
  check_Problem5_2 2 25 (by decide) (by decide)
example : ¬ WordRepresentable (tensorProd (muExt 5) (muExt 51)) :=
  check_Problem5_3 2 25 (by decide) (by decide)

#print WordRepTensor.TaskF.Challenge.Problem5_2
#print WordRepTensor.TaskF.Challenge.Problem5_3
#print axioms WordRepTensor.TaskF.Proof.check_Problem5_2
#print axioms WordRepTensor.TaskF.Proof.check_Problem5_3
