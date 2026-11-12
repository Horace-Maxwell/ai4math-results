import Research.WordRepTensor.TaskF.RouteContract

/-! The ordinary window colouring works on the extended window too. -/

set_option autoImplicit false

namespace WordRepTensor.TaskF.Proof

open WordRepTensor.Challenge WordRepTensor.TaskF.Route ClaudeWordRep

theorem commonColourCertificate : CommonColourCertificate := by
  unfold CommonColourCertificate
  decide +kernel

theorem commonWindowStep : CommonWindowStep := by
  intro V _ G w ι hw hi hwin
  rcases hwin with hmu | hext
  · exact flip_of_flipOK winMu_flip _ (orient_out w ι winMuEdges)
      (cond3_of_word hw ι hi winMuEdges hmu winMuPats winMu_valid)
  · exact flip_of_flipOK commonColourCertificate (orient w ι winExtEdges) (orient_out w ι winExtEdges)
      (cond3_of_word hw ι hi winExtEdges hext winExtPats winExt_valid)

theorem productStateShift : ProductStateShift := by
  intro k K _ hk w i
  rfl

end WordRepTensor.TaskF.Proof

#print axioms WordRepTensor.TaskF.Proof.commonColourCertificate
#print axioms WordRepTensor.TaskF.Proof.commonWindowStep
#print axioms WordRepTensor.TaskF.Proof.productStateShift
