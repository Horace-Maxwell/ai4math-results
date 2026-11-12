import Research.WordRepTensor.TaskF.Challenge
import Research.WordRepTensor.TaskF.Colour
import Research.WordRepTensor.TaskF.Windows

/-! Full answers: the common colour would alternate around the longer odd cycle. -/

set_option autoImplicit false

namespace WordRepTensor.TaskF.Proof

open WordRepTensor.Challenge WordRepTensor.TaskF.Route ClaudeWordRep

theorem check_Problem5_2 : WordRepTensor.TaskF.Challenge.Problem5_2 := by
  intro n m hn hnm hwr
  let _ : NeZero (2 * m + 1) := ⟨by omega⟩
  have hk : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨w, hw⟩ := hwr
  refine no_flip_cycle (by omega : (2 * m + 1) % 2 = 1)
    (fun i => colOf winMuCol (stateOf (orient w (productWinMap hk i) winMuEdges) winMuS0)) ?_
  intro i
  obtain ⟨hi, hwin⟩ := productWindowsMu (2 * n + 1) (2 * m + 1) hk
    (by omega) (by omega) (by omega) (by omega) i
  have hf := commonWindowStep _ _ w (productWinMap hk i) hw hi hwin
  rw [productStateShift (2 * n + 1) (2 * m + 1) hk w i] at hf
  exact hf

theorem check_Problem5_3 : WordRepTensor.TaskF.Challenge.Problem5_3 := by
  intro n m hn hnm hwr
  let _ : NeZero (2 * m + 1) := ⟨by omega⟩
  have hk : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨w, hw⟩ := hwr
  refine no_flip_cycle (by omega : (2 * m + 1) % 2 = 1)
    (fun i => colOf winMuCol (stateOf (orient w (productWinMap hk i) winMuEdges) winMuS0)) ?_
  intro i
  obtain ⟨hi, hwin⟩ := productWindowsExt (2 * n + 1) (2 * m + 1) hk
    (by omega) (by omega) (by omega) (by omega) i
  have hf := commonWindowStep _ _ w (productWinMap hk i) hw hi hwin
  rw [productStateShift (2 * n + 1) (2 * m + 1) hk w i] at hf
  exact hf

end WordRepTensor.TaskF.Proof

#print axioms WordRepTensor.TaskF.Proof.check_Problem5_2
#print axioms WordRepTensor.TaskF.Proof.check_Problem5_3
