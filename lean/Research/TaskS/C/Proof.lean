import Research.TaskS.C.Geometry
import Research.TaskS.Shared.Sawtooth

namespace TaskS.C.Proof

theorem conjectureC : Challenge.conjectureC := by
  intro n u ω _ hω
  dsimp only
  intro hv hi
  exact geometry u ω hω hv hi fun q hq x =>
    TaskS.Shared.sawtooth_weighted q hq (fun i => 1 / ω i) (fun i => one_div_pos.mpr (hω i)) x

#print axioms conjectureC

end TaskS.C.Proof
