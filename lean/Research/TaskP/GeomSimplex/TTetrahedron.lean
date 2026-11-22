import Research.TaskP.GeomSimplex.TLength
import Research.TaskP.GeomSimplex.TDiameter

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

theorem TetrahedronDiameter : TetrahedronDiameter :=
  ⟨fullT, ⟨lowerT, fun _ => upperT⟩, diameterT⟩

end TaskP.GeomSimplex.Proof
