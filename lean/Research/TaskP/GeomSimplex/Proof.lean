import Research.TaskP.GeomSimplex.TTetrahedron
import Research.TaskP.GeomSimplex.UTetrahedron
import Research.TaskP.GeomSimplex.PyramidTransport
import Research.TaskP.GeomSimplex.PyramidDiameter
namespace TaskP.GeomSimplex.Proof
open Challenge

private theorem one_level {d m : ℕ} (v : Fin (d+1) → Lattice d) (hd : 0<d)
    (hv : fullSimplex v) (h : lengthIs (simplex v) m) :
    lengthIs (simplex (pyrVertices v)) m := by
  have h1 : lengthIs (dilate 1 (simplex v)) m := by simpa [dilate] using h
  simpa [dilate] using pyramid_length v hd hv (t:=1) (by decide) h1

theorem EveryDimensionDiameter : Challenge.EveryDimensionDiameter := by
  intro d hd
  induction d,hd using Nat.le_induction with
  | base => exact ⟨verticesT,TetrahedronDiameter⟩
  | succ d hd ih =>
    obtain ⟨v,hv,hL,hD⟩ := ih
    exact ⟨pyrVertices v,full_pyramid v hv,one_level v (by omega) hv hL,diameter_pyramid v hD⟩

theorem EveryDimensionDilations : Challenge.EveryDimensionDilations := by
  intro d hd
  induction d,hd using Nat.le_induction with
  | base => exact ⟨verticesU,TetrahedronDilations⟩
  | succ d hd ih =>
    obtain ⟨v,hv,hL,hseq,_⟩ := ih
    have hbase := one_level v (by omega) hv hL
    have ht (t : ℕ) (h : 2 ≤ t) := pyramid_length v (by omega) hv (by omega : 0<t) (hseq t h)
    exact ⟨pyrVertices v,full_pyramid v hv,hbase,ht,not_quasiLinear hbase ht⟩

end TaskP.GeomSimplex.Proof
