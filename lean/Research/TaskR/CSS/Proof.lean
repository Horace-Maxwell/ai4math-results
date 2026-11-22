import Research.TaskR.CSS.Radius
import Research.TaskR.CSS.Volume
import Research.TaskR.CSS.Exclusion

namespace TaskR.CSS.Proof

theorem NonHollow : Challenge.NonHollow := Geometry.nonHollow
theorem Radius : Challenge.Radius := radius
theorem Volume : Challenge.Volume := VolumeCalc.volume_from_nonHollow NonHollow

#print axioms NonHollow
#print axioms Radius
#print axioms Volume

end TaskR.CSS.Proof
