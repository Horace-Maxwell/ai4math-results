import Research.TaskR.A7.Counting
import Research.TaskR.A7.Interpret
import Research.TaskR.A7.Cert

namespace TaskR.A7.Proof

theorem HasTerrace : Challenge.HasTerrace :=
  fromMatching (Interpret.ordering Cert.allRows) (Interpret.first Cert.allRows)
    (Interpret.matching Cert.allRows) (Interpret.edges Cert.allRows)

end TaskR.A7.Proof
