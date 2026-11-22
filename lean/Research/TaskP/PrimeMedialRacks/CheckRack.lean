import Research.TaskP.PrimeMedialRacks.Proof

namespace TaskP.PrimeMedialRacks

theorem check_RackCount : Challenge.RackCount := Proof.RackCount
theorem check_QuandleCount : Challenge.QuandleCount := Proof.QuandleCount
theorem check_AutomaticIdempotence : Challenge.AutomaticIdempotence := Proof.AutomaticIdempotence

#print axioms Proof.RackCount
#print axioms Proof.QuandleCount
#print axioms Proof.AutomaticIdempotence
#print axioms check_RackCount
#print axioms check_QuandleCount
#print axioms check_AutomaticIdempotence

end TaskP.PrimeMedialRacks
