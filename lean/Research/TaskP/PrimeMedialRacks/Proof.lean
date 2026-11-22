import Research.TaskP.PrimeMedialRacks.Coordinates
import Research.TaskP.PrimeMedialRacks.PrimeOrbits
import Research.TaskP.PrimeMedialRacks.Enumeration

namespace TaskP.PrimeMedialRacks.Proof

theorem classified {p : ℕ} [hp : Fact p.Prime] : ClassifiedAt p := by
  intro op hr hm hn
  obtain ⟨D⟩ := nonempty_regularDisplacements hp.out op hr hm hn
  exact regular_affine op hr hn D

theorem RackCount : Challenge.RackCount := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact rack_count_of_classification classified

theorem QuandleCount : Challenge.QuandleCount := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact quandle_count_of_classification classified

theorem AutomaticIdempotence : Challenge.AutomaticIdempotence := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact idempotent_of_classification classified

end TaskP.PrimeMedialRacks.Proof
