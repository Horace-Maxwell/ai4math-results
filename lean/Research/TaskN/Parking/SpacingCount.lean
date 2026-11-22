import Research.TaskN.Parking.ParkBand
import Research.TaskN.Parking.SpacingPalCount

namespace TaskN.Parking
open Challenge
open scoped Classical

theorem arithmetic_count (b : ℕ) (xs : List ℕ) (hd : dominant xs) :
    ((Finset.Icc b (b+xs.sum)).filter
      (fun a => xs.sum ≤ a-b ∨ prefixSymmetric xs (xs.sum-(a-b)))).card =
    1 + runContribution (jumps xs) :=
  (band_eq_prefix b xs hd).trans (palCount_ruler _)

end TaskN.Parking
