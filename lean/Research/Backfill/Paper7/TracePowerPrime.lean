import Research.Backfill.Paper7.ChallengeV3

/-!
# Paper 7: the frozen integer-matrix trace congruence

Source-only author candidate for the V3 frozen contract. Map the matrix to
`ZMod q`, apply the finite-field trace identity and Fermat's identity, and
translate vanishing of the integer cast back to divisibility. The finite-field
trace theorem covers empty index types as well as nonempty ones.
-/

set_option autoImplicit false

theorem check_TracePowerPrime : BackfillPaper7.Challenge.TracePowerPrime := by
  intro V _ _ A q hq
  have : Fact q.Prime := ⟨hq⟩
  let f : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  have htrace : f ((A ^ q).trace) = f A.trace := by
    calc
      f ((A ^ q).trace) = ((A ^ q).map f).trace :=
        AddMonoidHom.map_trace f (A ^ q)
      _ = ((A.map f) ^ q).trace :=
        congrArg Matrix.trace (Matrix.map_pow A f q)
      _ = (A.map f).trace ^ q := ZMod.trace_pow_card (A.map f)
      _ = (A.map f).trace := ZMod.pow_card (A.map f).trace
      _ = f A.trace := (AddMonoidHom.map_trace f A).symm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((A ^ q).trace - A.trace) q).mp
  change f ((A ^ q).trace - A.trace) = 0
  rw [map_sub, htrace, sub_self]

#print axioms check_TracePowerPrime
