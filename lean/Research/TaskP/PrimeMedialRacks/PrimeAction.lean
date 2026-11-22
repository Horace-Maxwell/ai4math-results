import Research.TaskP.PrimeMedialRacks.DisplacementData

namespace TaskP.PrimeMedialRacks

/-- If every point stabilizer lies in a common proper subgroup, its index divides every
orbit size. On a prime-sized set the action is therefore transitive. -/
theorem prime_action_transitive {p : ℕ} (hp : p.Prime) (D : Subgroup (Equiv.Perm (Fin p)))
    (H : Subgroup D) (proper : H ≠ ⊤) (stab : ∀ x : Fin p, MulAction.stabilizer D x ≤ H) :
    ∀ x y : Fin p, ∃ d : D, d.val x = y := by
  classical
  let Ω := MulAction.orbitRel.Quotient D (Fin p)
  let : Fintype Ω := Fintype.ofFinite Ω
  have divIndex (x : Fin p) : H.index ∣ (MulAction.stabilizer D x).index :=
    Subgroup.index_dvd_of_le (stab x)
  have sum : p = ∑ ω : Ω, (MulAction.stabilizer D ω.out).index := by
    have h := Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer D (Fin p))
    simpa only [Nat.card_fin, Nat.card_sigma, Subgroup.index] using h
  have hd : H.index ∣ p := by
    calc
      H.index ∣ ∑ ω : Ω, (MulAction.stabilizer D ω.out).index :=
        Finset.dvd_sum fun ω _ => divIndex ω.out
      _ = p := sum.symm
  have idx : H.index = p :=
    (hp.eq_one_or_self_of_dvd H.index hd).resolve_left (fun h => proper (Subgroup.index_eq_one.mp h))
  intro x y
  let O := MulAction.orbit D x
  have dorb : p ∣ Nat.card O := by
    calc
      p = H.index := idx.symm
      _ ∣ (MulAction.stabilizer D x).index := divIndex x
      _ = Nat.card O := (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D x)).symm
  have : Nonempty O := ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  have low := Nat.le_of_dvd (Nat.card_pos (α := O)) dorb
  have high : Nat.card O ≤ Nat.card (Fin p) := Nat.card_le_card_of_injective _ Subtype.val_injective
  have bij : Function.Bijective (Subtype.val : O → Fin p) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨Subtype.val_injective, high.antisymm (by simpa using low)⟩
  obtain ⟨⟨_, hg⟩, rfl⟩ := bij.surjective y
  exact hg

theorem abelian_transitive_regular {α : Type*} (D : Subgroup (Equiv.Perm α))
    (comm : ∀ d ∈ D, ∀ e ∈ D, Commute d e)
    (tr : ∀ x y : α, ∃ d : D, d.val x = y) (x : α) :
    Function.Bijective (fun d : D => d.val x) := by
  refine ⟨?_, tr x⟩
  intro d e h
  apply Subtype.ext
  ext y
  obtain ⟨g, rfl⟩ := tr x y
  have hd := congrArg (fun t : Equiv.Perm α => t x) (comm _ d.property _ g.property).eq
  have he := congrArg (fun t : Equiv.Perm α => t x) (comm _ e.property _ g.property).eq
  exact hd.trans ((congrArg g.val h).trans he.symm)

end TaskP.PrimeMedialRacks
