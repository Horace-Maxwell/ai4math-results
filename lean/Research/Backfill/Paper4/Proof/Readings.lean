import Research.Backfill.Paper4.Proof.MetricBounds

/-!
Paper4: exact repeated-vertex, distinct-triple, and weak/strong readings.
Compilation and acceptance evidence is separate from this proof source.
The strong-reading equivalences keep the frozen cardinality >= 3 hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper4
open BackfillPaper4 SimpleGraph Finset
namespace Readings

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
lemma triDist_swap_left (u v w : V) :
    Challenge.triDist G u v w = Challenge.triDist G v u w := by
  unfold Challenge.triDist
  rw [G.dist_comm (u := v) (v := u)]
  omega

omit [Fintype V] in
lemma triDist_swap_right (u v w : V) :
    Challenge.triDist G u v w = Challenge.triDist G u w v := by
  unfold Challenge.triDist
  rw [G.dist_comm (u := w) (v := v)]
  omega

omit [Fintype V] in
lemma triDist_rotate (u v w : V) :
    Challenge.triDist G u v w = Challenge.triDist G v w u := by
  unfold Challenge.triDist
  rw [G.dist_comm (u := v) (v := u), G.dist_comm (u := w) (v := u)]
  omega

lemma repeated_iff (hc : G.Connected) (u v : V) :
    Challenge.IsTriametral G u u v ↔
      Challenge.triameter G = 2 * G.diam ∧ Challenge.IsDiametral G u v := by
  have hd := MetricBounds.dist_le_diameter G hc u v
  have ht := MetricBounds.two_diam_le_triameter G hc
  unfold Challenge.IsTriametral Challenge.IsDiametral
  rw [MetricBounds.triDist_repeated]
  omega

lemma peripheral_iff_pair (hc : G.Connected) (u : V) :
    Challenge.IsPeripheral G u ↔ Challenge.IsPeripheralPair G u := by
  have : Nonempty V := hc.nonempty
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hc
  have hediam : G.ediam = (G.diam : ℕ∞) := by
    change G.ediam = (G.ediam.toNat : ℕ∞)
    exact (ENat.natCast_toNat hne).symm
  have hedist (v w : V) : G.edist v w = (G.dist v w : ℕ∞) :=
    ((hc.preconnected v w).coe_dist_eq_edist).symm
  constructor
  · intro h
    change G.eccent u = G.ediam at h
    obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
    refine ⟨v, ?_⟩
    rw [h, hediam, hedist] at hv
    change G.dist u v = G.diam
    exact_mod_cast hv
  · rintro ⟨v, hv⟩
    change G.dist u v = G.diam at hv
    change G.eccent u = G.ediam
    apply le_antisymm eccent_le_ediam
    rw [hediam, ← hv, ← hedist]
    exact edist_le_eccent

lemma peripheral_of_diametral (hc : G.Connected) {u v : V}
    (huv : Challenge.IsDiametral G u v) : Challenge.IsPeripheral G u :=
  (peripheral_iff_pair G hc u).mpr ⟨v, huv⟩

lemma repeated_has_diametral (hc : G.Connected) {a b c : V}
    (htri : Challenge.IsTriametral G a b c) (hrep : a = b ∨ a = c ∨ b = c) :
    Challenge.IsDiametral G a b ∨ Challenge.IsDiametral G a c ∨ Challenge.IsDiametral G b c := by
  rcases hrep with he | he | he
  · subst b
    exact Or.inr (Or.inl ((repeated_iff G hc a c).mp htri).2)
  · subst c
    have hh : Challenge.IsTriametral G a a b := by
      change Challenge.triDist G a a b = _
      rw [triDist_swap_right G a a b]
      exact htri
    exact Or.inl ((repeated_iff G hc a b).mp hh).2
  · subst c
    have hh : Challenge.IsTriametral G b b a := by
      change Challenge.triDist G b b a = _
      rw [← triDist_rotate G a b b]
      exact htri
    have hd := ((repeated_iff G hc b a).mp hh).2
    left
    change G.dist a b = G.diam
    rw [G.dist_comm (u := a) (v := b)]
    exact hd

lemma triametral_distinct_of_ne_two (hc : G.Connected)
    (hT : Challenge.triameter G ≠ 2 * G.diam) {a b c : V}
    (htri : Challenge.IsTriametral G a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩
  · intro he; subst b
    exact hT ((repeated_iff G hc a c).mp htri).1
  · intro he; subst c
    have hh : Challenge.IsTriametral G a a b := by
      change Challenge.triDist G a a b = _
      rw [triDist_swap_right G a a b]
      exact htri
    exact hT ((repeated_iff G hc a b).mp hh).1
  · intro he; subst c
    have hh : Challenge.IsTriametral G b b a := by
      change Challenge.triDist G b b a = _
      rw [← triDist_rotate G a b b]
      exact htri
    exact hT ((repeated_iff G hc b a).mp hh).1

lemma triametral_distinct_of_no_diametral (hc : G.Connected) {a b c : V}
    (htri : Challenge.IsTriametral G a b c)
    (hab : ¬ Challenge.IsDiametral G a b) (hac : ¬ Challenge.IsDiametral G a c)
    (hbc : ¬ Challenge.IsDiametral G b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hn : ¬ (a = b ∨ a = c ∨ b = c) := by
    intro hrep
    rcases repeated_has_diametral G hc htri hrep with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr (Or.inl h)),
    fun h => hn (Or.inr (Or.inr h))⟩

lemma question3'_of_question3 (hc : G.Connected) (h : Challenge.Question3 G) :
    Challenge.Question3' G := by
  intro a b c htri
  rcases h a b c htri with hd | hd | hd
  · exact Or.inl (peripheral_of_diametral G hc hd)
  · exact Or.inl (peripheral_of_diametral G hc hd)
  · exact Or.inr (Or.inl (peripheral_of_diametral G hc hd))

lemma question4'_of_question4 (hc : G.Connected) (h : Challenge.Question4 G) :
    Challenge.Question4' G := by
  intro x hx
  obtain ⟨y, hxy⟩ := (peripheral_iff_pair G hc x).mp hx
  obtain ⟨z, htri⟩ := h x y hxy
  exact ⟨y, z, htri⟩

lemma exists_outside_pair (hcard : 3 ≤ Fintype.card V) (x y : V) :
    ∃ z : V, z ≠ x ∧ z ≠ y := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := V)).mp (by omega)
  by_contra hn
  have hcover : ∀ z : V, z = x ∨ z = y := by
    intro z
    by_cases hz : z = x
    · exact Or.inl hz
    · right
      by_contra hzy
      exact hn ⟨z, hz, hzy⟩
  rcases hcover a with ha | ha <;>
    rcases hcover b with hb | hb <;>
    rcases hcover c with hc | hc <;> aesop

lemma diam_pos (hc : G.Connected) (hcard : 3 ≤ Fintype.card V) : 0 < G.diam := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := V)).mp (by omega)
  have hdist : G.dist a b ≠ 0 :=
    dist_ne_zero_iff_ne_and_reachable.mpr ⟨hab, hc.preconnected a b⟩
  exact (Nat.pos_of_ne_zero hdist).trans_le (MetricBounds.dist_le_diameter G hc a b)

lemma diametral_distinct (hc : G.Connected) (hcard : 3 ≤ Fintype.card V)
    {x y : V} (hxy : Challenge.IsDiametral G x y) : x ≠ y := by
  intro he
  subst y
  have hd := diam_pos G hc hcard
  change G.dist x x = G.diam at hxy
  rw [G.dist_self] at hxy
  omega

lemma triametral_of_two (hc : G.Connected) (hT : Challenge.triameter G = 2 * G.diam)
    {x y : V} (hxy : Challenge.IsDiametral G x y) (z : V) :
    Challenge.IsTriametral G x y z := by
  apply le_antisymm (MetricBounds.triDist_le_triameter G x y z)
  rw [hT]
  exact MetricBounds.triDist_pair_lower G hc hxy z

end Readings

theorem check_Sec2_peripheral_iff : Challenge.Sec2_peripheral_iff := by
  intro V _ G hc u
  exact Readings.peripheral_iff_pair G hc u

theorem check_Sec2_Q3_imp_Q3' : Challenge.Sec2_Q3_imp_Q3' := by
  intro V _ G hc h
  exact Readings.question3'_of_question3 G hc h

theorem check_Sec2_Q4_imp_Q4' : Challenge.Sec2_Q4_imp_Q4' := by
  intro V _ G hc h
  exact Readings.question4'_of_question4 G hc h

theorem check_Sec2_repeated : Challenge.Sec2_repeated := by
  intro V _ G hc u v
  exact ⟨MetricBounds.triDist_repeated G u v,
    MetricBounds.triDist_le_triameter G u u v, Readings.repeated_iff G hc u v⟩

theorem check_Sec2_readings_Q3 : Challenge.Sec2_readings_Q3 := by
  classical
  intro V _ G hc
  constructor
  · constructor
    · intro h a b c _hab _hac _hbc htri
      exact h a b c htri
    · intro h a b c htri
      by_cases hab : a = b
      · exact Readings.repeated_has_diametral G hc htri (Or.inl hab)
      by_cases hac : a = c
      · exact Readings.repeated_has_diametral G hc htri (Or.inr (Or.inl hac))
      by_cases hbc : b = c
      · exact Readings.repeated_has_diametral G hc htri (Or.inr (Or.inr hbc))
      exact h a b c hab hac hbc htri
  · constructor
    · intro h a b c _hab _hac _hbc htri
      exact h a b c htri
    · intro h a b c htri
      by_cases hrep : a = b ∨ a = c ∨ b = c
      · rcases Readings.repeated_has_diametral G hc htri hrep with hd | hd | hd
        · exact Or.inl (Readings.peripheral_of_diametral G hc hd)
        · exact Or.inl (Readings.peripheral_of_diametral G hc hd)
        · exact Or.inr (Or.inl (Readings.peripheral_of_diametral G hc hd))
      · have hab : a ≠ b := fun he => hrep (Or.inl he)
        have hac : a ≠ c := fun he => hrep (Or.inr (Or.inl he))
        have hbc : b ≠ c := fun he => hrep (Or.inr (Or.inr he))
        exact h a b c hab hac hbc htri

theorem check_Sec2_readings_Q4 : Challenge.Sec2_readings_Q4 := by
  classical
  intro V _ G hc hcard
  constructor
  · constructor
    · intro h x y hxy
      by_cases hT : Challenge.triameter G = 2 * G.diam
      · obtain ⟨z, hzx, hzy⟩ := Readings.exists_outside_pair hcard x y
        exact ⟨z, hzx, hzy, Readings.triametral_of_two G hc hT hxy z⟩
      · obtain ⟨z, hz⟩ := h x y hxy
        obtain ⟨hxy', hxz, hyz⟩ := Readings.triametral_distinct_of_ne_two G hc hT hz
        exact ⟨z, Ne.symm hxz, Ne.symm hyz, hz⟩
    · intro h x y hxy
      obtain ⟨z, hzx, hzy, hz⟩ := h x y hxy
      exact ⟨z, hz⟩
  · constructor
    · intro h x hx
      by_cases hT : Challenge.triameter G = 2 * G.diam
      · obtain ⟨y, hxy⟩ := (Readings.peripheral_iff_pair G hc x).mp hx
        have hne := Readings.diametral_distinct G hc hcard hxy
        obtain ⟨z, hzx, hzy⟩ := Readings.exists_outside_pair hcard x y
        exact ⟨y, z, hne, Ne.symm hzx, Ne.symm hzy,
          Readings.triametral_of_two G hc hT hxy z⟩
      · obtain ⟨y, z, htri⟩ := h x hx
        obtain ⟨hxy, hxz, hyz⟩ := Readings.triametral_distinct_of_ne_two G hc hT htri
        exact ⟨y, z, hxy, hxz, hyz, htri⟩
    · intro h x hx
      obtain ⟨y, z, hxy, hxz, hyz, htri⟩ := h x hx
      exact ⟨y, z, htri⟩

#print axioms check_Sec2_repeated
#print axioms check_Sec2_readings_Q3
#print axioms check_Sec2_readings_Q4
#print axioms check_Sec2_peripheral_iff
#print axioms check_Sec2_Q3_imp_Q3'
#print axioms check_Sec2_Q4_imp_Q4'
end CodexPaper4
