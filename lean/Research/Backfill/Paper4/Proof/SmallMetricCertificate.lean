import Research.Backfill.Paper4.Proof.Readings

/-! Actual graph metric semantics for small finite certificates.
The general distance proof reproduces the accepted walk argument, without importing
unrelated concrete graph certificates. All numerical hypotheses must be discharged
in separate kernel-checked modules. This helper alone completes no frozen target. -/
set_option autoImplicit false

namespace CodexPaper4.SmallMetricCertificate
open BackfillPaper4 SimpleGraph Finset

theorem dist_eq_of_certificate {V : Type*} (G : SimpleGraph V) (D : V → V → ℕ)
    (hself : ∀ x, D x x = 0)
    (hzero : ∀ x y, D x y = 0 → x = y)
    (hstep : ∀ x y, D x y ≠ 0 → ∃ z, G.Adj x z ∧ D z y + 1 = D x y)
    (hlip : ∀ u v w, G.Adj u v → D u w ≤ D v w + 1) :
    ∀ x y, G.dist x y = D x y := by
  have hwalk : ∀ n : ℕ, ∀ x y, D x y = n → ∃ p : G.Walk x y, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro x y h
      obtain rfl := hzero x y h
      exact ⟨Walk.nil, rfl⟩
    | succ n ih =>
      intro x y h
      obtain ⟨z, hxz, hz⟩ := hstep x y (by omega)
      obtain ⟨p, hp⟩ := ih z y (by omega)
      exact ⟨Walk.cons hxz p, by simp [hp]⟩
  have hlow : ∀ x y (p : G.Walk x y), D x y ≤ p.length := by
    intro x y p
    induction p with
    | nil => simp [hself]
    | @cons u v w h p ih =>
      have := hlip u v w h
      simp only [Walk.length_cons]
      omega
  intro x y
  obtain ⟨p, hp⟩ := hwalk _ x y rfl
  apply le_antisymm
  · exact (SimpleGraph.dist_le p).trans hp.le
  · have hr : G.Reachable x y := ⟨p⟩
    obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    exact hq ▸ hlow x y q

theorem connected_of_dist {V : Type*} [Nonempty V] (G : SimpleGraph V)
    (D : V → V → ℕ) (hD : ∀ x y, G.dist x y = D x y)
    (hzero : ∀ x y, D x y = 0 → x = y) : G.Connected := by
  refine ⟨fun x y => ?_⟩
  by_cases hxy : x = y
  · exact hxy ▸ Reachable.refl _
  · apply Reachable.of_dist_ne_zero
    intro hz
    exact hxy (hzero x y (by rwa [hD] at hz))

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (D : V → V → ℕ)

theorem diam_eq_of_table (hc : G.Connected) (hD : ∀ x y, G.dist x y = D x y)
    (m : ℕ) (hle : ∀ x y, D x y ≤ m) (a b : V) (hw : D a b = m) :
    G.diam = m := by
  have : Nonempty V := hc.nonempty
  apply le_antisymm
  · obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
    rw [← hxy, hD]
    exact hle x y
  · rw [← hw, ← hD]
    exact MetricBounds.dist_le_diameter G hc a b

theorem triameter_eq_of_table (hD : ∀ x y, G.dist x y = D x y)
    (t : ℕ) (hle : ∀ x y z, D x y + D x z + D y z ≤ t)
    (a b c : V) (hw : D a b + D a c + D b c = t) :
    Challenge.triameter G = t := by
  apply le_antisymm
  · unfold Challenge.triameter
    apply Finset.sup_le
    rintro ⟨x, y, z⟩ _
    simpa only [Challenge.triDist, hD] using hle x y z
  · have h := MetricBounds.triDist_le_triameter G a b c
    simpa only [Challenge.triDist, hD, hw] using h

theorem peripheral_iff_table (hc : G.Connected)
    (hD : ∀ x y, G.dist x y = D x y) (m : ℕ) (hm : G.diam = m) (u : V) :
    Challenge.IsPeripheral G u ↔ ∃ v, D u v = m := by
  rw [Readings.peripheral_iff_pair G hc u]
  simp only [Challenge.IsPeripheralPair, Challenge.IsDiametral, hD, hm]

theorem triametral_iff_table (hD : ∀ x y, G.dist x y = D x y)
    (t : ℕ) (ht : Challenge.triameter G = t) (a b c : V) :
    Challenge.IsTriametral G a b c ↔ D a b + D a c + D b c = t := by
  simp only [Challenge.IsTriametral, Challenge.triDist, hD, ht]

theorem question3'_of_table (hc : G.Connected)
    (hD : ∀ x y, G.dist x y = D x y) (m t : ℕ)
    (hm : G.diam = m) (ht : Challenge.triameter G = t)
    (hQ : ∀ a b c, D a b + D a c + D b c = t →
      (∃ z, D a z = m) ∨ (∃ z, D b z = m) ∨ (∃ z, D c z = m)) :
    Challenge.Question3' G := by
  intro a b c h
  rcases hQ a b c ((triametral_iff_table G D hD t ht a b c).mp h) with ha | hb | hc'
  · exact Or.inl ((peripheral_iff_table G D hc hD m hm a).mpr ha)
  · exact Or.inr (Or.inl ((peripheral_iff_table G D hc hD m hm b).mpr hb))
  · exact Or.inr (Or.inr ((peripheral_iff_table G D hc hD m hm c).mpr hc'))

theorem question4_of_table (hD : ∀ x y, G.dist x y = D x y)
    (m t : ℕ) (hm : G.diam = m) (ht : Challenge.triameter G = t)
    (hQ : ∀ x y, D x y = m → ∃ z, D x y + D x z + D y z = t) :
    Challenge.Question4 G := by
  intro x y h
  have hxy : D x y = m := by
    simpa only [Challenge.IsDiametral, hD, hm] using h
  obtain ⟨z, hz⟩ := hQ x y hxy
  exact ⟨z, (triametral_iff_table G D hD t ht x y z).mpr hz⟩

omit [Fintype V] in
theorem median_of_table (hc : G.Connected) (hD : ∀ x y, G.dist x y = D x y)
    (hM : ∀ u v w, ∃! x,
      (D u x + D x v = D u v) ∧
      (D u x + D x w = D u w) ∧ (D v x + D x w = D v w)) :
    Challenge.IsMedian G := by
  refine ⟨hc, ?_⟩
  simpa only [Challenge.InInterval, hD] using hM

omit [Fintype V] in
theorem not_median_of_two (hD : ∀ x y, G.dist x y = D x y)
    (a b c x y : V) (hne : x ≠ y)
    (hx : (D a x + D x b = D a b) ∧
      (D a x + D x c = D a c) ∧ (D b x + D x c = D b c))
    (hy : (D a y + D y b = D a b) ∧
      (D a y + D y c = D a c) ∧ (D b y + D y c = D b c)) :
    ¬ Challenge.IsMedian G := by
  intro hm
  obtain ⟨z, _, hu⟩ := hm.2 a b c
  have hx' : Challenge.InInterval G a b x ∧ Challenge.InInterval G a c x ∧
      Challenge.InInterval G b c x := by
    simpa only [Challenge.InInterval, hD] using hx
  have hy' : Challenge.InInterval G a b y ∧ Challenge.InInterval G a c y ∧
      Challenge.InInterval G b c y := by
    simpa only [Challenge.InInterval, hD] using hy
  exact hne ((hu x hx').trans (hu y hy').symm)

#print axioms dist_eq_of_certificate
#print axioms connected_of_dist
#print axioms diam_eq_of_table
#print axioms triameter_eq_of_table
#print axioms question3'_of_table
#print axioms question4_of_table
#print axioms median_of_table
#print axioms not_median_of_two

end CodexPaper4.SmallMetricCertificate
