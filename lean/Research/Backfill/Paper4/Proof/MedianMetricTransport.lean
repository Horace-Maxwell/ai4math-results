import Research.Backfill.Paper4.Proof.DHExtensionCore
import Research.Backfill.Paper4.Proof.Readings

/-! Transport of the frozen median and triameter questions along true graph isomorphisms.
Finite maxima are transported over the entire vertex type; repeated endpoints and singleton
connected graphs are included. Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.MedianMetricTransport
open BackfillPaper4 SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem dist_eq (e : G ≃g H) (hc : G.Connected) (u v : V) :
    H.dist (e u) (e v) = G.dist u v :=
  DHExtensionCore.iso_dist_eq e hc u v

theorem triDist_eq (e : G ≃g H) (hc : G.Connected) (a b c : V) :
    Challenge.triDist H (e a) (e b) (e c) = Challenge.triDist G a b c := by
  unfold Challenge.triDist
  rw [dist_eq e hc, dist_eq e hc, dist_eq e hc]

theorem inInterval_iff (e : G ≃g H) (hc : G.Connected) (u v x : V) :
    Challenge.InInterval H (e u) (e v) (e x) ↔ Challenge.InInterval G u v x := by
  unfold Challenge.InInterval
  rw [dist_eq e hc, dist_eq e hc, dist_eq e hc]

/-- Median graphs already contain their connectedness assumption. -/
theorem isMedian_map (e : G ≃g H) (hm : Challenge.IsMedian G) :
    Challenge.IsMedian H := by
  refine ⟨e.connected_iff.mp hm.1, ?_⟩
  intro u v w
  obtain ⟨a, rfl⟩ := e.surjective u
  obtain ⟨b, rfl⟩ := e.surjective v
  obtain ⟨c, rfl⟩ := e.surjective w
  obtain ⟨x, hx, huniq⟩ := hm.2 a b c
  refine ⟨e x, ⟨(inInterval_iff e hm.1 a b x).mpr hx.1,
    (inInterval_iff e hm.1 a c x).mpr hx.2.1,
    (inInterval_iff e hm.1 b c x).mpr hx.2.2⟩, ?_⟩
  intro y hy
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz : z = x := huniq z ⟨(inInterval_iff e hm.1 a b z).mp hy.1,
    (inInterval_iff e hm.1 a c z).mp hy.2.1,
    (inInterval_iff e hm.1 b c z).mp hy.2.2⟩
  exact congrArg e hz

theorem isMedian_iff (e : G ≃g H) :
    Challenge.IsMedian G ↔ Challenge.IsMedian H :=
  ⟨isMedian_map e, isMedian_map e.symm⟩

variable [Fintype V] [Fintype W]

theorem diam_eq (e : G ≃g H) (hc : G.Connected) : H.diam = G.diam := by
  have hcH : H.Connected := e.connected_iff.mp hc
  have : Nonempty V := hc.nonempty
  have : Nonempty W := hcH.nonempty
  apply le_antisymm
  · obtain ⟨x, y, hxy⟩ := H.exists_dist_eq_diam
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    calc
      H.diam = H.dist (e u) (e v) := hxy.symm
      _ = G.dist u v := dist_eq e hc u v
      _ ≤ G.diam := MetricBounds.dist_le_diameter G hc u v
  · obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    calc
      G.diam = G.dist u v := huv.symm
      _ = H.dist (e u) (e v) := (dist_eq e hc u v).symm
      _ ≤ H.diam := MetricBounds.dist_le_diameter H hcH (e u) (e v)

theorem triameter_le (e : G ≃g H) (hc : G.Connected) :
    Challenge.triameter H ≤ Challenge.triameter G := by
  unfold Challenge.triameter
  apply Finset.sup_le
  rintro ⟨x, y, z⟩ _
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  obtain ⟨c, rfl⟩ := e.surjective z
  change Challenge.triDist H (e a) (e b) (e c) ≤ Challenge.triameter G
  rw [triDist_eq e hc]
  exact MetricBounds.triDist_le_triameter G a b c

theorem triameter_eq (e : G ≃g H) (hc : G.Connected) :
    Challenge.triameter H = Challenge.triameter G :=
  le_antisymm (triameter_le e hc) (triameter_le e.symm (e.connected_iff.mp hc))

theorem isDiametral_iff (e : G ≃g H) (hc : G.Connected) (u v : V) :
    Challenge.IsDiametral H (e u) (e v) ↔ Challenge.IsDiametral G u v := by
  unfold Challenge.IsDiametral
  rw [dist_eq e hc, diam_eq e hc]

theorem isTriametral_iff (e : G ≃g H) (hc : G.Connected) (a b c : V) :
    Challenge.IsTriametral H (e a) (e b) (e c) ↔ Challenge.IsTriametral G a b c := by
  unfold Challenge.IsTriametral
  rw [triDist_eq e hc, triameter_eq e hc]

/-- Using the already proved pair reading avoids imposing extra restrictions on peripheral
vertices or on the number of vertices. -/
theorem isPeripheral_iff (e : G ≃g H) (hc : G.Connected) (u : V) :
    Challenge.IsPeripheral H (e u) ↔ Challenge.IsPeripheral G u := by
  rw [Readings.peripheral_iff_pair H (e.connected_iff.mp hc) (e u),
    Readings.peripheral_iff_pair G hc u]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := e.surjective y
    exact ⟨v, (isDiametral_iff e hc u v).mp hy⟩
  · rintro ⟨v, hv⟩
    exact ⟨e v, (isDiametral_iff e hc u v).mpr hv⟩

theorem question3'_map (e : G ≃g H) (hc : G.Connected)
    (h : Challenge.Question3' G) : Challenge.Question3' H := by
  intro x y z htri
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  obtain ⟨c, rfl⟩ := e.surjective z
  rcases h a b c ((isTriametral_iff e hc a b c).mp htri) with ha | hb | hc'
  · exact Or.inl ((isPeripheral_iff e hc a).mpr ha)
  · exact Or.inr (Or.inl ((isPeripheral_iff e hc b).mpr hb))
  · exact Or.inr (Or.inr ((isPeripheral_iff e hc c).mpr hc'))

theorem question3'_iff (e : G ≃g H) (hc : G.Connected) :
    Challenge.Question3' G ↔ Challenge.Question3' H :=
  ⟨question3'_map e hc, question3'_map e.symm (e.connected_iff.mp hc)⟩

theorem question4_map (e : G ≃g H) (hc : G.Connected)
    (h : Challenge.Question4 G) : Challenge.Question4 H := by
  intro x y hdiam
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  obtain ⟨c, hc'⟩ := h a b ((isDiametral_iff e hc a b).mp hdiam)
  exact ⟨e c, (isTriametral_iff e hc a b c).mpr hc'⟩

theorem question4_iff (e : G ≃g H) (hc : G.Connected) :
    Challenge.Question4 G ↔ Challenge.Question4 H :=
  ⟨question4_map e hc, question4_map e.symm (e.connected_iff.mp hc)⟩

theorem question4'_map (e : G ≃g H) (hc : G.Connected)
    (h : Challenge.Question4' G) : Challenge.Question4' H := by
  intro x hx
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, c, htri⟩ := h a ((isPeripheral_iff e hc a).mp hx)
  exact ⟨e b, e c, (isTriametral_iff e hc a b c).mpr htri⟩

theorem question4'_iff (e : G ≃g H) (hc : G.Connected) :
    Challenge.Question4' G ↔ Challenge.Question4' H :=
  ⟨question4'_map e hc, question4'_map e.symm (e.connected_iff.mp hc)⟩

#print axioms dist_eq
#print axioms diam_eq
#print axioms triameter_eq
#print axioms isMedian_iff
#print axioms question3'_iff
#print axioms question4_iff
#print axioms question4'_iff

end CodexPaper4.MedianMetricTransport
