import Research.TaskH.Seven.SevenTwoColorPaths
import Research.TaskH.General.TwoColorSingletonPathOriginal
import Research.TaskH.General.WholeClassCardOriginal

/-! Parameter-uniform transport of ACTUAL two-color paths in the whole G-v.
The namespace of the reused two-color construction is historical: its type
parameters are arbitrary, and no fixed-seven equality theorem is invoked. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

def originalDeletedHom (v : V) : G.induce {z | z ≠ v} →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

def originalDeletedLift (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {z | z ≠ v}).Walk a b) : G.Walk a.val b.val :=
  p.map (originalDeletedHom v)

theorem originalDeletedLift_isPath (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {z | z ≠ v}).Walk a b) (hp : p.IsPath) :
    (originalDeletedLift v p).IsPath :=
  hp.map (show Function.Injective (originalDeletedHom (G := G) v) from Subtype.val_injective)

theorem originalDeletedLift_avoids_root (v : V) {a b : {z : V // z ≠ v}}
    (p : (G.induce {z | z ≠ v}).Walk a b) :
    v ∉ (originalDeletedLift v p).support := by
  change v ∉ (p.map (originalDeletedHom (G := G) v)).support
  rw [Walk.support_map, List.mem_map]
  rintro ⟨z, _, he⟩
  exact z.property he

theorem originalDeletedLift_mem_colors (v : V)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    {a b : {z : V // z ≠ v}} (γ : Fin k)
    (p : (G.induce {z | z ≠ v}).Walk a b)
    (hf : _root_.TaskH.Follows p c (Equiv.swap (c a) γ))
    {z : V} (hz : z ∈ (originalDeletedLift v p).support) :
    ∃ w : {z : V // z ≠ v}, w.val = z ∧ (c w = c a ∨ c w = γ) := by
  change z ∈ (p.map (originalDeletedHom (G := G) v)).support at hz
  rw [Walk.support_map, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨n, hn, hle⟩ := Walk.mem_support_iff_exists_getVert.mp hw
  refine ⟨w, rfl, ?_⟩
  have hc := _root_.TaskH.Seven.twoColor_color_at p c γ hf n hle
  rw [hn] at hc
  by_cases he : n % 2 = 0
  · exact Or.inl (by simpa only [ite_eq_left he] using hc)
  · exact Or.inr (by simpa only [ite_eq_right he] using hc)

theorem wholeDeletedColorClass_subtype_card [Fintype V] {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k) :
    (Finset.univ.filter (fun z : {z : V // z ≠ v} => c z = γ)).card =
      (wholeDeletedColorClass c γ).card := by
  classical
  let S := Finset.univ.filter (fun z : {z : V // z ≠ v} => c z = γ)
  have he : S.image Subtype.val = wholeDeletedColorClass c γ := by
    ext z
    rw [Finset.mem_image, mem_wholeDeletedColorClass]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w ∈ Finset.univ.filter (fun z : {z : V // z ≠ v} => c z = γ) at hw
      have hwc : c w = γ := (Finset.mem_filter.mp hw).2
      exact ⟨w.property, hwc⟩
    · rintro ⟨hzv, hc⟩
      refine ⟨⟨z, hzv⟩, ?_, rfl⟩
      change (⟨z, hzv⟩ : {z : V // z ≠ v}) ∈
        Finset.univ.filter (fun w : {z : V // z ≠ v} => c w = γ)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rw [← he, Finset.card_image_of_injective _ Subtype.val_injective]

/-- The actual locked row is internally chosen as a shortest simple path.
Its lower bound comes from original short spokes and its upper bound counts
the ENTIRE actual old singleton color class, not the root fiber. -/
theorem equality_original_locked_path_range [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (a b q : {z : V // z ≠ v}) (hva : G.Adj v a.val) (hvb : G.Adj v b.val)
    (hvq : G.Adj v q.val)
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c a → z = a.val)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c b → z = b.val)
    (habcolor : c a ≠ c b) (hqa : c q ≠ c a) (haq : ¬G.Adj a.val q.val)
    (hreach : q ∈ _root_.TaskH.Seven.twoColorComponent c (c a) (c q) a) :
    ∃ p : (G.induce {z | z ≠ v}).Walk a q,
      p.IsPath ∧ _root_.TaskH.Follows p c (Equiv.swap (c a) (c q)) ∧
      p.length % 2 = 1 ∧ k - 1 ≤ p.length ∧ p.length ≤ 2 * k - 5 := by
  classical
  obtain ⟨p, hp, hf, _, hpos, hodd⟩ :=
    _root_.TaskH.Seven.twoColor_exists_shortest c (c q) hqa rfl hreach
  have hlen1 : p.length ≠ 1 := by
    intro he
    have eaq : (G.induce {z | z ≠ v}).Adj a q :=
      Walk.adj_of_length_eq_one (p := p) he
    exact haq eaq
  have hlen2 : 2 ≤ p.length := by omega
  have hmaplen : (originalDeletedLift v p).length = p.length := by
    change (p.map (originalDeletedHom (G := G) v)).length = p.length
    exact Walk.length_map (originalDeletedHom (G := G) v) p
  have ht : ∀ (z : V) (hzv : z ≠ v), z ∈ (originalDeletedLift v p).support →
      c ⟨z, hzv⟩ = c a ∨ c ⟨z, hzv⟩ = c q := by
    intro z hzv hz
    obtain ⟨w, hw, hc⟩ := originalDeletedLift_mem_colors v c (c q) p hf hz
    have he : w = (⟨z, hzv⟩ : {z : V // z ≠ v}) := Subtype.ext hw
    simpa only [he] using hc
  have hlo := equality_original_two_color_singleton_path_long hk hcrit hcount
    hvb hva c hbunique haunique habcolor.symm (originalDeletedLift v p)
    (originalDeletedLift_isPath v p hp) (originalDeletedLift_avoids_root v p)
    hvq.symm (by rw [hmaplen]; exact hlen2) (c q) ht
  have hclass := equality_singleton_whole_class_card_le hk hcrit hcount
    hva hvb c haunique hbunique habcolor
  have hsub : (Finset.univ.filter (fun z : {z : V // z ≠ v} => c z = c a)).card ≤ k - 2 := by
    rw [wholeDeletedColorClass_subtype_card]
    exact hclass
  have hup := _root_.TaskH.Seven.twoColor_odd_path_length_le p c (c q) hp hf hodd
    (k - 2) hsub
  have hlo' : k - 1 ≤ p.length :=
    Eq.mp (congrArg (fun n : ℕ => k - 1 ≤ n) hmaplen) hlo
  exact ⟨p, hp, hf, hodd, hlo', by omega⟩

end TaskH.General
#print axioms TaskH.General.originalDeletedHom
#print axioms TaskH.General.originalDeletedLift
#print axioms TaskH.General.originalDeletedLift_isPath
#print axioms TaskH.General.originalDeletedLift_avoids_root
#print axioms TaskH.General.originalDeletedLift_mem_colors
#print axioms TaskH.General.wholeDeletedColorClass_subtype_card
#print axioms TaskH.General.equality_original_locked_path_range
