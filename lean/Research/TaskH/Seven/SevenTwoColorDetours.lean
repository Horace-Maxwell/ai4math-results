import Research.TaskH.Seven.SevenTwoColorClosing

/-! Explicit detours in the actual original graph.  The length-three detour
has four edges; the length-nine detour has five.  Their interiors are proved
disjoint from the actual two-color path using its colors and the deleted root.
The two same-colored pair vertices in the five-edge detour remain distinct
as actual vertices; they are not silently identified. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem twoColorDeletedLift_mem_colors (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b : {z : V // z ≠ v}} (beta : Fin 7)
    (p : (G.induce {x | x ≠ v}).Walk a b)
    (hf : Follows p c (Equiv.swap (c a) beta)) {z : V}
    (hz : z ∈ (twoColorDeletedLift v p).support) :
    ∃ w : {x : V // x ≠ v}, w.val = z ∧ (c w = c a ∨ c w = beta) := by
  have hsupport : (twoColorDeletedLift v p).support = p.support.map Subtype.val :=
    Walk.support_map (twoColorDeletedHom v) p
  rw [hsupport, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨n, hn, hle⟩ := Walk.mem_support_iff_exists_getVert.mp hw
  refine ⟨w, rfl, ?_⟩
  have hc := twoColor_color_at p c beta hf n hle
  rw [hn] at hc
  by_cases he : n % 2 = 0
  · exact Or.inl (by simpa only [ite_eq_left he] using hc)
  · exact Or.inr (by simpa only [ite_eq_right he] using hc)

theorem twoColorDeletedLift_detour_disjoint (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b : {z : V // z ≠ v}} (beta : Fin 7)
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c a) beta)) (q : G.Walk b.val a.val)
    (hqcolors : ∀ z ∈ q.support.tail, z = a.val ∨ z = v ∨
      ∃ w : {x : V // x ≠ v}, w.val = z ∧ c w ≠ c a ∧ c w ≠ beta) :
    (twoColorDeletedLift v p).support.tail.Disjoint q.support.tail := by
  rw [List.disjoint_left]
  intro z hz hqz
  have hzs : z ∈ (twoColorDeletedLift v p).support := List.mem_of_mem_tail hz
  rcases hqcolors z hqz with he | he | ⟨w, hw, hwa, hwb⟩
  · subst z
    have hn := (twoColorDeletedLift_isPath v p hp).support_nodup
    rw [← Walk.cons_tail_support (twoColorDeletedLift v p)] at hn
    exact (List.nodup_cons.mp hn).1 hz
  · subst z
    exact twoColorDeletedLift_avoids_root v p hzs
  · obtain ⟨w', hw', hca | hcb⟩ := twoColorDeletedLift_mem_colors v c beta p hf hzs
    · have he : w' = w := Subtype.ext (hw'.trans hw.symm)
      subst w'
      exact hwa hca
    · have he : w' = w := Subtype.ext (hw'.trans hw.symm)
      subst w'
      exact hwb hcb

theorem twoColor_path_length_ne_three (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b s t : {z : V // z ≠ v}} (beta : Fin 7)
    (hbeta : beta ≠ c a) (hend : c b = beta)
    (hsa : c s ≠ c a) (hsb : c s ≠ beta)
    (hta : c t ≠ c a) (htb : c t ≠ beta) (hst : c s ≠ c t)
    (hbs : G.Adj b.val s.val) (hsv : G.Adj s.val v)
    (hvt : G.Adj v t.val) (htaedge : G.Adj t.val a.val)
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c a) beta)) : p.length ≠ 3 := by
  intro hl
  have hab : a.val ≠ b.val := by
    intro he
    have he' := congrArg c (Subtype.ext he : a = b)
    exact hbeta (hend.symm.trans he'.symm)
  have hsa' : s.val ≠ a.val := fun he => hsa (congrArg c (Subtype.ext he))
  have hsb' : s.val ≠ b.val := fun he => hsb ((congrArg c (Subtype.ext he)).trans hend)
  have hta' : t.val ≠ a.val := fun he => hta (congrArg c (Subtype.ext he))
  have htb' : t.val ≠ b.val := fun he => htb ((congrArg c (Subtype.ext he)).trans hend)
  have hst' : s.val ≠ t.val := fun he => hst (congrArg c (Subtype.ext he))
  let q : G.Walk b.val a.val := .cons hbs (.cons hsv (.cons hvt (.cons htaedge .nil)))
  have hq : q.IsPath := by
    simp [q, Walk.cons_isPath_iff, Ne.symm hab, hsa', hta', hst',
      Ne.symm hsb', Ne.symm htb', b.property, s.property,
      Ne.symm a.property, Ne.symm t.property]
  have hdis := twoColorDeletedLift_detour_disjoint v c beta p hp hf q (by
    intro z hz
    change z ∈ [s.val, v, t.val, a.val] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨s, rfl, hsa, hsb⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨t, rfl, hta, htb⟩)
    · exact Or.inl rfl)
  let r := (twoColorDeletedLift v p).append q
  have hlength : (twoColorDeletedLift v p).length = p.length :=
    Walk.length_map (twoColorDeletedHom v) p
  have hrC : r.IsCycle := (twoColorDeletedLift_isPath v p hp).isCycle_append hq hdis
    (Or.inl (by rw [hlength]; omega))
  have hrl : r.length = 7 := by
    change ((twoColorDeletedLift v p).append q).length = 7
    rw [Walk.length_append, hlength]
    change p.length + 4 = 7
    omega
  have hm (n : ℕ) (hn : n ≤ p.length) : (p.getVert n).val ∈ r.support := by
    apply Walk.support_subset_support_append_left _ _
    have hsupport : (twoColorDeletedLift v p).support = p.support.map Subtype.val :=
      Walk.support_map (twoColorDeletedHom v) p
    rw [hsupport, List.mem_map]
    exact ⟨p.getVert n, Walk.mem_support_iff_exists_getVert.mpr ⟨n, rfl, hn⟩, rfl⟩
  have hc2 : c (p.getVert 2) = c (p.getVert 0) := by
    simpa using twoColor_color_at p c beta hf 2 (by omega)
  have he := hr v c r hrC hrl (p.getVert 0) (p.getVert 2) (hm 0 (by omega))
    (hm 2 (by omega)) hc2.symm
  have hn := hp.getVert_injOn (by change 0 ≤ p.length; omega)
    (by change 2 ≤ p.length; omega) he
  omega

theorem twoColor_path_length_ne_nine (hs : ShortSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b s t u : {z : V // z ≠ v}} (beta : Fin 7)
    (hbeta : beta ≠ c a) (hend : c b = beta)
    (hsa : c s ≠ c a) (hsb : c s ≠ beta)
    (hta : c t ≠ c a) (htb : c t ≠ beta)
    (hucolor : c u = c t) (htu : t ≠ u) (hst : c s ≠ c t)
    (hbs : G.Adj b.val s.val) (hstedge : G.Adj s.val t.val)
    (htv : G.Adj t.val v) (hvu : G.Adj v u.val) (hua : G.Adj u.val a.val)
    (p : (G.induce {x | x ≠ v}).Walk a b) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c a) beta)) : p.length ≠ 9 := by
  intro hl
  have hab : a.val ≠ b.val := by
    intro he
    have he' := congrArg c (Subtype.ext he : a = b)
    exact hbeta (hend.symm.trans he'.symm)
  have hsa' : s.val ≠ a.val := fun he => hsa (congrArg c (Subtype.ext he))
  have hsb' : s.val ≠ b.val := fun he => hsb ((congrArg c (Subtype.ext he)).trans hend)
  have hta' : t.val ≠ a.val := fun he => hta (congrArg c (Subtype.ext he))
  have htb' : t.val ≠ b.val := fun he => htb ((congrArg c (Subtype.ext he)).trans hend)
  have hua' : u.val ≠ a.val := fun he => hta (hucolor.symm.trans (congrArg c (Subtype.ext he)))
  have hub' : u.val ≠ b.val := fun he => htb (hucolor.symm.trans ((congrArg c (Subtype.ext he)).trans hend))
  have hst' : s.val ≠ t.val := fun he => hst (congrArg c (Subtype.ext he))
  have hsu' : s.val ≠ u.val := fun he => hst ((congrArg c (Subtype.ext he)).trans hucolor)
  have htu' : t.val ≠ u.val := fun he => htu (Subtype.ext he)
  let q : G.Walk b.val a.val :=
    .cons hbs (.cons hstedge (.cons htv (.cons hvu (.cons hua .nil))))
  have hq : q.IsPath := by
    simp [q, Walk.cons_isPath_iff, Ne.symm hab, hsa', hta', hua', hst', hsu', htu',
      Ne.symm hsb', Ne.symm htb', Ne.symm hub', b.property, s.property, t.property,
      Ne.symm a.property, Ne.symm u.property]
  have hdis := twoColorDeletedLift_detour_disjoint v c beta p hp hf q (by
    intro z hz
    change z ∈ [s.val, t.val, v, u.val, a.val] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨s, rfl, hsa, hsb⟩)
    · exact Or.inr (Or.inr ⟨t, rfl, hta, htb⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨u, rfl, by simpa [hucolor] using hta, by simpa [hucolor] using htb⟩)
    · exact Or.inl rfl)
  let r := (twoColorDeletedLift v p).append q
  have hlength : (twoColorDeletedLift v p).length = p.length :=
    Walk.length_map (twoColorDeletedHom v) p
  have hrC : r.IsCycle := (twoColorDeletedLift_isPath v p hp).isCycle_append hq hdis
    (Or.inl (by rw [hlength]; omega))
  have hrl : r.length = 14 := by
    change ((twoColorDeletedLift v p).append q).length = 14
    rw [Walk.length_append, hlength]
    change p.length + 5 = 14
    omega
  have hseven := hs r hrC (by rw [hrl]; omega)
  omega

end TaskH.Seven
#print axioms TaskH.Seven.twoColorDeletedLift_mem_colors
#print axioms TaskH.Seven.twoColorDeletedLift_detour_disjoint
#print axioms TaskH.Seven.twoColor_path_length_ne_three
#print axioms TaskH.Seven.twoColor_path_length_ne_nine
