import Research.TaskJ.Grid.GridPadding
import Research.TaskJ.Grid.GridEndpoints

namespace Grid.Pad

open Challenge

abbrev CleanIncident (ds : List ℕ) (p : List Point) : Prop :=
  ∀ a ∈ p, Touches (fun x y => defect ds x y = 0) p a

structure Inserted (ds : List ℕ) (p q : List Point) (u v : Point) : Prop where
  perm : q.Perm (u::v::p)
  head : q.head? = p.head?
  last : q.getLast? = p.getLast?
  loss : edgeLoss ds q = edgeLoss ds p
  incident : CleanIncident ds q

private theorem insert_at {ds : List ℕ} {p : List Point} (hi : CleanIncident ds p)
    {x y u v : Point} (hmem : (x,y) ∈ pathEdges p) (hxy : defect ds x y = 0)
    (hxu : defect ds x u = 0) (huv : defect ds u v = 0) (hvy : defect ds v y = 0) :
    ∃ q, Inserted ds p q u v := by
  obtain ⟨pre,post,rfl⟩ := split_at_edge p x y hmem
  let q := pre ++ x::u::v::y::post
  have hp : q.Perm (u::v::(pre ++ x::y::post)) := by
    have h₁ := @List.perm_middle _ u (pre ++ [x]) (v::y::post)
    have h₂ := @List.perm_middle _ v (pre ++ [x]) (y::post)
    simpa [q,List.append_assoc] using h₁.trans (h₂.cons u)
  refine ⟨q,hp,by simp [q],by simp [q],edgeLoss_splice _ _ _ _ _ _ _ hxy hxu huv hvy,?_⟩
  intro a ha
  have hm := hp.mem_iff.mp ha
  rcases List.mem_cons.mp hm with h|h
  · subst a
    refine ⟨(u,v),?_,huv,Or.inl rfl⟩
    rw [show q = pre ++ x::u::v::y::post from rfl, pathEdges_cut pre x]
    simp [pathEdges]
  rcases List.mem_cons.mp h with h|h
  · subst a
    refine ⟨(u,v),?_,huv,Or.inr rfl⟩
    rw [show q = pre ++ x::u::v::y::post from rfl, pathEdges_cut pre x]
    simp [pathEdges]
  exact touch_after_splice (fun a b => defect ds a b = 0) pre post x y u v hxu hvy (hi a h)

theorem insert_pair {ds : List ℕ} {p : List Point} (hbox : ∀ x ∈ p, x ∈ vertices ds)
    (hi : CleanIncident ds p) {a z : Point} (ha : a ∈ p) (hz : z ∈ vertices ds)
    (hs : signature ds a = signature ds z) :
    ∃ q, Inserted ds p q z (antipode ds z) := by
  obtain ⟨⟨x,y⟩,hmem,hxy,hends⟩ := hi a ha
  obtain ⟨left,right,heq⟩ := split_at_edge p x y hmem
  have hx : x ∈ vertices ds := hbox _ (by simp [heq])
  have hy : y ∈ vertices ds := hbox _ (by simp [heq])
  have hv := antipode_mem hz
  have hzv := defect_to_antipode hz
  rcases hends with rfl|rfl
  · have h1 := defect_transfer hz hx hv hs.symm hzv
    have h2 := defect_transfer hx hz hy hs hxy
    obtain ⟨q,hq⟩ := insert_at hi hmem hxy h1 (by rw [defect_comm]; exact hzv) h2
    exact ⟨q, ⟨hq.perm.trans (List.Perm.swap _ _ _),hq.head,hq.last,hq.loss,hq.incident⟩⟩
  · have h1 := defect_transfer hy hz hx hs (by rw [defect_comm];exact hxy)
    have h2 := defect_transfer hz hy hv hs.symm hzv
    exact insert_at hi hmem hxy (by rw [defect_comm];exact h1) hzv (by rw [defect_comm];exact h2)

private theorem finish_partial (ds : List ℕ) (p : List Point)
    (hn : p.Nodup) (hv : ∀ x ∈ p, x ∈ vertices ds)
    (ha : ∀ x ∈ p, antipode ds x ∈ p)
    (hs : ∀ v ∈ vertices ds, ∃ x ∈ p, signature ds x = signature ds v)
    (hi : CleanIncident ds p) :
    ∃ q, Order ds q ∧ q.head? = p.head? ∧ q.getLast? = p.getLast? ∧ edgeLoss ds q = edgeLoss ds p := by
  classical
  by_cases hall : ∀ y ∈ vertices ds, y ∈ p
  · exact ⟨p, (List.perm_ext_iff_of_nodup hn (vertices_nodup ds)).mpr (fun _ => ⟨hv _, hall _⟩),
        rfl,rfl,rfl⟩
  push Not at hall
  obtain ⟨z,hz,hm⟩ := hall
  obtain ⟨x,hx,he⟩ := hs z hz
  have hzv := antipode_mem hz
  have close := antipode_involutive hz
  have notfixed : z ≠ antipode ds z := by
    intro heq
    have := central_unique hz (hv x hx) heq.symm he.symm
    exact hm (this ▸ hx)
  have missingOpp : antipode ds z ∉ p := by
    intro ha'
    exact hm (close ▸ ha _ ha')
  obtain ⟨q,hq⟩ := insert_pair hv hi hx hz he
  have qn : q.Nodup := hq.perm.nodup_iff.mpr (by simp [hn,hm,missingOpp,notfixed])
  have qv : ∀ y ∈ q, y ∈ vertices ds := by
    intro y hy
    rcases List.mem_cons.mp (hq.perm.mem_iff.mp hy) with rfl|h
    · exact hz
    rcases List.mem_cons.mp h with rfl|h
    · exact hzv
    exact hv y h
  have qa : ∀ y ∈ q, antipode ds y ∈ q := by
    intro y hy
    apply hq.perm.mem_iff.mpr
    rcases List.mem_cons.mp (hq.perm.mem_iff.mp hy) with rfl|h
    · simp
    rcases List.mem_cons.mp h with rfl|h
    · simp [close]
    simp [ha y h]
  have qs : ∀ y ∈ vertices ds, ∃ a ∈ q, signature ds a = signature ds y := by
    intro y hy
    obtain ⟨a,ha,hsig⟩ := hs y hy
    exact ⟨a,hq.perm.mem_iff.mpr (by simp [ha]),hsig⟩
  obtain ⟨r,ho,hh,hl,hw⟩ := finish_partial ds q qn qv qa qs hq.incident
  exact ⟨r,ho,hh.trans hq.head,hl.trans hq.last,hw.trans hq.loss⟩
termination_by (vertices ds).length - p.length
decreasing_by
  have hle := List.Nodup.length_le_of_subset qn (by exact fun _ h => qv _ h)
  have heq := hq.perm.length_eq
  simp only [List.length_cons] at heq
  omega

theorem inflate (pads : Padding) (hw : Wide pads) {p : List Point} (hp : Order (inner pads) p)
    (ht : CleanIncident (inner pads) p) :
    ∃ q, Order (outer pads) q ∧ q.head? = p.head?.map (shift pads) ∧
      q.getLast? = p.getLast?.map (shift pads) ∧ edgeLoss (outer pads) q = edgeLoss (inner pads) p := by
  let f := shift pads
  have hv (x : Point) (hm : x ∈ p) : x ∈ vertices (inner pads) := hp.mem_iff.mp hm
  have hbound : ∀ a ∈ p.map f, a ∈ vertices (outer pads) := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact shift_mem (hv x hx)
  have hclosed : ∀ a ∈ p.map f, antipode (outer pads) a ∈ p.map f := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨_,hp.mem_iff.mpr (antipode_mem (hv x hx)),(antipode_shift (hv x hx)).symm⟩
  have hreal : ∀ v ∈ vertices (outer pads), ∃ a ∈ p.map f, signature (outer pads) a = signature (outer pads) v := by
    intro v hm
    obtain ⟨a,ha,he⟩ := realize_signature hw hm
    exact ⟨_,List.mem_map_of_mem (hp.mem_iff.mpr ha),he⟩
  have hn := (hp.nodup_iff.mpr (vertices_nodup _)).map_on (f := f)
    (fun x hx y hy heq => shift_inj (hv x hx) (hv y hy) heq)
  have hedge {x y : Point} (he : (x,y) ∈ pathEdges p) :
      defect (outer pads) (f x) (f y) = defect (inner pads) x y := by
    obtain ⟨l,r,h⟩ := split_at_edge p x y he
    exact defect_shift (hv _ (by simp [h])) (hv _ (by simp [h]))
  have ht' : CleanIncident (outer pads) (p.map f) := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨⟨u,v⟩,hm,hh,hend⟩ := ht x hx
    refine ⟨(f u,f v),?_,(hedge hm).trans hh,?_⟩
    · rw [pathEdges_map]
      exact List.mem_map.mpr ⟨(u,v),hm,rfl⟩
    · exact hend.imp (congrArg f) (congrArg f)
  obtain ⟨q,ho,hh,hl,hs⟩ := finish_partial (outer pads) (p.map f) hn hbound hclosed hreal ht'
  refine ⟨q,ho,by simpa [f] using hh,by simpa [f] using hl,hs.trans ?_⟩
  rw [edgeLoss_edges,edgeLoss_edges,pathEdges_map,List.map_map]
  congr 1
  exact List.map_congr_left (fun e he => hedge he)

end Grid.Pad
