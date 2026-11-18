import Research.TaskH.Gao.ActualSimpleEarExtension

/-! Inclusion-maximal ordinary two-connected regions have one genuine
attachment per actual outside component; no block-cover/ear witness is input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem maximal_twoConnected_region_single_attachment [Fintype V]
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (hG : G.Connected) (hS : TwoConnected (G.induce S))
    (hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S) :
    SingleAttachmentCarrier G S := by
  classical
  intro C
  let D := componentRegion C Set.univ
  have hDS : Disjoint D S := componentRegion_disjoint C Set.univ
  obtain ⟨vr, _hvr⟩ := C.nonempty_supp
  let v : C.supp := ⟨vr, _hvr⟩
  obtain ⟨r⟩ := hS.2.1.nonempty
  have hvD : componentVertex C v ∈ D := ⟨v, Set.mem_univ v, rfl⟩
  have hrD : r.1 ∉ D := fun hr => Set.disjoint_left.mp hDS hr r.2
  obtain ⟨u, huD, a, haD, eua⟩ := reachable_crosses_vertex_set G D
    (componentVertex C v) r.1 hvD hrD (hG (componentVertex C v) r.1)
  obtain ⟨ur, _hur, heu⟩ := huD
  have eaS : a ∈ S := by
    by_contra haS
    have e : (G.induce Sᶜ).Adj ur.1 ⟨a, haS⟩ :=
      Eq.mpr (congrArg (fun u : V => G.Adj u a) heu) eua
    let ar : C.supp := ⟨⟨a, haS⟩, C.mem_supp_of_adj_mem_supp ur.2 e⟩
    exact haD ⟨ar, Set.mem_univ ar, rfl⟩
  let ar : S := ⟨a, eaS⟩
  have eau : G.Adj a (componentVertex C ur) :=
    Eq.mpr (congrArg (fun u : V => G.Adj a u) heu) eua.symm
  refine ⟨ar, ⟨ur, eau⟩, ?_⟩
  intro wr zr ewz
  by_contra hza
  have haz : a ≠ zr.1 := fun he => hza (Subtype.ext he.symm)
  obtain ⟨q, hq⟩ := C.connected_toSimpleGraph.exists_isPath ur wr
  let f := componentVertexHom C
  let R : G.Walk (componentVertex C ur) (componentVertex C wr) := q.map f
  have hR : R.IsPath := (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hq
  have hRS : ∀ t ∈ R.support, t ∉ S := by
    intro t ht
    change t ∈ (q.map f).support at ht
    rw [Walk.support_map] at ht
    obtain ⟨z, _hz, he⟩ := List.mem_map.mp ht
    have he' : componentVertex C z = t := he
    exact fun htS => z.1.2 (Eq.mpr (congrArg (fun t : V => t ∈ S) he') htS)
  let U : G.Walk (componentVertex C ur) zr.1 := R.append ewz.toWalk
  have hU : U.IsPath := by
    apply append_isPath_of_only_common_endpoint hR ewz.isPath_toWalk
    intro t htR htE
    have ht : t = componentVertex C wr ∨ t = zr.1 := by
      simpa only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using htE
    rcases ht with he | he
    · exact he
    · exact False.elim (hRS t htR
        (Eq.mpr (congrArg (fun t : V => t ∈ S) he) zr.2))
  have haU : a ∉ U.support := by
    intro ha
    rcases (Walk.mem_support_append_iff R ewz.toWalk).mp ha with haR | haE
    · exact hRS a haR eaS
    · have he : a = componentVertex C wr ∨ a = zr.1 := by
        simpa only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using haE
      rcases he with he | he
      · have he' : a = wr.1.1 := he
        exact wr.1.2 (Eq.mp (congrArg (fun t : V => t ∈ S) he') eaS)
      · exact haz he
  let P : G.Walk a zr.1 := Walk.cons eau U
  have hP : P.IsPath := hU.cons haU
  let T : Set V := S ∪ {t | t ∈ P.support}
  obtain ⟨iT, hTwo⟩ := twoConnected_union_simple_ear G S hS a zr.1 eaS zr.2 haz P hP
  have hTS : T ⊆ S := hmax T iT Set.subset_union_left hTwo
  have huP : componentVertex C ur ∈ P.support := by
    change componentVertex C ur ∈ a :: U.support
    exact List.mem_cons_of_mem a U.start_mem_support
  exact ur.1.2 (hTS (Or.inr huP))

#print axioms maximal_twoConnected_region_single_attachment
end TaskH.Gao
