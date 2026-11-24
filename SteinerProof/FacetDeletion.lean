import SteinerProof.PLComplex

/-! Erasing maximal simplices and constructing the deletion chain in Section 6.3. -/

open Set

noncomputable section

namespace FinitePlanarComplex

/-- Erasing a facet retains all of its proper faces. -/
def eraseFacet (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) : FinitePlanarComplex where
  simplices := {
    faces := K.simplices.faces \ {s}
    indep := fun ht => K.simplices.indep ht.1
    isRelLowerSet_faces := by
      intro t ht
      refine ⟨K.simplices.nonempty_of_mem_faces ht.1, ?_⟩
      intro u hut hu
      refine ⟨K.simplices.down_closed ht.1 hut hu, ?_⟩
      intro hus
      have heq : u = s := Set.mem_singleton_iff.mp hus
      exact ht.2 (Set.mem_singleton_iff.mpr
        ((Geometry.SimplicialComplex.mem_facets.mp hs).2 t ht.1 (heq ▸ hut)).symm)
    inter_subset_convexHull := fun ht hu => K.simplices.inter_subset_convexHull ht.1 hu.1 }
  finite_faces := K.finite_faces.subset Set.sdiff_subset

@[simp] theorem faces_eraseFacet (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) :
    (K.eraseFacet s hs).simplices.faces = K.simplices.faces \ {s} := rfl

theorem faceFinset_eraseFacet (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) [DecidableEq (Finset PLPoint)] :
    (K.eraseFacet s hs).faceFinset = K.faceFinset.erase s := by
  ext t
  simp [mem_faceFinset_iff, and_comm]

theorem realization_mono {A B : FinitePlanarComplex}
    (hAB : A.simplices.faces ⊆ B.simplices.faces) : A.realization ⊆ B.realization := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (A.mem_realization_iff x).mp hx
  exact B.convexHull_face_subset_realization s (hAB hs) hx

/-- The part of a simplex left after removing the hulls of its proper faces. -/
def openFace (s : Finset PLPoint) : Set PLPoint :=
  convexHull ℝ (s : Set PLPoint) \ ⋃ t : Finset PLPoint, ⋃ (_ : t ⊂ s),
    convexHull ℝ (t : Set PLPoint)

theorem realization_sdiff_eraseFacet (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) :
    K.realization \ (K.eraseFacet s hs).realization = openFace s := by
  classical
  have hsK := (Geometry.SimplicialComplex.mem_facets.mp hs).1
  ext x
  constructor
  · rintro ⟨hx, hxErase⟩
    obtain ⟨t, ht, hxt⟩ := (K.mem_realization_iff x).mp hx
    have hts : t = s := by
      by_contra hne
      exact hxErase ((K.eraseFacet s hs).convexHull_face_subset_realization t ⟨ht, hne⟩ hxt)
    subst t
    refine ⟨hxt, ?_⟩
    intro hxProper
    obtain ⟨t, htProper, hxt⟩ := Set.mem_iUnion₂.mp hxProper
    have htNonempty : t.Nonempty := by
      apply Finset.coe_nonempty.mp
      exact convexHull_nonempty_iff.mp ⟨x, hxt⟩
    obtain ⟨htsub, htne⟩ := Finset.ssubset_iff_subset_ne.mp htProper
    have htK := K.simplices.down_closed hsK htsub htNonempty
    exact hxErase ((K.eraseFacet s hs).convexHull_face_subset_realization t ⟨htK, htne⟩ hxt)
  · rintro ⟨hxs, hxProper⟩
    refine ⟨K.convexHull_face_subset_realization s hsK hxs, ?_⟩
    intro hxErase
    obtain ⟨t, ht, hxt⟩ := ((K.eraseFacet s hs).mem_realization_iff x).mp hxErase
    have hinter : s ∩ t ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have hst : s ⊆ t := heq ▸ (Finset.inter_subset_right : s ∩ t ⊆ t)
      have hstEq := (Geometry.SimplicialComplex.mem_facets.mp hs).2 t ht.1 hst
      exact ht.2 (Set.mem_singleton_iff.mpr hstEq.symm)
    have hxInter := K.simplices.inter_subset_convexHull hsK ht.1 ⟨hxs, hxt⟩
    exact hxProper (Set.mem_iUnion₂.mpr ⟨s ∩ t, hinter, by simpa only [Finset.coe_inter]
      using hxInter⟩)

theorem realization_eraseFacet_eq_sdiff (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) :
    (K.eraseFacet s hs).realization = K.realization \ openFace s := by
  rw [← realization_sdiff_eraseFacet K s hs]
  have hsubset := realization_mono (A := K.eraseFacet s hs) (B := K) Set.sdiff_subset
  ext x
  simp only [Set.mem_sdiff]
  constructor
  · exact fun hx => ⟨hsubset hx, fun h => h.2 hx⟩
  · exact fun hx => Classical.byContradiction (fun hn => hx.2 ⟨hx.1, hn⟩)

theorem realization_eq_eraseFacet_union_convexHull (K : FinitePlanarComplex)
    (s : Finset PLPoint) (hs : s ∈ K.simplices.facets) :
    K.realization = (K.eraseFacet s hs).realization ∪ convexHull ℝ (s : Set PLPoint) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := (K.mem_realization_iff x).mp hx
    by_cases heq : t = s
    · exact Or.inr (heq ▸ hxt)
    · exact Or.inl ((K.eraseFacet s hs).convexHull_face_subset_realization t ⟨ht, heq⟩ hxt)
  · rintro (hx | hx)
    · exact realization_mono (A := K.eraseFacet s hs) (B := K) Set.sdiff_subset hx
    · exact K.convexHull_face_subset_realization s (Geometry.SimplicialComplex.mem_facets.mp hs).1 hx

/-- A face of maximum cardinality among the missing faces is a facet. -/
theorem exists_missing_facet {A B : FinitePlanarComplex}
    (hAB : ¬ A.simplices.faces ⊆ B.simplices.faces) :
    ∃ s ∈ A.simplices.facets, s ∉ B.simplices.faces ∧
      ∀ t ∈ A.simplices.faces, t ∉ B.simplices.faces → t.card ≤ s.card := by
  classical
  obtain ⟨u, huA, huB⟩ := Set.not_subset.mp hAB
  have hnonempty : (A.faceFinset \ B.faceFinset).Nonempty :=
    ⟨u, by simp [mem_faceFinset_iff, huA, huB]⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ Finset.card hnonempty
  have hsA : s ∈ A.simplices.faces :=
    (A.mem_faceFinset_iff s).mp (Finset.mem_sdiff.mp hs).1
  have hsB : s ∉ B.simplices.faces :=
    fun h => (Finset.mem_sdiff.mp hs).2 ((B.mem_faceFinset_iff s).mpr h)
  have hbound : ∀ t ∈ A.simplices.faces, t ∉ B.simplices.faces → t.card ≤ s.card :=
    fun t htA htB => hmax t (by simp [mem_faceFinset_iff, htA, htB])
  refine ⟨s, Geometry.SimplicialComplex.mem_facets.mpr ⟨hsA, ?_⟩, hsB, hbound⟩
  intro t htA hst
  have htB : t ∉ B.simplices.faces :=
    fun h => hsB (B.simplices.down_closed h hst (A.simplices.nonempty_of_mem_faces hsA))
  exact (Finset.eq_of_subset_of_card_le hst (hbound t htA htB))

/-- A deletion toward a fixed target removes a missing face of maximum dimension. -/
def DeletesFacetToward (target A B : FinitePlanarComplex) : Prop :=
  ∃ s, ∃ hs : s ∈ A.simplices.facets,
    s ∉ target.simplices.faces ∧
      (∀ t ∈ A.simplices.faces, t ∉ target.simplices.faces → t.card ≤ s.card) ∧
      B = A.eraseFacet s hs

/-- Every finite subcomplex can be reached by deleting missing faces in
descending dimension. -/
theorem reflTransGen_deletesFacetToward (A B : FinitePlanarComplex)
    (hBA : B.simplices.faces ⊆ A.simplices.faces) :
    Relation.ReflTransGen (DeletesFacetToward B) A B := by
  classical
  by_cases hAB : A.simplices.faces ⊆ B.simplices.faces
  · have hsimp : A.simplices = B.simplices := by
      ext t
      exact ⟨fun ht => hAB ht, fun ht => hBA ht⟩
    have hEq : A = B := by
      cases A
      cases B
      congr
    subst B
    exact Relation.ReflTransGen.refl
  · obtain ⟨s, hs, hsB, hmax⟩ := exists_missing_facet hAB
    have hnext : B.simplices.faces ⊆ (A.eraseFacet s hs).simplices.faces := by
      intro t ht
      exact ⟨hBA ht, fun heq => hsB ((Set.mem_singleton_iff.mp heq) ▸ ht)⟩
    have hlt : (A.eraseFacet s hs).faceFinset.card < A.faceFinset.card := by
      rw [faceFinset_eraseFacet]
      exact Finset.card_erase_lt_of_mem
        ((A.mem_faceFinset_iff s).mpr (Geometry.SimplicialComplex.mem_facets.mp hs).1)
    exact Relation.ReflTransGen.head ⟨s, hs, hsB, hmax, rfl⟩
      (reflTransGen_deletesFacetToward (A.eraseFacet s hs) B hnext)
termination_by A.faceFinset.card

end FinitePlanarComplex
