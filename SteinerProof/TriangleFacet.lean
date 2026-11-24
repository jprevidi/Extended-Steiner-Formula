import SteinerProof.Background
import SteinerProof.FacetDeletion
import SteinerProof.TriangleDeletion

/-! Geometric triangles associated to three-vertex faces. -/

open Set Affine.Simplex

noncomputable section

namespace FinitePlanarComplex

/-- Enumerate the three vertices of a face as an affine simplex. -/
def triangleOfFace (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.faces) (hcard : s.card = 3) : Affine.Simplex ℝ PLPoint 2 := by
  let e : s ≃ Fin 3 := s.equivFinOfCardEq hcard
  have hind : AffineIndependent ℝ ((↑) : s → PLPoint) := K.simplices.indep hs
  exact ⟨((↑) : s → PLPoint) ∘ e.symm, hind.comp_embedding e.symm.toEmbedding⟩

@[simp] theorem range_triangleOfFace (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.faces) (hcard : s.card = 3) :
    range (K.triangleOfFace s hs hcard).points = (s : Set PLPoint) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((s.equivFinOfCardEq hcard).symm i).property
  · intro hx
    exact ⟨s.equivFinOfCardEq hcard ⟨x, hx⟩, by simp [triangleOfFace]⟩

/-- In the plane the open part of a triangle face is its ambient interior. -/
theorem openFace_eq_interior_of_card_three {s : Finset PLPoint}
    (T : Affine.Simplex ℝ PLPoint 2) (hT : range T.points = (s : Set PLPoint)) :
    openFace s = interior (convexHull ℝ (s : Set PLPoint)) := by
  classical
  let b : AffineBasis (Fin 3) ℝ PLPoint :=
    ⟨T.points, T.independent, T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp)⟩
  have hb : range b = (s : Set PLPoint) := hT
  ext x
  constructor
  · rintro ⟨hx, hproper⟩
    rw [← hb, b.interior_convexHull]
    intro i
    have hxnonneg : ∀ j, 0 ≤ b.coord j x := by
      rwa [← hb, b.convexHull_eq_nonneg_coord] at hx
    by_contra! hi
    have hi0 := le_antisymm hi (hxnonneg i)
    have hxComb : Finset.univ.affineCombination ℝ T.points (fun j => b.coord j x) = x :=
      b.affineCombination_coord_eq_self x
    have hxOpp : x ∈ (T.faceOpposite i).closedInterior := by
      rw [← hxComb, Affine.Simplex.faceOpposite,
        T.affineCombination_mem_closedInterior_face_iff_nonneg _ (b.sum_coord_apply_eq_one x)]
      exact ⟨fun j _ => hxnonneg j, fun j hj => by
        have heq : j = i := by simpa using hj
        simpa [heq] using hi0⟩
    have hbi : b i ∈ (s : Set PLPoint) := hb ▸ mem_range_self i
    have hsub : s.erase (b i) ⊂ s := Finset.erase_ssubset hbi
    apply hproper
    refine Set.mem_iUnion₂.mpr ⟨s.erase (b i), hsub, ?_⟩
    rw [← convexHull_eq_closedInterior, T.range_faceOpposite_points] at hxOpp
    apply convexHull_mono _ hxOpp
    rintro _ ⟨j, hj, rfl⟩
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · exact fun heq => hj (Set.mem_singleton_iff.mpr (T.independent.injective heq))
    · exact (show T.points j ∈ (s : Set PLPoint) from hT ▸ mem_range_self j)
  · intro hx
    refine ⟨interior_subset hx, ?_⟩
    rintro hproper
    obtain ⟨t, hts, hxt⟩ := Set.mem_iUnion₂.mp hproper
    obtain ⟨v, hvs, hvt⟩ := Finset.exists_of_ssubset hts
    obtain ⟨i, rfl⟩ : v ∈ range b := hb.symm ▸ (show v ∈ (s : Set PLPoint) from hvs)
    have hzero : convexHull ℝ (t : Set PLPoint) ⊆ b.coord i ⁻¹' {0} := by
      apply convexHull_min _ ((convex_singleton _).affine_preimage _)
      intro y hy
      have hys : y ∈ (s : Set PLPoint) := (Finset.ssubset_iff_subset_ne.mp hts).1 hy
      obtain ⟨j, rfl⟩ : y ∈ range b := hb.symm ▸ hys
      have hij : i ≠ j := fun h => hvt (h ▸ hy)
      exact b.coord_apply_ne hij
    have hpos : ∀ j, 0 < b.coord j x := by
      rwa [← hb, b.interior_convexHull] at hx
    exact (ne_of_gt (hpos i)) (hzero hxt)

theorem triangleArea_eq_simplex_volume {s : Finset PLPoint}
    (T : Affine.Simplex ℝ PLPoint 2) (hT : range T.points = (s : Set PLPoint)) :
    triangleArea s = T.volume := by
  rw [triangleArea, ← hT, convexHull_eq_closedInterior]
  exact (Affine.Simplex.volume_eq_volume_real_closedInterior (by simp) T).symm

theorem trianglePerimeter_eq_sum_opposite_lengths {s : Finset PLPoint}
    (T : Affine.Simplex ℝ PLPoint 2) (hT : range T.points = (s : Set PLPoint)) :
    trianglePerimeter s = ∑ i, (T.faceOpposite i).volume := by
  classical
  let e : Fin 3 ↪ PLPoint := ⟨T.points, T.independent.injective⟩
  have hmap : Finset.univ.map e = s := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact Set.ext_iff.mp hT x
  have h0 : (T.faceOpposite 0).volume = dist (T.points 1) (T.points 2) := by
    rw [Affine.Simplex.volume_eq_dist, T.faceOpposite_point_eq_point_succAbove,
      T.faceOpposite_point_eq_point_succAbove]
    rfl
  have h1 : (T.faceOpposite 1).volume = dist (T.points 0) (T.points 2) := by
    rw [Affine.Simplex.volume_eq_dist, T.faceOpposite_point_eq_point_succAbove,
      T.faceOpposite_point_eq_point_succAbove]
    rfl
  have h2 : (T.faceOpposite 2).volume = dist (T.points 0) (T.points 1) := by
    rw [Affine.Simplex.volume_eq_dist, T.faceOpposite_point_eq_point_succAbove,
      T.faceOpposite_point_eq_point_succAbove]
    rfl
  have hsides := Fin.sum_univ_three (fun i : Fin 3 => (T.faceOpposite i).volume)
  rw [hsides, h0, h1, h2, trianglePerimeter, boundaryLength, ← hmap]
  simp only [Finset.sum_map, Fin.sum_univ_three, e, Function.Embedding.coeFn_mk,
    dist_self, dist_comm]
  ring

/-- The triangle area decrement in the deletion induction, reduced to the
ordinary offset area formula for the closed triangle. -/
theorem area_extendedBody_sdiff_erase_triangle (K : FinitePlanarComplex)
    (s : Finset PLPoint) (hs : s ∈ K.simplices.facets) (hcard : s.card = 3)
    {r : ℝ} (hr : 0 < r)
    (hsmall : 2 * r < (K.triangleOfFace s
      (Geometry.SimplicialComplex.mem_facets.mp hs).1 hcard).inradius)
    (hpoly : TriangleOffsetFormula s) :
    (MeasureTheory.volume (extendedBody K.realization r \
      extendedBody (K.eraseFacet s hs).realization r)).toReal =
        triangleArea s - r * trianglePerimeter s + Real.pi * r ^ 2 := by
  have hsK := (Geometry.SimplicialComplex.mem_facets.mp hs).1
  let T := K.triangleOfFace s hsK hcard
  have hT : range T.points = (s : Set PLPoint) := K.range_triangleOfFace s hsK hcard
  have hArea := triangleArea_eq_simplex_volume T hT
  have hPerim := trianglePerimeter_eq_sum_opposite_lengths T hT
  have hCA : convexHull ℝ (range T.points) ⊆ K.realization := by
    rw [hT]
    exact K.convexHull_face_subset_realization s hsK
  have hFormula := T.area_extendedBody_sdiff_triangle_of_offset_formula
    K.isClosed_realization hCA hr hsmall 
    (by simpa only [TriangleOffsetFormula, hT, ← hArea, ← hPerim] using hpoly)
  rwa [K.realization_eraseFacet_eq_sdiff s hs, openFace_eq_interior_of_card_three T hT,
    hArea, hPerim, ← hT]

end FinitePlanarComplex
