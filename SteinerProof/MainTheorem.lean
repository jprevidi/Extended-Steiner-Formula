import SteinerProof.EdgeDeletion
import SteinerProof.HullFilling
import SteinerProof.VertexDeletion
import SteinerProof.TriangleScale
import SteinerProof.SimplexValuation

set_option linter.all false

noncomputable section

namespace FinitePlanarComplex

-- The Steiner identity at one particular radius.
def SteinerIdentityAt
    (K : FinitePlanarComplex) (r : ℝ) : Prop :=
  K.extendedArea r = K.steinerPolynomial r

-- The small-radius version of Theorem 1.1.
def HasSmallRadiusSteinerFormula
    (K : FinitePlanarComplex) : Prop :=
  ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, 0 < r → r < R →
      SteinerIdentityAt K r

/-- Propagate the formula across one deletion once its area change is known. -/
theorem SteinerIdentityAt.of_deletion
    {A B : FinitePlanarComplex} {r : ℝ} (hr : 0 ≤ r)
    (hBA : B.realization ⊆ A.realization) (hA : SteinerIdentityAt A r)
    (hdelta :
      (MeasureTheory.volume
        (extendedBody A.realization r \ extendedBody B.realization r)).toReal =
        A.steinerPolynomial r - B.steinerPolynomial r) :
    SteinerIdentityAt B r := by
  have harea := extendedArea_sub_of_realization_subset hBA r hr
  rw [hdelta] at harea
  unfold SteinerIdentityAt at hA ⊢
  linarith

/-- Propagate the formula across a facet deletion with the face's Steiner contribution. -/
theorem SteinerIdentityAt.of_facet_deletion
    {A : FinitePlanarComplex} {s : Finset PLPoint} (hs : s ∈ A.simplices.facets)
    {r : ℝ} (hr : 0 ≤ r) (hA : SteinerIdentityAt A r)
    (hdelta : (MeasureTheory.volume (extendedBody A.realization r \
      extendedBody (A.eraseFacet s hs).realization r)).toReal = steinerFaceContribution s r) :
    SteinerIdentityAt (A.eraseFacet s hs) r := by
  apply SteinerIdentityAt.of_deletion hr (realization_mono Set.sdiff_subset) hA
  rw [steinerPolynomial_sub_eraseFacet]
  exact hdelta

/-- The isolated-vertex case of the facet deletion induction. -/
theorem SteinerIdentityAt.of_isolated_vertex_deletion
    {K A : FinitePlanarComplex} {z : PLPoint}
    (hz : ({z} : Finset PLPoint) ∈ A.simplices.facets)
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : 5 * r < K.vertexFaceSeparation)
    (hA : SteinerIdentityAt A r) :
    SteinerIdentityAt (A.eraseFacet {z} hz) r := by
  let B := A.eraseFacet {z} hz
  have hreal : A.realization = B.realization ∪ {z} := by
    simpa only [B, Finset.coe_singleton, convexHull_singleton] using
      A.realization_eq_eraseFacet_union_convexHull {z} hz
  have hzK : z ∈ K.simplices.vertices := hAK (Geometry.SimplicialComplex.mem_facets.mp hz).1
  have hsep : ∀ b ∈ B.realization, 5 * r < dist b z := by
    intro b hb
    obtain ⟨t, ht, hbt⟩ := (B.mem_realization_iff b).mp hb
    have hzNotMem : z ∉ t := by
      intro hzt
      exact ht.2 (Set.mem_singleton_iff.mpr
        ((Geometry.SimplicialComplex.mem_facets.mp hz).2 t ht.1
          (Finset.singleton_subset_iff.mpr hzt)).symm)
    rw [dist_comm]
    exact hsmall.trans_le (K.vertexFaceSeparation_le_dist hzK (hAK ht.1) hzNotMem hbt)
  apply SteinerIdentityAt.of_facet_deletion hz hr hA
  rw [hreal]
  simpa [steinerFaceContribution, B] using
    volume_extendedBody_sdiff_isolated_vertex B.isClosed_realization hr hsep

/-- The triangle case of the facet deletion induction, given its ordinary offset formula. -/
theorem SteinerIdentityAt.of_triangle_deletion
    {K A : FinitePlanarComplex} {s : Finset PLPoint} (hs : s ∈ A.simplices.facets)
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    (hcard : s.card = 3) {r : ℝ} (hr : 0 < r) (hsmall : 6 * r < K.vertexFaceSeparation)
    (hpoly : TriangleOffsetFormula s)
    (hA : SteinerIdentityAt A r) : SteinerIdentityAt (A.eraseFacet s hs) r := by
  apply SteinerIdentityAt.of_facet_deletion hs hr.le hA
  have hinradius := third_vertexFaceSeparation_le_triangle_inradius hAK s
    (Geometry.SimplicialComplex.mem_facets.mp hs).1 hcard
  have hdepth := (show 2 * r < K.vertexFaceSeparation / 3 by linarith).trans_le hinradius
  simpa only [steinerFaceContribution, ite_eq_left hcard] using
    A.area_extendedBody_sdiff_erase_triangle s hs hcard hr hdepth hpoly

private theorem SteinerIdentityAt.of_subcomplex_step
    {A B : FinitePlanarComplex} {r : ℝ}
    (hBA : B.simplices.faces ⊆ A.simplices.faces)
    (hA : SteinerIdentityAt A r)
    (hstep : ∀ (C : FinitePlanarComplex) (s : Finset PLPoint)
      (hs : s ∈ C.simplices.facets), C.simplices.faces ⊆ A.simplices.faces →
      s ∉ B.simplices.faces → SteinerIdentityAt C r →
      SteinerIdentityAt (C.eraseFacet s hs) r) :
    SteinerIdentityAt B r := by
  have hchain := reflTransGen_deletesFacetToward A B hBA
  suffices h : ∀ D, Relation.ReflTransGen (DeletesFacetToward B) A D →
      D.simplices.faces ⊆ A.simplices.faces ∧ SteinerIdentityAt D r from (h B hchain).2
  intro D hD
  induction hD with
  | refl => exact ⟨Set.Subset.rfl, hA⟩
  | tail _ hdelete ih =>
      obtain ⟨s, hs, hsB, _, rfl⟩ := hdelete
      exact ⟨Set.sdiff_subset.trans ih.1, hstep _ s hs ih.1 hsB ih.2⟩

/-- Deletion induction from a verified seed to a subcomplex. The local input is
the area of the lost region at each allowed deletion. -/
theorem SteinerIdentityAt.of_subcomplex
    {A B : FinitePlanarComplex} {r : ℝ} (hr : 0 ≤ r)
    (hBA : B.simplices.faces ⊆ A.simplices.faces)
    (hA : SteinerIdentityAt A r)
    (hdelta : ∀ (C : FinitePlanarComplex) (s : Finset PLPoint)
      (hs : s ∈ C.simplices.facets), C.simplices.faces ⊆ A.simplices.faces →
      s ∉ B.simplices.faces →
      (MeasureTheory.volume (extendedBody C.realization r \
        extendedBody (C.eraseFacet s hs).realization r)).toReal = steinerFaceContribution s r) :
    SteinerIdentityAt B r := by
  apply SteinerIdentityAt.of_subcomplex_step hBA hA
  intro C s hs hCA hsB hC
  exact SteinerIdentityAt.of_facet_deletion hs hr hC (hdelta C s hs hCA hsB)

/-- Theorem 1.1 at every radius below the bound of the supplied hull
triangulation, with the ordinary convex offset formulas as background. -/
theorem steinerIdentityAt_of_background
    (A : FinitePlanarComplex) (H : CompatibleHullRefinement A)
    (hseed : ∀ r : ℝ, 0 < r → r < H.hull.admissibleRadius → ConvexOffsetFormulaAt H.hull r)
    (htriangle : ∀ s ∈ H.hull.triangles, TriangleOffsetFormula s)
    {r : ℝ} (hr : 0 < r) (hR : r < H.hull.admissibleRadius) : SteinerIdentityAt A r := by
  have hconv : Convex ℝ H.hull.realization := by
    rw [H.hull_realization]
    exact convex_convexHull _ _
  have hH : SteinerIdentityAt H.hull r := by
    unfold SteinerIdentityAt extendedArea
    rw [extendedBody_eq_offset_of_convex H.hull.isClosed_realization hconv hr.le]
    exact hseed r hr hR
  have hsmall := H.hull.six_mul_lt_separation_of_lt_admissibleRadius hR
  have ht : SteinerIdentityAt H.target r := by
    apply SteinerIdentityAt.of_subcomplex_step H.target_faces_subset hH
    intro C s hs hCH _ hC
    have hsFace := (Geometry.SimplicialComplex.mem_facets.mp hs).1
    have hpos := Finset.card_pos.mpr (C.simplices.nonempty_of_mem_faces hsFace)
    have hdim : s.card ≤ 3 := by
      have h := (C.simplices.indep hsFace).card_le_finrank_succ
      have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
      simp only [Fintype.card_coe] at h
      rw [finrank_euclideanSpace_fin] at hle
      omega
    have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
    rcases hcases with h₁ | h₂ | h₃
    · obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp h₁
      exact SteinerIdentityAt.of_isolated_vertex_deletion hs hCH hr.le (by linarith) hC
    · obtain ⟨v, u, hvu, rfl⟩ := Finset.card_eq_two.mp h₂
      apply SteinerIdentityAt.of_facet_deletion hs hr.le hC
      rw [area_extendedBody_sdiff_eraseEdge hCH hvu hs hr hR]
      simp [steinerFaceContribution, h₂, edgeLength_pair v u hvu]
    · have htri : s ∈ H.hull.triangles := by
        simp [triangles, mem_faceFinset_iff, hCH hsFace, h₃]
      exact SteinerIdentityAt.of_triangle_deletion hs hCH h₃ hr hsmall (htriangle s htri) hC
  unfold SteinerIdentityAt extendedArea at ht ⊢
  rwa [H.target_realization, H.target_polynomial] at ht

/-- The small-radius extended Steiner formula, with the explicit positive
radius supplied by the hull triangulation. -/
theorem hasSmallRadiusSteinerFormula_of_background
    (A : FinitePlanarComplex) (H : CompatibleHullRefinement A)
    (hseed : ∀ r : ℝ, 0 < r → r < H.hull.admissibleRadius → ConvexOffsetFormulaAt H.hull r)
    (htriangle : ∀ s ∈ H.hull.triangles, TriangleOffsetFormula s) :
    HasSmallRadiusSteinerFormula A :=
  ⟨H.hull.admissibleRadius, H.hull.admissibleRadius_pos,
    fun _ => steinerIdentityAt_of_background A H hseed htriangle⟩

private theorem steinerIdentityAt_of_ordinarySteiner (h : OrdinaryPlanarSteiner)
    {A : FinitePlanarComplex} (hA : A.realization.Nonempty) (H : CompatibleHullRefinement A)
    {r : ℝ} (hr : 0 < r) (hR : r < H.hull.admissibleRadius) : SteinerIdentityAt A r := by
  have hHullNonempty : H.hull.realization.Nonempty := H.hull_realization.symm ▸ hA.convexHull
  have hHullConvex : Convex ℝ H.hull.realization := H.hull_realization.symm ▸ convex_convexHull ℝ A.realization
  exact steinerIdentityAt_of_background A H
    (fun _ hs _ => h.convexOffset H.hull hHullNonempty hHullConvex _ hs.le) (h.triangleOffset H.hull) hr hR

/-- The small-radius conclusion of Theorem 1.1 for every nonempty closed
planar realization, from the ordinary planar Steiner formula. -/
theorem hasSmallRadiusSteinerFormula (h : OrdinaryPlanarSteiner)
    (A : FinitePlanarComplex) (hA : A.realization.Nonempty) : HasSmallRadiusSteinerFormula A := by
  obtain ⟨H⟩ := A.nonempty_compatibleHullRefinement
  exact ⟨H.hull.admissibleRadius, H.hull.admissibleRadius_pos,
    fun _ hr hR => steinerIdentityAt_of_ordinarySteiner h hA H hr hR⟩

/-- The linear and quadratic Steiner coefficients are independent of the
chosen finite complex representing a nonempty closed planar set. -/
theorem steinerCoefficients_eq_of_realization_eq (h : OrdinaryPlanarSteiner)
    {A B : FinitePlanarComplex} (hA : A.realization.Nonempty) (hAB : A.realization = B.realization) :
    A.twiceV1 = B.twiceV1 ∧ A.eulerChar = B.eulerChar := by
  obtain ⟨RA, hRA, hSA⟩ := hasSmallRadiusSteinerFormula h A hA
  obtain ⟨RB, hRB, hSB⟩ := hasSmallRadiusSteinerFormula h B (hAB ▸ hA)
  let R := min RA RB
  have hR : 0 < R := lt_min hRA hRB
  have hArea : A.totalArea = B.totalArea := by simp only [totalArea_eq_volume_realization, hAB]
  have hEq (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      A.twiceV1 - B.twiceV1 + Real.pi * r * ((A.eulerChar : ℝ) - (B.eulerChar : ℝ)) = 0 := by
    have ha := hSA r hr (hrR.trans_le (min_le_left _ _))
    have hb := hSB r hr (hrR.trans_le (min_le_right _ _))
    have hEA : A.extendedArea r = B.extendedArea r := by simp only [extendedArea, hAB]
    have hp := ha.symm.trans (hEA.trans hb)
    unfold steinerPolynomial at hp
    have hFactor : r * (A.twiceV1 - B.twiceV1 + Real.pi * r * ((A.eulerChar : ℝ) - (B.eulerChar : ℝ))) = 0 := by
      linear_combination hp - hArea
    exact (mul_eq_zero.mp hFactor).resolve_left hr.ne'
  have h₁ := hEq (R / 2) (by positivity) (by linarith)
  have h₂ := hEq (R / 3) (by positivity) (by linarith)
  have hDiff : Real.pi * (R / 2 - R / 3) * ((A.eulerChar : ℝ) - (B.eulerChar : ℝ)) = 0 := by
    linear_combination h₁ - h₂
  have hχ : (A.eulerChar : ℝ) = (B.eulerChar : ℝ) := sub_eq_zero.mp
    ((mul_eq_zero.mp hDiff).resolve_left (mul_ne_zero Real.pi_ne_zero (by linarith)))
  rw [hχ, sub_self, mul_zero, add_zero, sub_eq_zero] at h₁
  exact ⟨h₁, by exact_mod_cast hχ⟩

/-- The explicit radius in Theorem 1.1 from any compatible hull
triangulation. The target subcomplex can use a refinement of the original faces. -/
theorem steinerIdentityAt_of_hull_triangulation (h : OrdinaryPlanarSteiner)
    {A K T : FinitePlanarComplex} (hA : A.realization.Nonempty)
    (hTK : T.simplices.faces ⊆ K.simplices.faces)
    (hK : K.realization = convexHull ℝ A.realization) (hT : T.realization = A.realization)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) : SteinerIdentityAt A r := by
  obtain ⟨hLin, hEuler⟩ := steinerCoefficients_eq_of_realization_eq h (hT.symm ▸ hA) hT
  let H : CompatibleHullRefinement A := ⟨K, T, hTK, hK, hT, hLin, hEuler⟩
  exact steinerIdentityAt_of_ordinarySteiner h hA H hr hR

/-- Theorem 1.1 in terms of ordinary area and the simplicial Steiner coefficients. -/
theorem planarExtendedSteinerFormula (h : OrdinaryPlanarSteiner)
    (A : FinitePlanarComplex) (hA : A.realization.Nonempty) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      (MeasureTheory.volume (extendedBody A.realization r)).toReal =
        (MeasureTheory.volume A.realization).toReal + r * A.twiceV1 + Real.pi * r ^ 2 * (A.eulerChar : ℝ) := by
  obtain ⟨R, hR, hFormula⟩ := hasSmallRadiusSteinerFormula h A hA
  exact ⟨R, hR, fun r hr hrR => by
    simpa only [SteinerIdentityAt, extendedArea, steinerPolynomial, totalArea_eq_volume_realization] using
      hFormula r hr hrR⟩

end FinitePlanarComplex
