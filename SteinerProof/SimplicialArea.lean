import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import SteinerProof.PLComplex

/-! The area coefficient is the area of the realization. -/

open Set MeasureTheory
open scoped Function

noncomputable section

namespace FinitePlanarComplex

private theorem volume_convexHull_eq_zero_of_card_le_two (s : Finset PLPoint)
    (h : s.card ≤ 2) : volume (convexHull ℝ (s : Set PLPoint)) = 0 := by
  have hc : (s : Set PLPoint).encard ≤ Module.finrank ℝ PLPoint := by
    rw [Set.encard_coe_eq_coe_finsetCard, finrank_euclideanSpace_fin]
    exact_mod_cast h
  have hs : affineSpan ℝ (s : Set PLPoint) ≠ ⊤ := by
    simpa only [Set.image_id] using
      affineSpan_image_ne_top_of_encard_le_finrank ℝ hc (id : PLPoint → PLPoint)
  exact measure_mono_null (convexHull_min (subset_affineSpan ℝ _) (AffineSubspace.convex _))
    (MeasureTheory.Measure.addHaar_affineSubspace volume _ hs)

private theorem face_card_le_three {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.simplices.faces) : s.card ≤ 3 := by
  have h := (K.simplices.indep hs).card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
  simp only [Fintype.card_coe] at h
  rw [finrank_euclideanSpace_fin] at hle
  omega

/-- Boundary faces and intersections of distinct triangles have area zero,
so summing the areas of triangles gives the area of the realization. -/
theorem totalArea_eq_volume_realization (K : FinitePlanarComplex) :
    K.totalArea = (volume K.realization).toReal := by
  classical
  let f (s : Finset PLPoint) := convexHull ℝ (s : Set PLPoint)
  have hreal : K.realization = ⋃ s ∈ K.faceFinset, f s := by
    ext x
    simpa only [Set.mem_iUnion, exists_prop, K.mem_faceFinset_iff] using K.mem_realization_iff x
  have hdisj : Set.Pairwise (K.faceFinset : Set (Finset PLPoint)) (AEDisjoint volume on f) := by
    intro s hs t ht hst
    have hsFace := (K.mem_faceFinset_iff s).mp (show s ∈ K.faceFinset from hs)
    have htFace := (K.mem_faceFinset_iff t).mp (show t ∈ K.faceFinset from ht)
    change volume (f s ∩ f t) = 0
    change volume (convexHull ℝ (s : Set PLPoint) ∩ convexHull ℝ (t : Set PLPoint)) = 0
    rw [K.simplices.convexHull_inter_convexHull hsFace htFace, ← Finset.coe_inter]
    apply volume_convexHull_eq_zero_of_card_le_two
    have hi : (s ∩ t).card ≤ 3 := (Finset.card_le_card Finset.inter_subset_left).trans
      (face_card_le_three hsFace)
    by_contra! hbig
    have hi' : (s ∩ t).card = 3 := by omega
    have hEQ₁ := Finset.eq_of_subset_of_card_le
      (Finset.inter_subset_left : s ∩ t ⊆ s) (hi' ▸ face_card_le_three hsFace)
    have hEQ₂ := Finset.eq_of_subset_of_card_le
      (Finset.inter_subset_right : s ∩ t ⊆ t) (hi' ▸ face_card_le_three htFace)
    exact hst (hEQ₁.symm.trans hEQ₂)
  have hcompact (s : Finset PLPoint) : IsCompact (f s) :=
    s.finite_toSet.isCompact_convexHull ℝ
  have hsum := measureReal_biUnion_finset₀ hdisj
    (fun s _ => (hcompact s).isClosed.nullMeasurableSet)
    (fun s _ => (hcompact s).measure_lt_top.ne)
  rw [← hreal] at hsum
  change K.totalArea = volume.real K.realization
  rw [hsum]
  unfold totalArea triangleArea triangles
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s hs hsTri
  have hp : s.card ≤ 3 := face_card_le_three ((K.mem_faceFinset_iff s).mp hs)
  have hn : s.card ≠ 3 := fun heq => hsTri (Finset.mem_filter.mpr ⟨hs, heq⟩)
  change (volume (convexHull ℝ (s : Set PLPoint))).toReal = 0
  rw [volume_convexHull_eq_zero_of_card_le_two s (by omega), ENNReal.toReal_zero]

end FinitePlanarComplex
