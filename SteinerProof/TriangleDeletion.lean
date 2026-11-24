import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Euclidean.Volume.Incenter
import Mathlib.Tactic.Positivity.Basic
import SteinerProof.ExtendedBody

/-! The lost offset and lost extended body when deleting an open region.
These identities apply to the interior of a two-simplex in Section 6.1. -/

open Set

noncomputable section

private theorem closedBall_subset_of_avoids_frontier {D : Set Point2}
    (hD : IsOpen D) {x : Point2} {t : ℝ} (hfront : x ∉ offset (frontier D) t)
    (hball : (Metric.closedBall x t ∩ D).Nonempty) :
    Metric.closedBall x t ⊆ D := by
  apply Metric.isPreconnected_closedBall.subset_of_closure_inter_subset hD hball
  rintro y ⟨hyClosure, hyBall⟩
  by_contra hyD
  have hyFront : y ∈ frontier D := hD.frontier_eq.symm ▸ ⟨hyClosure, hyD⟩
  have hxy : dist x y ≤ t := by simpa [dist_comm] using Metric.mem_closedBall.mp hyBall
  exact hfront ((mem_offset_iff_exists_dist_le isClosed_frontier).mpr ⟨y, hyFront, hxy⟩)

/-- The lost offset is the open region with its frontier offset removed. -/
theorem offset_sdiff_open_deletion {A D : Set Point2} (hA : IsClosed A) (hD : IsOpen D)
    (hDA : D ⊆ A) {t : ℝ} (ht : 0 ≤ t) :
    offset A t \ offset (A \ D) t = D \ offset (frontier D) t := by
  have hB : IsClosed (A \ D) := hA.sdiff hD
  have hfront : frontier D ⊆ A \ D := by
    rw [hD.frontier_eq]
    exact fun _ hy => ⟨closure_minimal hDA hA hy.1, hy.2⟩
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨a, ha, hxa⟩ := (mem_offset_iff_exists_dist_le hA).mp hxA
    have haD : a ∈ D := by
      by_contra hn
      exact hxB ((mem_offset_iff_exists_dist_le hB).mpr ⟨a, ⟨ha, hn⟩, hxa⟩)
    have hxFront : x ∉ offset (frontier D) t := fun hx => hxB (offset_mono hfront t hx)
    have haBall : a ∈ Metric.closedBall x t := by simpa [Metric.mem_closedBall, dist_comm] using hxa
    exact ⟨closedBall_subset_of_avoids_frontier hD hxFront ⟨a, haBall, haD⟩
      (Metric.mem_closedBall_self ht), hxFront⟩
  · rintro ⟨hxD, hxFront⟩
    refine ⟨(mem_offset_iff_exists_dist_le hA).mpr
      ⟨x, hDA hxD, by simpa only [dist_self] using ht⟩, ?_⟩
    intro hxB
    obtain ⟨b, hb, hxb⟩ := (mem_offset_iff_exists_dist_le hB).mp hxB
    have hbBall : b ∈ Metric.closedBall x t := by simpa [Metric.mem_closedBall, dist_comm] using hxb
    exact hb.2 (closedBall_subset_of_avoids_frontier hD hxFront
      ⟨x, Metric.mem_closedBall_self ht, hxD⟩ hbBall)

/-- The lost extended body consists of the points within distance `r`
of a point of the open region that is farther than `2 * r` from its frontier. -/
theorem extendedBody_sdiff_open_deletion {A D : Set Point2} (hA : IsClosed A)
    (hD : IsOpen D) (hDA : D ⊆ A) {r : ℝ} (hr : 0 ≤ r) :
    extendedBody A r \ extendedBody (A \ D) r =
      {x | (Metric.closedBall x r ∩ (D \ offset (frontier D) (2 * r))).Nonempty} := by
  have ht : 0 ≤ 2 * r := by positivity
  ext x
  rw [mem_extendedBody_sdiff_iff (hA.sdiff hD) hr, offset_sdiff_open_deletion hA hD hDA ht]
  constructor
  · exact And.right
  · rintro ⟨y, hyBall, hyD, hyFront⟩
    have hxyBall : x ∈ Metric.closedBall y (2 * r) := by
      rw [Metric.mem_closedBall, dist_comm]
      linarith [Metric.mem_closedBall.mp hyBall]
    have hxD := closedBall_subset_of_avoids_frontier hD hyFront
      ⟨y, Metric.mem_closedBall_self ht, hyD⟩ hxyBall
    exact ⟨offset_subset_extendedBody A r
      ((mem_offset_iff_exists_dist_le hA).mpr ⟨x, hDA hxD, by simpa only [dist_self] using hr⟩),
      y, hyBall, hyD, hyFront⟩

/-- For positive radius the lost region is the open offset of the inset. -/
theorem extendedBody_sdiff_open_deletion_eq_thickening {A D : Set Point2}
    (hA : IsClosed A) (hD : IsOpen D) (hDA : D ⊆ A) {r : ℝ} (hr : 0 < r) :
    extendedBody A r \ extendedBody (A \ D) r =
      Metric.thickening r (D \ offset (frontier D) (2 * r)) := by
  rw [extendedBody_sdiff_open_deletion hA hD hDA hr.le]
  have hInsetOpen : IsOpen (D \ offset (frontier D) (2 * r)) :=
    hD.sdiff (isClosed_offset _ _)
  ext x
  rw [Metric.mem_thickening_iff]
  constructor
  · rintro ⟨y, hyBall, hyInset⟩
    have hyClosure : y ∈ closure (Metric.ball x r) := by
      rwa [closure_ball x hr.ne']
    obtain ⟨z, hzInset, hzBall⟩ := mem_closure_iff.mp hyClosure _ hInsetOpen hyInset
    exact ⟨z, hzInset, by simpa [dist_comm] using Metric.mem_ball.mp hzBall⟩
  · rintro ⟨y, hyInset, hxy⟩
    exact ⟨y, Metric.mem_closedBall.mpr (by simpa [dist_comm] using hxy.le), hyInset⟩

/-- When the closure of the open inset is convex, its ordinary closed
offset has the same area as the lost region. -/
theorem volume_extendedBody_sdiff_open_deletion {A D T : Set Point2}
    (hA : IsClosed A) (hD : IsOpen D) (hDA : D ⊆ A) {r : ℝ} (hr : 0 < r)
    (hT : closure (D \ offset (frontier D) (2 * r)) = T) (hconv : Convex ℝ T) :
    MeasureTheory.volume (extendedBody A r \ extendedBody (A \ D) r) =
      MeasureTheory.volume (offset T r) := by
  have hclosed : IsClosed T := hT ▸ isClosed_closure
  have hoffset : offset T r = Metric.cthickening r T := by
    rw [Metric.cthickening_eq_biUnion_closedBall _ hr.le, hclosed.closure_eq]
    ext x
    simpa only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] using
      (mem_offset_iff_exists_dist_le hclosed (r := r) (x := x))
  have hmeasure := measure_closure_of_null_frontier
    ((hconv.thickening r).addHaar_frontier MeasureTheory.volume)
  rw [closure_thickening hr, ← hoffset] at hmeasure
  rw [extendedBody_sdiff_open_deletion_eq_thickening hA hD hDA hr,
    ← Metric.thickening_closure, hT, hmeasure]

open scoped RealInnerProductSpace

private theorem mem_open_inset_iff_ball_subset {D : Set Point2} (hD : IsOpen D)
    {x : Point2} {t : ℝ} (ht : 0 ≤ t) :
    x ∈ D \ offset (frontier D) t ↔ Metric.closedBall x t ⊆ D := by
  constructor
  · rintro ⟨hx, hfront⟩
    exact closedBall_subset_of_avoids_frontier hD hfront
      ⟨x, Metric.mem_closedBall_self ht, hx⟩
  · intro hball
    refine ⟨hball (Metric.mem_closedBall_self ht), ?_⟩
    intro hfront
    obtain ⟨y, hy, hxy⟩ := (mem_offset_iff_exists_dist_le isClosed_frontier).mp hfront
    rw [hD.frontier_eq] at hy
    exact hy.2 (hball (Metric.mem_closedBall.mpr ((dist_comm y x).trans_le hxy)))

private theorem offset_homothety_image {C : Set Point2} (hC : IsClosed C)
    (p : Point2) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    offset (AffineMap.homothety p a '' C) r =
      AffineMap.homothety p a '' offset C (r / a) := by
  let H := AffineMap.homothety p a
  let e := AffineEquiv.homothetyUnitsMulHom p (Units.mk0 a ha.ne')
  let homeo := (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph
  have he : (homeo : Point2 → Point2) = H := rfl
  have hHC : IsClosed (H '' C) := by
    rw [← he]
    exact homeo.isClosedMap _ hC
  have hdist (x y : Point2) : dist (H x) (H y) = a * dist x y := by
    rw [show H = AffineMap.homothety p a from rfl, dist_homothety, Real.norm_eq_abs,
      abs_of_nonneg ha.le]
  ext z
  obtain ⟨x, rfl⟩ := homeo.surjective z
  change H x ∈ offset (H '' C) r ↔ H x ∈ H '' offset C (r / a)
  rw [mem_offset_iff_exists_dist_le hHC]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    rw [hdist] at hxy
    exact ⟨x, (mem_offset_iff_exists_dist_le hC).mpr
      ⟨y, hy, (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hxy)⟩, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    have hwEq : w = x := homeo.injective hwx
    subst w
    obtain ⟨y, hy, hxy⟩ := (mem_offset_iff_exists_dist_le hC).mp hw
    refine ⟨H y, ⟨y, hy, rfl⟩, ?_⟩
    rw [hdist]
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hxy

namespace Affine.Simplex

variable (s : Simplex ℝ Point2 2)

private theorem signedInfDist_eq_signedDist_altitudeFoot (i : Fin 3) :
    s.signedInfDist i = signedDist (s.points i -ᵥ s.altitudeFoot i) (s.altitudeFoot i) := by
  rw [Affine.Simplex.signedInfDist,
    AffineSubspace.signedInfDist_eq_signedDist_of_mem (s.altitudeFoot_mem_affineSpan_image_compl i)]
  have hproj : (EuclideanGeometry.orthogonalProjection
      (affineSpan ℝ (s.points '' {i}ᶜ)) (s.points i) : Point2) = s.altitudeFoot i := by
    unfold altitudeFoot orthogonalProjectionSpan
    exact EuclideanGeometry.orthogonalProjection_congr
      (congrArg (affineSpan ℝ) (s.range_faceOpposite_points i).symm) rfl
  rw [hproj]

private theorem interior_hull_eq_signedInfDist :
    interior (convexHull ℝ (range s.points)) = {x | ∀ i, 0 < s.signedInfDist i x} := by
  let b : AffineBasis (Fin 3) ℝ Point2 :=
    ⟨s.points, s.independent, s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp)⟩
  change interior (convexHull ℝ (range b)) = _
  rw [b.interior_convexHull]
  ext x
  change (∀ i, 0 < b.coord i x) ↔ ∀ i, 0 < s.signedInfDist i x
  have hcoord (i : Fin 3) : s.signedInfDist i x =
      b.coord i x * ‖s.points i -ᵥ s.altitudeFoot i‖ := by
    calc
      _ = s.signedInfDist i (Finset.univ.affineCombination ℝ b (fun j => b.coord j x)) := by
        rw [b.affineCombination_coord_eq_self]
      _ = _ := s.signedInfDist_affineCombination i (b.sum_coord_apply_eq_one x)
  simp only [hcoord, mul_pos_iff_of_pos_right
    (norm_pos_iff.mpr (vsub_ne_zero.mpr (s.ne_altitudeFoot _)))]

private theorem closedBall_subset_triangle_interior_iff {x : Point2} {t : ℝ} (ht : 0 ≤ t) :
    Metric.closedBall x t ⊆ interior (convexHull ℝ (range s.points)) ↔
      ∀ i, t < s.signedInfDist i x := by
  rw [s.interior_hull_eq_signedInfDist]
  constructor
  · intro hball i
    let v : Point2 := s.points i -ᵥ s.altitudeFoot i
    let n := NormedSpace.normalize v
    have hn : ‖n‖ = 1 := NormedSpace.norm_normalize_eq_one_iff.mpr
      (vsub_ne_zero.mpr (s.ne_altitudeFoot i))
    let y : Point2 := (-t) • n +ᵥ x
    have hy : y ∈ Metric.closedBall x t := by
      rw [Metric.mem_closedBall, dist_eq_norm_vsub, show y -ᵥ x = (-t) • n by simp [y],
        norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht, hn, mul_one]
    have hpos : 0 < s.signedInfDist i y := hball hy i
    rw [s.signedInfDist_eq_signedDist_altitudeFoot i] at hpos ⊢
    change 0 < signedDist v (s.altitudeFoot i) ((-t) • n +ᵥ x) at hpos
    rw [signedDist_vadd_right, real_inner_smul_right,
      show NormedSpace.normalize v = n from rfl, real_inner_self_eq_norm_sq, hn] at hpos
    linarith
  · intro h y hy i
    have hbound := signedDist_le_dist (s.points i -ᵥ s.altitudeFoot i) y x
    rw [← signedDist_triangle_left _ (s.altitudeFoot i) x y,
      ← s.signedInfDist_eq_signedDist_altitudeFoot i] at hbound
    linarith [h i, Metric.mem_closedBall.mp hy]

/-- The open inset is obtained by a homothety about the incenter.
The inset depth is the distance to each shifted supporting line. -/
theorem open_inset_eq_homothety_image {t : ℝ} (ht : 0 ≤ t) (hsmall : t < s.inradius) :
    let D := interior (convexHull ℝ (range s.points))
    D \ offset (frontier D) t =
      AffineMap.homothety s.incenter (1 - t / s.inradius) '' D := by
  dsimp only
  let a := 1 - t / s.inradius
  have hρ := s.inradius_pos
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hρ).mpr hsmall)
  have hshift : (1 - a) * s.inradius = t := by
    calc
      (1 - a) * s.inradius = (t / s.inradius) * s.inradius := by dsimp [a]; ring
      _ = t := div_mul_cancel₀ _ hρ.ne'
  have hmap (x : Point2) (i : Fin 3) :
      s.signedInfDist i (AffineMap.homothety s.incenter a x) =
        t + a * s.signedInfDist i x := by
    rw [AffineMap.homothety_eq_lineMap, ← ContinuousAffineMap.coe_toAffineMap,
      AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      ContinuousAffineMap.coe_toAffineMap, s.signedInfDist_incenter, hshift]
  ext y
  rw [mem_open_inset_iff_ball_subset isOpen_interior ht,
    s.closedBall_subset_triangle_interior_iff ht]
  constructor
  · intro hy
    let x := AffineMap.homothety s.incenter a⁻¹ y
    have hxy : AffineMap.homothety s.incenter a x = y := by
      simp [x, ← AffineMap.homothety_mul_apply, ha.ne']
    refine ⟨x, ?_, hxy⟩
    rw [s.interior_hull_eq_signedInfDist]
    intro i
    have h := hy i
    rw [← hxy, hmap] at h
    exact pos_of_mul_pos_right (by linarith : 0 < a * s.signedInfDist i x) ha.le
  · rintro ⟨x, hx, rfl⟩ i
    rw [s.interior_hull_eq_signedInfDist] at hx
    rw [hmap]
    exact lt_add_of_pos_right _ (mul_pos ha (hx i))

/-- The closed inset is the homothetic image of the closed triangle. -/
theorem closure_open_inset_eq_homothety_image {t : ℝ} (ht : 0 ≤ t) (hsmall : t < s.inradius) :
    let C := convexHull ℝ (range s.points)
    let D := interior C
    closure (D \ offset (frontier D) t) =
      AffineMap.homothety s.incenter (1 - t / s.inradius) '' C := by
  dsimp only
  let C := convexHull ℝ (range s.points)
  let a := 1 - t / s.inradius
  have ha : 0 < a := sub_pos.mpr ((div_lt_one s.inradius_pos).mpr hsmall)
  let e := AffineEquiv.homothetyUnitsMulHom s.incenter (Units.mk0 a ha.ne')
  let homeo := (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph
  have he : (homeo : Point2 → Point2) =
      AffineMap.homothety s.incenter a := rfl
  have hconv : Convex ℝ C := convex_convexHull _ _
  have hclosed : IsClosed C := (finite_range s.points).isClosed_convexHull ℝ
  have hne : (interior C).Nonempty := by
    rw [s.interior_hull_eq_signedInfDist]
    exact ⟨s.incenter, fun i => by rw [s.signedInfDist_incenter]; exact s.inradius_pos⟩
  have hclosure := (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans
    hclosed.closure_eq
  rw [s.open_inset_eq_homothety_image ht hsmall]
  change closure (AffineMap.homothety s.incenter a '' interior C) =
    AffineMap.homothety s.incenter a '' C
  rw [← he, ← homeo.image_closure, hclosure]

/-- Deleting a triangle interior loses the area of the offset of its homothetic inset. -/
theorem volume_extendedBody_sdiff_triangle {A : Set Point2}
    (hA : IsClosed A) (hCA : convexHull ℝ (range s.points) ⊆ A)
    {r : ℝ} (hr : 0 < r) (hsmall : 2 * r < s.inradius) :
    let C := convexHull ℝ (range s.points)
    MeasureTheory.volume (extendedBody A r \ extendedBody (A \ interior C) r) =
      MeasureTheory.volume
        (offset (AffineMap.homothety s.incenter (1 - (2 * r) / s.inradius) '' C) r) := by
  dsimp only
  apply volume_extendedBody_sdiff_open_deletion hA isOpen_interior
    (interior_subset.trans hCA) hr (s.closure_open_inset_eq_homothety_image (by positivity) hsmall)
  exact (convex_convexHull _ _).affine_image _

/-- In the triangle deletion calculation, scaling the closed inset back to the
original triangle divides the offset radius by the homothety factor. -/
theorem area_extendedBody_sdiff_triangle_eq_rescaled_offset {A : Set Point2}
    (hA : IsClosed A) (hCA : convexHull ℝ (range s.points) ⊆ A)
    {r : ℝ} (hr : 0 < r) (hsmall : 2 * r < s.inradius) :
    let C := convexHull ℝ (range s.points)
    let a := 1 - (2 * r) / s.inradius
    (MeasureTheory.volume (extendedBody A r \ extendedBody (A \ interior C) r)).toReal =
      a ^ 2 * (MeasureTheory.volume (offset C (r / a))).toReal := by
  dsimp only
  rw [s.volume_extendedBody_sdiff_triangle hA hCA hr hsmall]
  have ha : 0 < 1 - 2 * r / s.inradius := sub_pos.mpr ((div_lt_one s.inradius_pos).mpr hsmall)
  rw [offset_homothety_image ((finite_range s.points).isClosed_convexHull ℝ) _ ha,
    MeasureTheory.Measure.addHaar_image_homothety, ENNReal.toReal_mul]
  simp [abs_of_nonneg (sq_nonneg (1 - 2 * r / s.inradius)),
    ENNReal.toReal_ofReal (sq_nonneg (1 - 2 * r / s.inradius))]

/-- The triangle deletion polynomial follows from the ordinary convex offset formula
for that triangle. The perimeter is the sum of the three opposite edge lengths. -/
theorem area_extendedBody_sdiff_triangle_of_offset_formula {A : Set Point2}
    (hA : IsClosed A) (hCA : convexHull ℝ (range s.points) ⊆ A)
    {r : ℝ} (hr : 0 < r) (hsmall : 2 * r < s.inradius)
    (hpoly : ∀ u : ℝ, 0 ≤ u →
      (MeasureTheory.volume (offset (convexHull ℝ (range s.points)) u)).toReal =
        s.volume + u * (∑ i, (s.faceOpposite i).volume) + Real.pi * u ^ 2) :
    (MeasureTheory.volume (extendedBody A r \
      extendedBody (A \ interior (convexHull ℝ (range s.points))) r)).toReal =
        s.volume - r * (∑ i, (s.faceOpposite i).volume) + Real.pi * r ^ 2 := by
  rw [s.area_extendedBody_sdiff_triangle_eq_rescaled_offset hA hCA hr hsmall]
  let a := 1 - 2 * r / s.inradius
  let p := ∑ i, (s.faceOpposite i).volume
  have hρ := s.inradius_pos
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hρ).mpr hsmall)
  have hshift : (1 - a) * s.inradius = 2 * r := by
    calc
      (1 - a) * s.inradius = (2 * r / s.inradius) * s.inradius := by dsimp [a]; ring
      _ = 2 * r := div_mul_cancel₀ _ hρ.ne'
  have hvol : 2 * s.volume = s.inradius * p := by
    have h : s.volume = (2 : ℝ)⁻¹ * s.inradius * p := s.volume_eq_inradius_mul
    calc
      2 * s.volume = 2 * ((2 : ℝ)⁻¹ * s.inradius * p) := congrArg (fun v => 2 * v) h
      _ = _ := by ring
  have hbalance : (1 - a) * s.volume = r * p := by
    linear_combination ((1 - a) / 2) * hvol + (p / 2) * hshift
  change a ^ 2 * (MeasureTheory.volume (offset (convexHull ℝ (range s.points)) (r / a))).toReal =
    s.volume - r * p + Real.pi * r ^ 2
  rw [hpoly _ (div_nonneg hr.le ha.le)]
  change a ^ 2 * (s.volume + (r / a) * p + Real.pi * (r / a) ^ 2) = _
  calc
    _ = a ^ 2 * s.volume + a * r * p + Real.pi * r ^ 2 := by
      field_simp [ha.ne']
    _ = _ := by linear_combination -(a + 1) * hbalance

end Affine.Simplex
