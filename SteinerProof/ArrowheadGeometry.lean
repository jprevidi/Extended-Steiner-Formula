import SteinerProof.AdmissibleRadius

/-! The bisector points used to construct the near and far arrowheads in Section 3. -/

noncomputable section

open InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

namespace SteinerProof

/-- The point `p_α` on the bisector at `v`, used for angles strictly between
zero and pi. -/
def arrowheadBisectorPoint (v u w : PLPoint) (r α : ℝ) : PLPoint :=
  v + (α * r / Real.sin (angle (u - v) (w - v))) • (normalize (u - v) + normalize (w - v))

theorem inner_normalize_eq_cos_angle {x y : PLPoint} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪normalize x, normalize y⟫ = Real.cos (angle x y) := by
  have ha : angle (normalize x) (normalize y) = angle x y := by
    unfold NormedSpace.normalize
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hx)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hy))]
  simpa only [ha, norm_normalize hx, norm_normalize hy, mul_one] using
    (cos_angle_mul_norm_mul_norm (normalize x) (normalize y)).symm

/-- The transverse component of a unit direction has length `sin θ`. -/
theorem norm_normalize_sub_cos_smul {x y : PLPoint} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖normalize y - Real.cos (angle x y) • normalize x‖ = Real.sin (angle x y) := by
  let θ := angle x y
  let c := Real.cos θ
  have hinner : ⟪normalize y, normalize x⟫ = c :=
    (real_inner_comm _ _).trans (inner_normalize_eq_cos_angle hx hy)
  apply (sq_eq_sq₀ (norm_nonneg _) (sin_angle_nonneg x y)).mp
  rw [norm_sub_sq_real, norm_normalize hy, norm_smul, Real.norm_eq_abs,
    norm_normalize hx, mul_one, sq_abs, real_inner_smul_right, hinner]
  have htrig := Real.sin_sq_add_cos_sq θ
  change 1 ^ 2 - 2 * (c * c) + c ^ 2 = Real.sin θ ^ 2
  change Real.sin θ ^ 2 + c ^ 2 = 1 at htrig
  linarith

private theorem norm_normalize_add {x y : PLPoint} (hx : x ≠ 0) (hy : y ≠ 0)
    (hθ : angle x y < Real.pi) :
    ‖normalize x + normalize y‖ = 2 * Real.cos (angle x y / 2) := by
  have hc : 0 < Real.cos (angle x y / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, angle_nonneg x y], by linarith⟩
  have hx₁ := norm_normalize hx
  have hy₁ := norm_normalize hy
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_add_sq_real, hx₁, hy₁, inner_normalize_eq_cos_angle hx hy]
  have hdouble : Real.cos (angle x y) = 2 * Real.cos (angle x y / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, show 2 * (angle x y / 2) = angle x y by ring]
  rw [hdouble]
  ring

/-- The distance from the common vertex to `p_α` in the paper's bisector lemma. -/
theorem dist_arrowheadBisectorPoint (v u w : PLPoint) {r α : ℝ}
    (hr : 0 ≤ r) (hα : 0 ≤ α) (hu : u ≠ v) (hw : w ≠ v)
    (hθ₀ : 0 < angle (u - v) (w - v)) (hθπ : angle (u - v) (w - v) < Real.pi) :
    dist (arrowheadBisectorPoint v u w r α) v =
      α * r * (Real.sin (angle (u - v) (w - v) / 2))⁻¹ := by
  let θ := angle (u - v) (w - v)
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
  have hsinHalf : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [show 0 < θ from hθ₀])
      (by linarith [show θ < Real.pi from hθπ, Real.pi_pos])
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [show 0 < θ from hθ₀, Real.pi_pos], by linarith [show θ < Real.pi from hθπ]⟩
  have hdouble : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul, show 2 * (θ / 2) = θ by ring]
  rw [arrowheadBisectorPoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hα hr) hsin.le),
    norm_normalize_add (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw) hθπ]
  change α * r / Real.sin θ * (2 * Real.cos (θ / 2)) = α * r * (Real.sin (θ / 2))⁻¹
  rw [hdouble]
  field_simp [hcos.ne', hsinHalf.ne']

/-- For the admissible radii, the points `p_α` with `0 ≤ α ≤ 4` lie inside
the vertex-to-face separation distance of their common vertex. -/
theorem dist_arrowheadBisectorPoint_lt_separation
    {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4) :
    dist (arrowheadBisectorPoint v u w r α) v < K.vertexFaceSeparation := by
  have hθ := K.incident_angle_pos hu hw huw
  rw [dist_arrowheadBisectorPoint v u w hr.le hα
    (FinitePlanarComplex.edge_endpoints_ne hu) (FinitePlanarComplex.edge_endpoints_ne hw) hθ hθπ]
  have hsin : 0 < Real.sin (angle (u - v) (w - v) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα₄ hr.le)
    (inv_nonneg.mpr hsin.le)).trans_lt (K.four_mul_csc_lt_separation hu hw huw hθ hr hrK)

/-- The bisector point is at distance `α * r` from the first finite edge.
The admissible radius puts the perpendicular foot on the edge segment. -/
theorem infDist_arrowheadBisectorPoint_edge
    {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4) :
    Metric.infDist (arrowheadBisectorPoint v u w r α) (segment ℝ v u) = α * r := by
  let θ := angle (u - v) (w - v)
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let d := α * r / Real.sin θ
  let c := Real.cos θ
  let k := d * (1 + c)
  let p := arrowheadBisectorPoint v u w r α
  let q := v + k • X
  have hu' := sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hu)
  have hw' := sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hw)
  have hX : ‖X‖ = 1 := norm_normalize hu'
  have hY : ‖Y‖ = 1 := norm_normalize hw'
  have hXY : ⟪X, Y⟫ = c := inner_normalize_eq_cos_angle hu' hw'
  have hYX : ⟪Y, X⟫ = c := (real_inner_comm _ _).trans hXY
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (K.incident_angle_pos hu hw huw) hθπ
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hα hr.le) hsin.le
  have hp : p - v = d • (X + Y) := add_sub_cancel_left v _
  have hk : 0 ≤ k := mul_nonneg hd (by linarith [Real.neg_one_le_cos θ])
  have hk_inner : ⟪p - v, X⟫ = k := by
    rw [hp, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hX, hYX]
    simp [k]
  have hk_le : k ≤ dist v u := by
    have hk_norm : k ≤ ‖p - v‖ := by
      rw [← hk_inner]
      simpa only [hX, mul_one] using real_inner_le_norm (p - v) X
    have hbound := dist_arrowheadBisectorPoint_lt_separation hu hw huw hθπ hr hrK hα hα₄
    rw [dist_eq_norm] at hbound
    exact hk_norm.trans (hbound.le.trans (FinitePlanarComplex.vertexFaceSeparation_le_edge_dist hu))
  let L := ‖u - v‖
  have huX : u - v = L • X := by
    dsimp [L, X, NormedSpace.normalize]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu'), one_smul]
  have huNorm : 0 < L := norm_pos_iff.mpr hu'
  have hq : q ∈ segment ℝ v u := by
    rw [segment_eq_image_lineMap]
    refine ⟨k / L, ⟨div_nonneg hk huNorm.le, (div_le_one huNorm).mpr ?_⟩, ?_⟩
    · simpa only [dist_comm v u, dist_eq_norm] using hk_le
    · rw [AffineMap.lineMap_apply_module', huX, smul_smul, div_mul_cancel₀ _ huNorm.ne']
      exact add_comm _ _
  have hpq : p - q = d • (Y - c • X) := by
    change (v + d • (X + Y)) - (v + (d * (1 + c)) • X) = _
    simp only [smul_add, mul_add, mul_one, add_smul, smul_sub, mul_smul]
    abel
  have hperp : ⟪p - q, X⟫ = 0 := by
    rw [hpq, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hYX,
      real_inner_self_eq_norm_sq, hX]
    ring
  have hmin : ‖p - q‖ = ⨅ z : segment ℝ v u, ‖p - z‖ := by
    apply (norm_eq_iInf_iff_real_inner_le_zero (convex_segment v u) hq).mpr
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, _, rfl⟩ := hz
    have hzq : AffineMap.lineMap v u t - q = (t * L - k) • X := by
      rw [AffineMap.lineMap_apply_module', huX, smul_smul, sub_smul]
      dsimp [q]
      abel
    rw [hzq, real_inner_smul_right, hperp, mul_zero]
  have hn := norm_normalize_sub_cos_smul hu' hw'
  calc
    Metric.infDist p (segment ℝ v u) = ‖p - q‖ := by
      simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hmin.symm
    _ = α * r := by
      rw [hpq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, hn]
      exact div_mul_cancel₀ _ hsin.ne'

theorem arrowheadBisectorPoint_comm (v u w : PLPoint) (r α : ℝ) :
    arrowheadBisectorPoint v u w r α = arrowheadBisectorPoint v w u r α := by
  unfold arrowheadBisectorPoint
  rw [angle_comm (u - v) (w - v), add_comm (normalize (u - v)) (normalize (w - v))]

/-- The bisector point has the same distance to the second finite edge. -/
theorem infDist_arrowheadBisectorPoint_other_edge
    {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4) :
    Metric.infDist (arrowheadBisectorPoint v u w r α) (segment ℝ v w) = α * r := by
  rw [arrowheadBisectorPoint_comm v u w]
  exact infDist_arrowheadBisectorPoint_edge hw hu huw.symm
    (by simpa only [angle_comm (w - v) (u - v)] using hθπ) hr hrK hα hα₄

end SteinerProof
