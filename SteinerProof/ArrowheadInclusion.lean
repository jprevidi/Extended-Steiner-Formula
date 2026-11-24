import SteinerProof.ArrowheadKite
import SteinerProof.ArrowheadLocalization

/-! Inclusion of the far arrowhead in the extended parallel body. -/

open Set InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

private theorem coefficient_bound_of_projection {K : FinitePlanarComplex}
    {v u w c : PLPoint} {a b r : ℝ}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : w ≠ v)
    (hrep : c - v = a • normalize (u - v) + b • normalize (w - v))
    (hb : 0 ≤ b) (hs : 0 ≤ ⟪c - v, normalize (u - v)⟫)
    (hc : dist c v < K.vertexFaceSeparation)
    (hfar : ∀ z ∈ segment ℝ v u, 2 * r < dist c z) :
    2 * r < b * Real.sin (angle (u - v) (w - v)) := by
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let θ := angle (u - v) (w - v)
  let L := ‖u - v‖
  let s := ⟪c - v, X⟫
  let z := v + s • X
  have hu' := sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hu)
  have hX : ‖X‖ = 1 := norm_normalize hu'
  have hL : 0 < L := norm_pos_iff.mpr hu'
  have hXs : L • X = u - v := norm_smul_normalize _
  have hc' : ‖c - v‖ < K.vertexFaceSeparation := by rwa [← dist_eq_norm]
  have hsM : s ≤ ‖c - v‖ := by simpa only [hX, mul_one] using real_inner_le_norm (c-v) X
  have hsL : s ≤ L := by
    have h := hsM.trans (hc'.le.trans (FinitePlanarComplex.vertexFaceSeparation_le_edge_dist hu))
    simpa only [dist_comm v u, dist_eq_norm] using h
  have hz : z ∈ segment ℝ v u := by
    rw [segment_eq_image_lineMap]
    refine ⟨s / L, ⟨div_nonneg hs hL.le, (div_le_one hL).mpr hsL⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', ← hXs, smul_smul, div_mul_cancel₀ _ hL.ne']
    exact add_comm _ _
  have hYX : ⟪Y, X⟫ = Real.cos θ := (real_inner_comm _ _).trans
    (inner_normalize_eq_cos_angle hu' (sub_ne_zero.mpr hw))
  have hs_eq : s = a + b * Real.cos θ := by
    change ⟪c-v, X⟫ = _
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hX, hYX, one_pow, mul_one]
  have hcz : c - z = b • (Y - Real.cos θ • X) := by
    calc
      c - z = (c - v) - s • X := by dsimp [z]; abel
      _ = _ := by
        rw [hrep, hs_eq, add_smul, mul_smul, smul_sub]
        abel
  have h := hfar z hz
  rw [dist_eq_norm, hcz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
    norm_normalize_sub_cos_smul hu' (sub_ne_zero.mpr hw)] at h
  exact h

private theorem two_coefficient_bounds {K : FinitePlanarComplex}
    {v u w c : PLPoint} {a b r : ℝ}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hrep : c - v = a • normalize (u - v) + b • normalize (w - v))
    (ha : 0 < a) (hb : 0 < b) (hc : dist c v < K.vertexFaceSeparation)
    (hfar₀ : ∀ z ∈ segment ℝ v u, 2 * r < dist c z)
    (hfar₁ : ∀ z ∈ segment ℝ v w, 2 * r < dist c z) :
    2 * r < a * Real.sin (angle (u - v) (w - v)) ∧
      2 * r < b * Real.sin (angle (u - v) (w - v)) := by
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let θ := angle (u - v) (w - v)
  let k := Real.cos θ
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hX : ‖X‖ = 1 := norm_normalize (sub_ne_zero.mpr huv)
  have hY : ‖Y‖ = 1 := norm_normalize (sub_ne_zero.mpr hwv)
  have hXY : ⟪X, Y⟫ = k := inner_normalize_eq_cos_angle (sub_ne_zero.mpr huv) (sub_ne_zero.mpr hwv)
  have hYX : ⟪Y, X⟫ = k := (real_inner_comm _ _).trans hXY
  have hs : ⟪c-v,X⟫ = a + b * k := by
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hX, one_pow, mul_one, hYX]
  have ht : ⟪c-v,Y⟫ = a * k + b := by
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hY, one_pow, mul_one, hXY]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hk : -1 ≤ k := Real.neg_one_le_cos θ
  have hbu (h : 0 ≤ a + b * k) : 2 * r < b * Real.sin θ :=
    coefficient_bound_of_projection hu hwv hrep hb.le (hs.symm ▸ h) hc hfar₀
  have haw (h : 0 ≤ a * k + b) : 2 * r < a * Real.sin θ := by
    have hrep' : c - v = b • Y + a • X := hrep.trans (add_comm _ _)
    have h' := coefficient_bound_of_projection hw huv hrep' ha.le (ht.symm ▸ h) hc hfar₁
    simpa only [angle_comm (w-v) (u-v)] using h'
  by_cases h₀ : 0 ≤ a + b * k
  · by_cases h₁ : 0 ≤ a * k + b
    · exact ⟨haw h₁, hbu h₀⟩
    · have hab : b < a := by nlinarith [mul_nonneg ha.le (show 0 ≤ k + 1 by linarith)]
      exact ⟨(hbu h₀).trans (mul_lt_mul_of_pos_right hab hsin), hbu h₀⟩
  · have hab : a < b := by nlinarith [mul_nonneg hb.le (show 0 ≤ k + 1 by linarith)]
    have h₁ : 0 ≤ a * k + b := by
      nlinarith [mul_nonneg ha.le (show 0 ≤ k + 1 by linarith)]
    exact ⟨haw h₁, (haw h₁).trans (mul_lt_mul_of_pos_right hab hsin)⟩

/-- The far arrowhead lies in the extended parallel body at admissible radius.
The inclusion itself uses only the two defining edges. -/
theorem farArrowhead_subset_extendedBody {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ A.edges) (huw : u ≠ w)
    (hπ : angle (u - v) (w - v) < Real.pi)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    farArrowhead v u w r ⊆ extendedBody A.realization r := by
  obtain ⟨huF, huC⟩ := (A.mem_edges_iff _).mp hu
  obtain ⟨hwF, hwC⟩ := (A.mem_edges_iff _).mp hw
  have huK : ({v, u} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK huF, huC⟩
  have hwK : ({v, w} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK hwF, hwC⟩
  have hθ := K.incident_angle_pos huK hwK huw
  have huv := FinitePlanarComplex.edge_endpoints_ne huK
  have hwv := FinitePlanarComplex.edge_endpoints_ne hwK
  have hsu : segment ℝ v u ⊆ A.realization := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      A.convexHull_face_subset_realization _ huF
  have hsw : segment ℝ v w ⊆ A.realization := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      A.convexHull_face_subset_realization _ hwF
  rw [extendedBody_eq_erosion A.realization r A.isClosed_realization hr.le]
  intro x hx c hc
  have hdist := Metric.mem_closedBall.mp hc
  by_contra hout
  have hfar (z : PLPoint) (hz : z ∈ A.realization) : 2 * r < dist c z :=
    lt_of_not_ge fun h =>
      hout ((mem_offset_iff_exists_dist_le A.isClosed_realization).mpr ⟨z, hz, h⟩)
  have hxi : x ∈ interior (farKite v u w r) := by
    rw [farArrowhead, ite_eq_left hπ] at hx
    exact hx.1
  have hxM := Metric.mem_ball.mp
    (farKite_subset_separation_ball huK hwK huw hπ hr hR (interior_subset hxi))
  have hcM : dist c v < K.vertexFaceSeparation := by
    have hh := dist_triangle c x v
    linarith [hR.trans_le K.admissibleRadius_le, K.vertexFaceSeparation_pos]
  have hn₀ := inner_pos_of_dist_le_of_mem_interior_farKite hr huv hwv hθ hπ hxi hdist
  have hxi' : x ∈ interior (farKite v w u r) := farKite_comm v u w r ▸ hxi
  have hn₁ := inner_pos_of_dist_le_of_mem_interior_farKite hr hwv huv
    (by rwa [angle_comm]) (by rwa [angle_comm]) hxi' hdist
  obtain ⟨basis, hb₀, hb₁⟩ := exists_incident_basis huv hwv hθ hπ
  let a := basis.repr (c-v) 0 * ‖u-v‖
  let b := basis.repr (c-v) 1 * ‖w-v‖
  let θ := angle (u-v) (w-v)
  have hrep : c-v = a • normalize (u-v) + b • normalize (w-v) := by
    dsimp [a, b]
    rw [mul_smul, mul_smul, norm_smul_normalize, norm_smul_normalize, ← hb₀, ← hb₁]
    have h := basis.sum_repr (c-v)
    rw [Fin.sum_univ_two] at h
    exact h.symm
  have hproof₀ := inner_nearKiteShoulder_directions (r := r) huv hwv hθ hπ
  have hproof₁ := inner_nearKiteShoulder_directions (r := r) hwv huv
    (by rwa [angle_comm]) (by rwa [angle_comm])
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hb : 0 < b := by
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hproof₀.1, hproof₀.2, mul_zero, zero_add] at hn₀
    exact pos_of_mul_pos_left hn₀ (mul_pos hr hsin).le
  have ha : 0 < a := by
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hproof₁.1, hproof₁.2, mul_zero, add_zero, angle_comm (w-v) (u-v)] at hn₁
    exact pos_of_mul_pos_left hn₁ (mul_pos hr hsin).le
  obtain ⟨ha₂, hb₂⟩ := two_coefficient_bounds huK hwK hθ hπ hrep ha hb hcM
    (fun z hz => hfar z (hsu hz)) (fun z hz => hfar z (hsw hz))
  let d := 2 * r / Real.sin θ
  have had : 0 < a - d := sub_pos.mpr ((div_lt_iff₀ hsin).mpr ha₂)
  have hbd : 0 < b - d := sub_pos.mpr ((div_lt_iff₀ hsin).mpr hb₂)
  have htip : c - arrowheadBisectorPoint v u w r 2 =
      (a-d) • normalize (u-v) + (b-d) • normalize (w-v) := by
    rw [show c - arrowheadBisectorPoint v u w r 2 =
      (c-v) - (arrowheadBisectorPoint v u w r 2 - v) by abel, hrep]
    change _ - (v + d • (normalize (u-v) + normalize (w-v)) - v) = _
    rw [add_sub_cancel_left, smul_add, sub_smul, sub_smul]
    abel
  exact (not_lt_of_ge hdist) (lt_dist_of_mem_farArrowhead_of_beyond_tip
    hr huv hwv hθ hπ hx had hbd htip)

end SteinerProof
