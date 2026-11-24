import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import SteinerProof.Separation

/-! The admissible radius and incident-angle bounds of Section 2.5. -/

noncomputable section

open InnerProductGeometry

namespace FinitePlanarComplex

private def angleFactor (θ : ℝ) : ℝ :=
  1 + (Real.sin (θ / 2))⁻¹ / 2

private theorem half_sin_pos {θ : ℝ} (hθ : 0 < θ) (hπ : θ ≤ Real.pi) :
    0 < Real.sin (θ / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

private theorem angleFactor_ge {θ : ℝ} (hθ : 0 < θ) (hπ : θ ≤ Real.pi) :
    3 / 2 ≤ angleFactor θ := by
  have h := half_sin_pos hθ hπ
  have h_inv : 1 ≤ (Real.sin (θ / 2))⁻¹ := by
    rw [← one_div, le_div_iff₀ h, one_mul]
    exact Real.sin_le_one _
  unfold angleFactor
  linarith

/-- The points of the complex that occur as vertices of faces. -/
private def vertexPoints (K : FinitePlanarComplex) : Finset PLPoint := by
  classical
  exact K.faceFinset.biUnion id

private theorem mem_vertexPoints {K : FinitePlanarComplex} {u : PLPoint} :
    u ∈ K.vertexPoints ↔ u ∈ K.simplices.vertices := by
  classical
  rw [K.simplices.vertices_eq]
  simp [vertexPoints, mem_faceFinset_iff]

private def incidentAngles (K : FinitePlanarComplex) : Finset ℝ := by
  classical
  exact (((K.vertexPoints ×ˢ (K.vertexPoints ×ˢ K.vertexPoints)).filter
    (fun (v, u, w) => u ≠ w ∧ ({v, u} : Finset PLPoint) ∈ K.edges ∧
      ({v, w} : Finset PLPoint) ∈ K.edges)).image
      (fun (v, u, w) => angle (u - v) (w - v))).filter (fun θ => 0 < θ)

/-- The maximum incident-angle factor, with the straight-angle value
`3 / 2` included as the default. -/
def angleScale (K : FinitePlanarComplex) : ℝ := by
  classical
  exact (insert (3 / 2) (K.incidentAngles.image angleFactor)).max'
    (Finset.insert_nonempty _ _)

theorem angleScale_ge (K : FinitePlanarComplex) : 3 / 2 ≤ K.angleScale := by
  classical
  unfold angleScale
  apply Finset.le_max'
  exact Finset.mem_insert_self _ _

private theorem angleScale_eq_max_of_nonempty (K : FinitePlanarComplex)
    (h : (K.incidentAngles.image angleFactor).Nonempty) :
    K.angleScale = (K.incidentAngles.image angleFactor).max' h := by
  classical
  have hmax : (K.incidentAngles.image angleFactor).max' h ∈
      K.incidentAngles.image angleFactor := Finset.max'_mem _ _
  obtain ⟨θ, hθ, heq⟩ := Finset.mem_image.mp hmax
  obtain ⟨himage, hpos⟩ := Finset.mem_filter.mp hθ
  obtain ⟨⟨v, u, w⟩, _, rfl⟩ := Finset.mem_image.mp himage
  unfold angleScale
  rw [Finset.max'_insert, max_eq_right]
  exact heq ▸ angleFactor_ge hpos (angle_le_pi _ _)

private theorem edge_point_mem_vertices {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.edges) {v : PLPoint} (hv : v ∈ s) : v ∈ K.simplices.vertices := by
  rw [K.simplices.vertices_eq]
  exact Set.mem_iUnion₂.mpr ⟨s, (K.mem_edges_iff s).mp hs |>.1, hv⟩

theorem edge_endpoints_ne {K : FinitePlanarComplex} {v u : PLPoint}
    (h : ({v, u} : Finset PLPoint) ∈ K.edges) : u ≠ v := by
  intro heq
  subst u
  have hc := (K.mem_edges_iff _ |>.mp h).2
  simp at hc

/-- Every edge has length at least the vertex-face separation. -/
theorem vertexFaceSeparation_le_edge_dist {K : FinitePlanarComplex} {v u : PLPoint}
    (h : ({v, u} : Finset PLPoint) ∈ K.edges) : K.vertexFaceSeparation ≤ dist v u := by
  have hv := edge_point_mem_vertices h (v := v) (by simp)
  have hu : ({u} : Finset PLPoint) ∈ K.simplices.faces :=
    edge_point_mem_vertices h (v := u) (by simp)
  exact K.vertexFaceSeparation_le_dist hv hu
    (by simp [Ne.symm (edge_endpoints_ne h)]) (by simp)

/-- Distinct edges cannot leave a vertex on the same ray, by the intersection
property of a simplicial complex. -/
theorem incident_angle_pos (K : FinitePlanarComplex) {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w) :
    0 < angle (u - v) (w - v) := by
  have huFace := K.mem_edges_iff _ |>.mp hu
  have hwFace := K.mem_edges_iff _ |>.mp hw
  have huv := edge_endpoints_ne hu
  have hwv := edge_endpoints_ne hw
  have hvertexU := edge_point_mem_vertices hu (v := u) (by simp)
  have hvertexW := edge_point_mem_vertices hw (v := w) (by simp)
  by_contra! hnonpos
  have hang := le_antisymm hnonpos (angle_nonneg _ _)
  obtain ⟨_, a, ha, hscale⟩ := angle_eq_zero_iff.mp hang
  have hline {x y : PLPoint} {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
      (heq : y - v = t • (x - v)) : y ∈ convexHull ℝ ({v, x} : Set PLPoint) := by
    rw [convexHull_pair, segment_eq_image_lineMap]
    refine ⟨t, ⟨ht₀, ht₁⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', ← heq, sub_add_cancel]
  by_cases hle : a ≤ 1
  · have hwHull := hline ha.le hle hscale
    have hwMem := (K.simplices.vertex_mem_convexHull_iff hvertexW huFace.1).mp
      (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hwHull)
    simp [hwv, huw.symm] at hwMem
  · have hinv : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_ge hle)
    have hscale' : u - v = a⁻¹ • (w - v) := by
      rw [hscale, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    have huHull := hline (inv_nonneg.mpr ha.le) hinv hscale'
    have huMem := (K.simplices.vertex_mem_convexHull_iff hvertexU hwFace.1).mp
      (by simpa only [Finset.coe_insert, Finset.coe_singleton] using huHull)
    simp [huv, huw] at huMem

private theorem angleScale_ge_angleFactor (K : FinitePlanarComplex)
    {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθ : 0 < angle (u - v) (w - v)) :
    angleFactor (angle (u - v) (w - v)) ≤ K.angleScale := by
  classical
  have hvMem {s : Finset PLPoint} (h : s ∈ K.edges) {x : PLPoint} (hx : x ∈ s) :
      x ∈ K.vertexPoints := by
    exact mem_vertexPoints.mpr (edge_point_mem_vertices h hx)
  have hv := hvMem hu (x := v) (by simp)
  have huv := hvMem hu (x := u) (by simp)
  have hwv := hvMem hw (x := w) (by simp)
  have hmem : angle (u - v) (w - v) ∈ K.incidentAngles := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(v, u, w), ?_, rfl⟩, hθ⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hv, Finset.mem_product.mpr ⟨huv, hwv⟩⟩, huw, hu, hw⟩
  unfold angleScale
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem)

/-- The paper's radius `M / (8 * Q)` with a finite default for the empty
vertex-face index, as in `vertexFaceSeparation`. -/
def admissibleRadius (K : FinitePlanarComplex) : ℝ :=
  K.vertexFaceSeparation / (8 * K.angleScale)

theorem admissibleRadius_pos (K : FinitePlanarComplex) : 0 < K.admissibleRadius := by
  have hQ : 0 < K.angleScale := by linarith [K.angleScale_ge]
  exact div_pos K.vertexFaceSeparation_pos (by positivity)

theorem admissibleRadius_le (K : FinitePlanarComplex) :
    K.admissibleRadius ≤ K.vertexFaceSeparation / 12 := by
  unfold admissibleRadius
  exact div_le_div_of_nonneg_left K.vertexFaceSeparation_pos.le (by norm_num)
    (by linarith [K.angleScale_ge])

/-- The angle-dependent inequality used in the arrowhead localization. -/
theorem incident_angle_radius_bound (K : FinitePlanarComplex) {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hθ : 0 < angle (u - v) (w - v)) {r : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) :
    2 * r * (1 + (Real.sin (angle (u - v) (w - v) / 2))⁻¹ / 2) <
      K.vertexFaceSeparation / 4 := by
  have hQ : 0 < K.angleScale := by linarith [K.angleScale_ge]
  have hR := (lt_div_iff₀ (show 0 < 8 * K.angleScale by positivity)).mp hrK
  have hfactor := K.angleScale_ge_angleFactor hu hw huw hθ
  change 2 * r * angleFactor (angle (u - v) (w - v)) < _
  exact (mul_le_mul_of_nonneg_left hfactor (by positivity)).trans_lt (by linarith)

/-- The radius keeps the incident-angle constructions inside the vertex separation scale. -/
theorem four_mul_one_add_csc_lt_separation (K : FinitePlanarComplex)
    {v u w : PLPoint} (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hθ : 0 < angle (u - v) (w - v)) {r : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) :
    4 * r * (1 + (Real.sin (angle (u - v) (w - v) / 2))⁻¹) <
      K.vertexFaceSeparation := by
  have h := K.incident_angle_radius_bound hu hw huw hθ hr hrK
  linarith

theorem four_mul_csc_lt_separation (K : FinitePlanarComplex)
    {v u w : PLPoint} (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hθ : 0 < angle (u - v) (w - v)) {r : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) :
    4 * r * (Real.sin (angle (u - v) (w - v) / 2))⁻¹ < K.vertexFaceSeparation := by
  linarith [K.four_mul_one_add_csc_lt_separation hu hw huw hθ hr hrK]

theorem six_mul_lt_separation_of_lt_admissibleRadius (K : FinitePlanarComplex) {r : ℝ}
    (hr : r < K.admissibleRadius) : 6 * r < K.vertexFaceSeparation := by
  linarith [hr.trans_le K.admissibleRadius_le, K.vertexFaceSeparation_pos]

end FinitePlanarComplex
