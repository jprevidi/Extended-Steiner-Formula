import SteinerProof.ArrowheadRecognition
import SteinerProof.ArrowheadSectors

/-! The exterior refinement of the consecutive-arrowhead characterization. -/

open Set InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

/-- An interior point of the far kite belongs to the open sector of its incident edges. -/
theorem exists_pos_edge_combination_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hr : 0 < r)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x - v = a • (u - v) + b • (w - v) := by
  obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis hu hw hθ hπ
  let a := B.repr (x - v) 0
  let b := B.repr (x - v) 1
  have hrep : x - v = a • (u - v) + b • (w - v) := by
    have h := B.sum_repr (x - v)
    rw [Fin.sum_univ_two, hB₀, hB₁] at h
    exact h.symm
  have hpos {y z : PLPoint} {A B : ℝ} (hy : y ≠ v) (hz : z ≠ v)
      (h₀ : 0 < angle (y - v) (z - v)) (h₁ : angle (y - v) (z - v) < Real.pi)
      (hrep : x - v = A • (y - v) + B • (z - v)) (hx : x ∈ interior (farKite v y z r)) :
      0 < B := by
    let N := nearKiteShoulder v y z r - v
    obtain ⟨hNy, hNz⟩ := inner_nearKiteShoulder_directions (r := r) hy hz h₀ h₁
    have hy₀ : ⟪y - v, N⟫ = 0 := calc
      _ = ⟪‖y - v‖ • normalize (y - v), N⟫ :=
        congrArg (fun t : PLPoint => ⟪t, N⟫) (norm_smul_normalize _).symm
      _ = _ := by rw [real_inner_smul_left, hNy, mul_zero]
    have hz₀ : ⟪z - v, N⟫ = ‖z - v‖ * (r * Real.sin (angle (y - v) (z - v))) := by
      calc
        _ = ⟪‖z - v‖ • normalize (z - v), N⟫ :=
          congrArg (fun t : PLPoint => ⟪t, N⟫) (norm_smul_normalize _).symm
        _ = _ := by rw [real_inner_smul_left, hNz]
    have h := lt_inner_of_mem_interior_farKite hr hy hz h₀ h₁ hx
    change r ^ 2 < ⟪x - v, N⟫ at h
    rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left, hy₀, mul_zero,
      zero_add, hz₀] at h
    exact pos_of_mul_pos_left ((sq_nonneg r).trans_lt h)
      (mul_nonneg (norm_nonneg _) (mul_nonneg hr.le (sin_angle_nonneg _ _)))
  have hx' : x ∈ interior (farKite v w u r) := farKite_comm v u w r ▸ hx
  have hrep' : x - v = b • (w - v) + a • (u - v) := hrep.trans (add_comm _ _)
  exact ⟨a, b, hpos hw hu (by rwa [angle_comm]) (by rwa [angle_comm]) hrep' hx',
    hpos hu hw hθ hπ hrep hx, hrep⟩

/-- If the two incident edges bound a triangle of the complex, their far
arrowhead is contained in that triangle. -/
theorem farArrowhead_subset_triangle_of_mem_faces {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hπ : angle (u - v) (w - v) < Real.pi)
    (ht : ({v, u, w} : Finset PLPoint) ∈ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    farArrowhead v u w r ⊆ convexHull ℝ (({v, u, w} : Finset PLPoint) : Set PLPoint) := by
  let T := convexHull ℝ (({v, u, w} : Finset PLPoint) : Set PLPoint)
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hθ := K.incident_angle_pos hu hw huw
  have hT : Convex ℝ T := convex_convexHull ℝ _
  have hvT : v ∈ T := subset_convexHull ℝ _ (by simp)
  have huT : u ∈ T := subset_convexHull ℝ _ (by simp)
  have hwT : w ∈ T := subset_convexHull ℝ _ (by simp)
  intro x hx
  rw [farArrowhead, ite_eq_left hπ] at hx
  obtain ⟨a, b, ha, hb, hrep⟩ := exists_pos_edge_combination_of_mem_interior_farKite huv hwv hr hθ hπ hx.1
  let d := a + b
  have hd : 0 < d := add_pos ha hb
  let z := (a / d) • u + (b / d) • w
  have hweights : a / d + b / d = 1 := by rw [← add_div, div_self hd.ne']
  have hz : z ∈ segment ℝ u w :=
    convex_segment u w (left_mem_segment ℝ u w) (right_mem_segment ℝ u w)
      (div_nonneg ha.le hd.le) (div_nonneg hb.le hd.le) hweights
  have hzT : z ∈ T := hT.segment_subset huT hwT hz
  have hv : v ∈ K.simplices.vertices := by
    rw [K.simplices.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨{v, u, w}, ht, by simp⟩
  have hf : ({u, w} : Finset PLPoint) ∈ K.simplices.faces :=
    K.simplices.down_closed ht (by simp) (by simp)
  have hzHull : z ∈ convexHull ℝ (({u, w} : Finset PLPoint) : Set PLPoint) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hz
  have hsep : K.vertexFaceSeparation ≤ dist z v := by
    rw [dist_comm z v]
    exact K.vertexFaceSeparation_le_dist hv hf (by simp [huv.symm, hwv.symm]) hzHull
  have hzRep : z - v = (a / d) • (u - v) + (b / d) • (w - v) := calc
    _ = z - ((a / d) • v + (b / d) • v) := by rw [← add_smul, hweights, one_smul]
    _ = _ := by dsimp [z]; rw [smul_sub, smul_sub]; abel
  have hvec : x - v = d • (z - v) := by
    rw [hrep, hzRep, smul_add, smul_smul, smul_smul, mul_comm d (a / d), mul_comm d (b / d),
      div_mul_cancel₀ _ hd.ne', div_mul_cancel₀ _ hd.ne']
  have hd₁ : d ≤ 1 := by
    have hsmall := Metric.mem_ball.mp (farKite_subset_separation_ball hu hw huw hπ hr hR (interior_subset hx.1))
    rw [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hd, ← dist_eq_norm] at hsmall
    by_contra! h
    have hle := le_mul_of_one_le_left (dist_nonneg (x := z) (y := v)) h.le
    linarith [K.vertexFaceSeparation_pos]
  have hxv : x = v + d • (z - v) := (sub_eq_iff_eq_add.mp hvec).trans (add_comm _ _)
  rw [hxv]
  exact hT.add_smul_sub_mem hvT hzT ⟨hd.le, hd₁⟩

/-- The far arrowheads whose defining edges do not bound a triangle of the complex. -/
def exteriorFarArrowheads (A : FinitePlanarComplex) (r : ℝ) : Set PLPoint :=
  {x | ∃ v u w : PLPoint, ({v, u} : Finset PLPoint) ∈ A.edges ∧
    ({v, w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
    angle (u - v) (w - v) < Real.pi ∧ ({v, u, w} : Finset PLPoint) ∉ A.simplices.faces ∧
    x ∈ farArrowhead v u w r}

/-- The exterior consecutive refinement in Section 4. -/
theorem extendedBody_eq_offset_union_exteriorFarArrowheads
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    extendedBody A.realization r = offset A.realization r ∪ exteriorFarArrowheads A r := by
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ offset A.realization r
    · exact Or.inl h
    · obtain ⟨v, u, w, hu, hw, huw, hc, hπ, hfar⟩ :=
        exists_consecutive_farArrowhead_of_mem_extendedBody_sdiff_offset hAK hr hR ⟨hx, h⟩
      refine Or.inr ⟨v, u, w, hu, hw, huw, hc, hπ, ?_, hfar⟩
      intro ht
      obtain ⟨huF, huC⟩ := (A.mem_edges_iff _).mp hu
      obtain ⟨hwF, hwC⟩ := (A.mem_edges_iff _).mp hw
      have huK := (K.mem_edges_iff _).mpr ⟨hAK huF, huC⟩
      have hwK := (K.mem_edges_iff _).mpr ⟨hAK hwF, hwC⟩
      have htri := farArrowhead_subset_triangle_of_mem_faces huK hwK huw hπ (hAK ht) hr hR hfar
      have hxA := A.convexHull_face_subset_realization _ ht htri
      exact h ((mem_offset_iff_exists_dist_le A.isClosed_realization).mpr ⟨x, hxA, by simpa using hr.le⟩)
  · rintro (hx | ⟨v, u, w, hu, hw, huw, _, hπ, _, hx⟩)
    · exact offset_subset_extendedBody _ _ hx
    · exact farArrowhead_subset_extendedBody hAK hu hw huw hπ hr hR hx

/-- An exterior consecutive far arrowhead lies outside the ordinary offset. -/
theorem disjoint_farArrowhead_offset_of_exterior_consecutive {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u w : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hc : ConsecutiveIncident A v u w) (hπ : angle (u-v) (w-v) < Real.pi)
    (hext : ({v,u,w} : Finset PLPoint) ∉ A.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (farArrowhead v u w r) (offset A.realization r) := by
  obtain ⟨huF, huC⟩ := (A.mem_edges_iff _).mp hu
  obtain ⟨hwF, hwC⟩ := (A.mem_edges_iff _).mp hw
  have huK := (K.mem_edges_iff _).mpr ⟨hAK huF, huC⟩
  have hwK := (K.mem_edges_iff _).mpr ⟨hAK hwF, hwC⟩
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hθ := K.incident_angle_pos huK hwK huw
  have hv : v ∈ K.simplices.vertices := by
    rw [K.simplices.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨{v,u}, hAK huF, by simp⟩
  apply Set.disjoint_left.mpr
  intro x hx hxOffset
  rw [farArrowhead, ite_eq_left hπ] at hx
  obtain ⟨z, hz, hxz⟩ := (mem_offset_iff_exists_dist_le A.isClosed_realization).mp hxOffset
  obtain ⟨s, hs, hz⟩ := (A.mem_realization_iff z).mp hz
  have hxM := Metric.mem_ball.mp (farKite_subset_separation_ball huK hwK huw hπ hr hR (interior_subset hx.1))
  have hzM : dist z v < K.vertexFaceSeparation := by
    have htri := dist_triangle z x v
    rw [dist_comm z x] at htri
    linarith [hR.trans_le K.admissibleRadius_le, K.vertexFaceSeparation_pos]
  have hvs : v ∈ s := by
    by_contra h
    have hsep := K.vertexFaceSeparation_le_dist hv (hAK hs) h hz
    exact (not_le_of_gt hzM) (by simpa only [dist_comm v z] using hsep)
  obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis huv hwv hθ hπ
  obtain ⟨a,b,ha,hb,hrep⟩ := exists_pos_edge_combination_of_mem_interior_farKite huv hwv hr hθ hπ hx.1
  have hxcoords : 0 < B.repr (x-v) 0 ∧ 0 < B.repr (x-v) 1 :=
    (sector_coordinates_pos_iff B (x-v)).mpr ⟨a, b, ha, hb, by rwa [hB₀, hB₁]⟩
  have hOutside : min (B.repr (z-v) 0) (B.repr (z-v) 1) ≤ 0 := by
    by_contra! h
    have hzcoords := lt_min_iff.mp h
    obtain ⟨hus,hws⟩ := sector_endpoints_mem_face_of_pos_coordinates hs hvs hu hw hc hz B hB₀ hB₁
      hzcoords.1 hzcoords.2
    apply hext
    exact A.simplices.down_closed hs
      (Finset.insert_subset_iff.mpr ⟨hvs, Finset.insert_subset_iff.mpr ⟨hus, Finset.singleton_subset_iff.mpr hws⟩⟩)
      ⟨v, Finset.mem_insert_self _ _⟩
  have hxM' : dist x v < K.vertexFaceSeparation := by linarith [K.vertexFaceSeparation_pos]
  obtain ⟨q, hq, hEdge⟩ := segment_meets_incident_edge_of_sector_crossing huK hwK B hB₀ hB₁
    hxcoords.1 hxcoords.2 hOutside hxM' hzM
  have hxq : dist x q ≤ r := by
    have hh := Metric.mem_closedBall.mp (segment_subset_closedBall_left x z hq)
    rw [dist_comm q x] at hh
    exact hh.trans hxz
  rcases hEdge with hEdge | hEdge
  · have hh := lt_infDist_edge_of_mem_interior_farKite hr huv hwv hθ hπ hx.1
    exact (not_le_of_gt hh) ((Metric.infDist_le_dist_of_mem hEdge).trans hxq)
  · have hh := lt_infDist_other_edge_of_mem_interior_farKite hr huv hwv hθ hπ hx.1
    exact (not_le_of_gt hh) ((Metric.infDist_le_dist_of_mem hEdge).trans hxq)

theorem disjoint_exteriorFarArrowheads_offset {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (exteriorFarArrowheads A r) (offset A.realization r) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨v,u,w,hu,hw,huw,hc,hπ,hext,hfar⟩ hoffset
  exact Set.disjoint_left.mp (disjoint_farArrowhead_offset_of_exterior_consecutive hAK hu hw huw hc hπ hext hr hR)
    hfar hoffset

/-- The part of the extended body outside the ordinary offset is exactly
the union of exterior consecutive far arrowheads. -/
theorem extendedBody_sdiff_offset_eq_exteriorFarArrowheads {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    extendedBody A.realization r \ offset A.realization r = exteriorFarArrowheads A r := by
  rw [extendedBody_eq_offset_union_exteriorFarArrowheads hAK hr hR]
  ext x
  constructor
  · rintro ⟨h | h, hn⟩
    · exact (hn h).elim
    · exact h
  · intro h
    exact ⟨Or.inr h, Set.disjoint_left.mp (disjoint_exteriorFarArrowheads_offset hAK hr hR) h⟩

private theorem vertex_separation_le_dist_of_vertices {K : FinitePlanarComplex} {v z : PLPoint}
    (hv : v ∈ K.simplices.vertices) (hz : z ∈ K.simplices.vertices) (hne : v ≠ z) :
    K.vertexFaceSeparation ≤ dist v z :=
  K.vertexFaceSeparation_le_dist hv hz (by simpa only [Finset.mem_singleton] using hne)
    (subset_convexHull ℝ _ (by simp))

/-- Distinct consecutive pairs give disjoint far arrowheads. The pairs are
compared as unordered pairs of incident edges. -/
theorem disjoint_farArrowheads_of_distinct_consecutive_pairs {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u w z g h : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (hg : ({z,g} : Finset PLPoint) ∈ A.edges) (hh : ({z,h} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hgh : g ≠ h) (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A z g h)
    (hπ₁ : angle (u-v) (w-v) < Real.pi) (hπ₂ : angle (g-z) (h-z) < Real.pi)
    (hne : v ≠ z ∨ ({u,w} : Finset PLPoint) ≠ {g,h})
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (farArrowhead v u w r) (farArrowhead z g h r) := by
  have hLift {e : Finset PLPoint} (he : e ∈ A.edges) : e ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp he
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace,hCard⟩
  have hVertex {v u : PLPoint} (he : ({v,u} : Finset PLPoint) ∈ A.edges) : v ∈ K.simplices.vertices := by
    rw [K.simplices.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨{v,u}, hAK ((A.mem_edges_iff _).mp he).1, by simp⟩
  apply Set.disjoint_left.mpr
  intro x h₁ h₂
  rw [farArrowhead, ite_eq_left hπ₁] at h₁
  rw [farArrowhead, ite_eq_left hπ₂] at h₂
  by_cases heq : v = z
  · subst z
    have hθ₁ := K.incident_angle_pos (hLift hu) (hLift hw) huw
    have hθ₂ := K.incident_angle_pos (hLift hg) (hLift hh) hgh
    have huv := FinitePlanarComplex.edge_endpoints_ne hu
    have hwv := FinitePlanarComplex.edge_endpoints_ne hw
    obtain ⟨B,hB₀,hB₁⟩ := exists_incident_basis huv hwv hθ₁ hπ₁
    obtain ⟨a,b,ha,hb,hab⟩ := exists_pos_edge_combination_of_mem_interior_farKite huv hwv hr hθ₁ hπ₁ h₁.1
    have hxcoords : 0 < B.repr (x-v) 0 ∧ 0 < B.repr (x-v) 1 :=
      (sector_coordinates_pos_iff B (x-v)).mpr ⟨a,b,ha,hb,by rwa [hB₀,hB₁]⟩
    obtain ⟨c,d,hc,hd,hcd⟩ := exists_pos_edge_combination_of_mem_interior_farKite
      (FinitePlanarComplex.edge_endpoints_ne hg) (FinitePlanarComplex.edge_endpoints_ne hh) hr hθ₂ hπ₂ h₂.1
    exact (hne.resolve_left (not_not_intro rfl)) (incident_pairs_eq_of_common_open_sector hu hw hg hh
      hc₁ hc₂ B hB₀ hB₁ hxcoords.1 hxcoords.2 hc hd hcd)
  · have hv := hVertex hu
    have hz := hVertex hg
    have hsep := vertex_separation_le_dist_of_vertices hv hz heq
    have hsmall₁ := Metric.mem_ball.mp (farKite_subset_separation_ball (hLift hu) (hLift hw)
      huw hπ₁ hr hR (interior_subset h₁.1))
    have hsmall₂ := Metric.mem_ball.mp (farKite_subset_separation_ball (hLift hg) (hLift hh)
      hgh hπ₂ hr hR (interior_subset h₂.1))
    have htri := dist_triangle v x z
    rw [dist_comm v x] at htri
    linarith

/-- A near arrowhead stays within one quarter of the separation distance of
its base vertex. -/
theorem nearArrowhead_subset_separation_ball {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hπ : angle (u-v) (w-v) < Real.pi)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    nearArrowhead v u w r ⊆ Metric.ball v (K.vertexFaceSeparation / 4) := by
  let Q := arrowheadBisectorPoint v u w r 1
  let θ := angle (u-v) (w-v)
  have hθ := K.incident_angle_pos hu hw huw
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hQ : dist Q v = 1*r*(Real.sin (θ/2))⁻¹ :=
    dist_arrowheadBisectorPoint v u w hr.le (by norm_num) huv hwv hθ hπ
  have hsin : 0 < Real.sin (θ/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [show 0 < θ from hθ])
    (by linarith [show θ < Real.pi from hπ, Real.pi_pos])
  have hrQ : r ≤ dist Q v := by
    rw [hQ, one_mul, ← div_eq_mul_inv]
    apply (le_div_iff₀ hsin).mpr
    exact mul_le_of_le_one_right hr.le (Real.sin_le_one _)
  have hsubset : nearKite v u w r ⊆ Metric.closedBall v (dist Q v) := by
    unfold nearKite
    apply convexHull_min _ (convex_closedBall _ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [Metric.mem_closedBall]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact le_rfl
    · exact (nearKiteShoulder_right_angle hr.le huv hwv hθ hπ).1.trans_le hrQ
    · have h := (nearKiteShoulder_right_angle hr.le hwv huv
        (by rwa [angle_comm]) (by rwa [angle_comm])).1
      exact h.trans_le hrQ
  intro x hx
  rw [nearArrowhead, ite_eq_left hπ] at hx
  have h := Metric.mem_closedBall.mp (hsubset (interior_subset hx.1))
  have hM := K.four_mul_csc_lt_separation hu hw huw hθ hr hR
  rw [hQ] at h
  exact Metric.mem_ball.mpr (by linarith)

/-- Near arrowheads at distinct base vertices are disjoint. -/
theorem disjoint_nearArrowheads_of_ne_vertices {K : FinitePlanarComplex} {v u w z g h : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (hg : ({z,g} : Finset PLPoint) ∈ K.edges) (hh : ({z,h} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hgh : g ≠ h) (hvz : v ≠ z)
    (hπ₁ : angle (u-v) (w-v) < Real.pi) (hπ₂ : angle (g-z) (h-z) < Real.pi)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (nearArrowhead v u w r) (nearArrowhead z g h r) := by
  have hVertex {v u : PLPoint} (he : ({v,u} : Finset PLPoint) ∈ K.edges) : v ∈ K.simplices.vertices := by
    rw [K.simplices.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨{v,u}, ((K.mem_edges_iff _).mp he).1, by simp⟩
  have hsep := vertex_separation_le_dist_of_vertices (hVertex hu) (hVertex hg) hvz
  apply Set.disjoint_left.mpr
  intro x h₁ h₂
  have hsmall₁ := Metric.mem_ball.mp (nearArrowhead_subset_separation_ball hu hw huw hπ₁ hr hR h₁)
  have hsmall₂ := Metric.mem_ball.mp (nearArrowhead_subset_separation_ball hg hh hgh hπ₂ hr hR h₂)
  have htri := dist_triangle v x z
  rw [dist_comm v x] at htri
  linarith [K.vertexFaceSeparation_pos]

end SteinerProof
