import SteinerProof.EndpointArrowheads
import SteinerProof.RealizationBridge
import SteinerProof.SegmentOffset
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Area accounting for deletion of an isolated open edge, as in Section 5. -/

open MeasureTheory Set
open InnerProductGeometry

noncomputable section

namespace FinitePlanarComplex

open SteinerProof

/-- The ordinary offset and the exterior arrowheads contribute additively to
the extended area. -/
theorem extendedArea_eq_offset_add_exteriorFarArrowheads {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {r : ℝ} (hr : 0 < r)
    (hR : r < K.admissibleRadius) :
    A.extendedArea r = (volume (offset A.realization r)).toReal +
      (volume (exteriorFarArrowheads A r)).toReal := by
  have hUnion := extendedBody_eq_offset_union_exteriorFarArrowheads hAK hr hR
  have hDisjoint := (disjoint_exteriorFarArrowheads_offset hAK hr hR).symm
  have hFinite := A.volume_extendedBody_lt_top r hr.le
  have hOffset := ((measure_mono (offset_subset_extendedBody A.realization r)).trans_lt hFinite).ne
  have hExt : exteriorFarArrowheads A r ⊆ extendedBody A.realization r := by
    rw [hUnion]
    exact subset_union_right
  have hArrowheads := ((measure_mono hExt).trans_lt hFinite).ne
  unfold extendedArea
  rw [hUnion, measure_union' hDisjoint (measurableSet_offset A.realization r),
    ENNReal.toReal_add hOffset hArrowheads]

/-- For a facet deletion, the two terms to compare are the ordinary offset
areas and the exterior arrowhead areas. -/
theorem volume_extendedBody_sdiff_eraseFacet_eq_offset_add_exterior
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {s : Finset PLPoint} (hs : s ∈ A.simplices.facets) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    let B := A.eraseFacet s hs
    (volume (extendedBody A.realization r \ extendedBody B.realization r)).toReal =
      (volume (offset A.realization r)).toReal - (volume (offset B.realization r)).toReal +
      ((volume (exteriorFarArrowheads A r)).toReal - (volume (exteriorFarArrowheads B r)).toReal) := by
  let B := A.eraseFacet s hs
  have hBA : B.simplices.faces ⊆ A.simplices.faces := fun _ h => h.1
  change (volume (extendedBody A.realization r \ extendedBody B.realization r)).toReal = _
  rw [← extendedArea_sub_of_realization_subset (realization_mono hBA) r hr.le,
    extendedArea_eq_offset_add_exteriorFarArrowheads hAK hr hR,
    extendedArea_eq_offset_add_exteriorFarArrowheads (hBA.trans hAK) hr hR]
  ring

/-- The area decrement splits into the ordinary offset change, the removed
far-arrowhead area, and the area of the newly consecutive pairs. -/
theorem volume_extendedBody_sdiff_eraseEdge_eq_offset_add_removed_sub_created
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {s : Finset PLPoint} (hs : s ∈ A.simplices.facets) (hs₂ : s.card = 2) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    let B := A.eraseFacet s hs
    (volume (extendedBody A.realization r \ extendedBody B.realization r)).toReal =
      (volume (offset A.realization r)).toReal - (volume (offset B.realization r)).toReal +
      (volume (removedFarArrowheads A s r)).toReal - (volume (createdFarArrowheads A s hs r)).toReal := by
  let B := A.eraseFacet s hs
  have hBK : B.simplices.faces ⊆ K.simplices.faces := fun _ h => hAK h.1
  have hExtFinite {C : FinitePlanarComplex} (hCK : C.simplices.faces ⊆ K.simplices.faces) :
      volume (exteriorFarArrowheads C r) < ⊤ := by
    have hsub : exteriorFarArrowheads C r ⊆ extendedBody C.realization r := by
      rw [extendedBody_eq_offset_union_exteriorFarArrowheads hCK hr hR]
      exact subset_union_right
    exact (measure_mono hsub).trans_lt (C.volume_extendedBody_lt_top r hr.le)
  have hOld := hExtFinite hAK
  have hRemoved : volume (removedFarArrowheads A s r) ≤ volume (exteriorFarArrowheads A r) :=
    measure_mono removedFarArrowheads_subset
  have hSurv : volume (exteriorFarArrowheads A r \ removedFarArrowheads A s r) ≠ ⊤ :=
    ((measure_mono sdiff_subset).trans_lt hOld).ne
  have hNew : volume (createdFarArrowheads A s hs r) ≠ ⊤ :=
    ((measure_mono createdFarArrowheads_subset).trans_lt (hExtFinite hBK)).ne
  dsimp only
  rw [volume_extendedBody_sdiff_eraseFacet_eq_offset_add_exterior hAK hs hr hR]
  rw [exteriorFarArrowheads_eraseEdge_eq hAK hs hs₂ hr hR,
    measure_union (disjoint_surviving_createdFarArrowheads hAK hs hr hR)
      (measurableSet_createdFarArrowheads A s hs r), ENNReal.toReal_add hSurv hNew,
    measure_sdiff removedFarArrowheads_subset (measurableSet_removedFarArrowheads A s r).nullMeasurableSet
      (hRemoved.trans_lt hOld).ne, ENNReal.toReal_sub_of_le hRemoved hOld.ne]
  ring

end FinitePlanarComplex

namespace SteinerProof

private theorem disjoint_farArrowheads_of_endpoint_neighbors {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w z : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ A.edges) (hz : ({v,z} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z)
    (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A v u z)
    (hπ₁ : angle (u-v) (w-v) < Real.pi) (hπ₂ : angle (u-v) (z-v) < Real.pi)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (farArrowhead v u w r) (farArrowhead v u z r) := by
  have hpair : ({u,w} : Finset PLPoint) ≠ {u,z} := by
    intro h
    have hm : w ∈ ({u,z} : Finset PLPoint) := h ▸ (by simp : w ∈ ({u,w} : Finset PLPoint))
    exact hwz (Finset.mem_singleton.mp ((Finset.mem_insert.mp hm).resolve_left huw.symm))
  exact disjoint_farArrowheads_of_distinct_consecutive_pairs hAK hu hw hu hz
    huw huz hc₁ hc₂ hπ₁ hπ₂ (Or.inr hpair) hr hR

/-- Endpoint area cancellation in the non-reflex and straight cases. When
the neighboring angle is strictly less than pi, the deleted direction is
a positive combination of the two neighboring directions. -/
theorem volume_union_farArrowheads_eq_add_of_intervening_edge {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w z : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ A.edges) (hz : ({v,z} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z)
    (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A v u z)
    (hπ₁ : angle (u-v) (w-v) < Real.pi) (hπ₂ : angle (u-v) (z-v) < Real.pi)
    (hBetween : angle (w-v) (z-v) < Real.pi →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ u-v = a • (w-v) + b • (z-v))
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (farArrowhead v u w r ∪ farArrowhead v u z r) =
      volume (nearArrowhead v u w r ∪ nearArrowhead v u z r) + volume (farArrowhead v w z r) := by
  have hLift {e : Finset PLPoint} (he : e ∈ A.edges) : e ∈ K.edges := by
    obtain ⟨hFace,hCard⟩ := (A.mem_edges_iff _).mp he
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace,hCard⟩
  have hDisjoint := disjoint_farArrowheads_of_endpoint_neighbors hAK hu hw hz huw huz hwz hc₁ hc₂ hπ₁ hπ₂ hr hR
  have hOverlap : volume (nearArrowhead v u w r ∩ nearArrowhead v u z r) =
      volume (farArrowhead v w z r) := by
    by_cases hπ : angle (w-v) (z-v) < Real.pi
    · obtain ⟨a,b,ha,hb,hrep⟩ := hBetween hπ
      rw [measure_congr (nearArrowhead_inter_ae_eq_of_intervening_edge (hLift hu) (hLift hw) (hLift hz)
        huw huz hwz hπ₁ hπ₂ hπ ha hb hrep hr hR), volume_nearArrowhead_eq_farArrowhead]
    · have hStraight := le_antisymm (angle_le_pi (w-v) (z-v)) (le_of_not_gt hπ)
      rw [farArrowhead, ite_eq_right hπ, measure_empty]
      apply measure_eq_zero_iff_ae_notMem.mpr
      have hCircle : ∀ᵐ x ∂(volume : Measure PLPoint), x ∉ Metric.sphere v r :=
        ae_iff.mpr (by simpa only [not_not, Set.setOf_mem_eq] using Measure.addHaar_sphere volume v r)
      filter_upwards [hCircle, inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead (hLift hu) (hLift hw) huw hπ₁ hr hR,
        inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead (hLift hu) (hLift hz) huz hπ₂ hr hR] with x hx h₁ h₂
      rintro ⟨hn₁,hn₂⟩
      obtain ⟨⟨_,hW⟩,hOut⟩ := h₁.mpr hn₁
      obtain ⟨⟨_,hZ⟩,_⟩ := h₂.mpr hn₂
      have hBall : x ∈ Metric.closedBall v r :=
        (inter_edge_offsets_of_angle_eq_pi hStraight) ▸ (show x ∈
          offset (segment ℝ v w) r ∩ offset (segment ℝ v z) r from ⟨hW,hZ⟩)
      exact hx (Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hBall)
        (le_of_not_gt fun hh => hOut (Metric.mem_ball.mpr hh))))
  rw [measure_union hDisjoint (measurableSet_farArrowhead v u z r),
    ← volume_nearArrowhead_eq_farArrowhead v u w r, ← volume_nearArrowhead_eq_farArrowhead v u z r,
    ← hOverlap]
  exact (measure_union_add_inter (nearArrowhead v u w r) (measurableSet_nearArrowhead v u z r)).symm

/-- Endpoint area cancellation when the deleted edge is in the reflex angle. -/
theorem volume_union_farArrowheads_eq_near_union_of_reflex {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w z : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ A.edges) (hz : ({v,z} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z)
    (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A v u z)
    (hπ₁ : angle (u - v) (w - v) < Real.pi) (hπ₂ : angle (u - v) (z - v) < Real.pi)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hReflex : -(u - v) = a • (w - v) + b • (z - v))
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (farArrowhead v u w r ∪ farArrowhead v u z r) =
      volume (nearArrowhead v u w r ∪ nearArrowhead v u z r) := by
  have hFar := disjoint_farArrowheads_of_endpoint_neighbors hAK hu hw hz huw huz hwz hc₁ hc₂ hπ₁ hπ₂ hr hR
  have hNear := disjoint_nearArrowheads_of_reflex (FinitePlanarComplex.edge_endpoints_ne hu)
    (FinitePlanarComplex.edge_endpoints_ne hw) (FinitePlanarComplex.edge_endpoints_ne hz) hr
    (A.incident_angle_pos hu hw huw) (A.incident_angle_pos hu hz huz) hπ₁ hπ₂ ha hb hReflex
  rw [measure_union hFar (measurableSet_farArrowhead v u z r),
    measure_union hNear (measurableSet_nearArrowhead v u z r),
    volume_nearArrowhead_eq_farArrowhead, volume_nearArrowhead_eq_farArrowhead]

/-- At each endpoint, the removed far area equals the near overlap and
the far area of the newly consecutive pair. -/
theorem volume_endpointRemoved_eq_near_add_created {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (endpointRemovedFarArrowheads A v u r) =
      volume (endpointNearArrowheads A v u r) + volume (endpointCreatedFarArrowheads A v u r) := by
  classical
  rcases consecutiveNeighbors_eq_empty_singleton_or_pair hu with hN | ⟨w, hN⟩ | ⟨w, z, hwz, hN⟩
  · rw [endpointCreated_eq_empty_of_subsingleton (by rw [hN]; exact Set.subsingleton_empty)]
    simp [endpointRemovedFarArrowheads, endpointNearArrowheads, hN]
  · rw [endpointCreated_eq_empty_of_subsingleton (by rw [hN]; exact Set.subsingleton_singleton)]
    simp [endpointRemovedFarArrowheads, endpointNearArrowheads, hN, volume_nearArrowhead_eq_farArrowhead]
  have hw : w ∈ consecutiveNeighbors A v u := by rw [hN]; simp
  have hz : z ∈ consecutiveNeighbors A v u := by rw [hN]; simp
  rw [endpointRemovedFarArrowheads, endpointNearArrowheads, hN, Set.biUnion_pair, Set.biUnion_pair,
    endpointCreated_eq_of_neighbor_pair hwz hN]
  have hArea := volume_union_farArrowheads_eq_add_of_intervening_edge hAK hu hw.1 hz.1
    hw.2.1 hz.2.1 hwz hw.2.2.1 hz.2.2.1 hw.2.2.2 hz.2.2.2
  rcases consecutiveNeighbors_direction_cases hu hw hz hwz.symm with hπ | ⟨hπ, hPos | hNeg⟩
  · have hnot : ¬ angle (w - v) (z - v) < Real.pi := by rw [hπ]; exact lt_irrefl _
    have hEmpty : farArrowhead v w z r = ∅ := if_neg hnot
    rw [if_neg (fun h => hnot h.1), ← hEmpty]
    exact hArea (fun h => (hnot h).elim) hr hR
  · rw [if_pos ⟨hπ, hPos⟩]
    exact hArea (fun _ => hPos) hr hR
  · obtain ⟨a, b, ha, hb, hReflex⟩ := hNeg
    have hnot : ¬ ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ u - v = c • (w - v) + d • (z - v) := by
      intro h
      obtain ⟨C, hC₀, hC₁⟩ := exists_incident_basis (FinitePlanarComplex.edge_endpoints_ne hw.1)
        (FinitePlanarComplex.edge_endpoints_ne hz.1) (A.incident_angle_pos hw.1 hz.1 hwz) hπ
      obtain ⟨c, d, hc, hd, hrep⟩ := h
      have hPlus := (sector_coordinates_pos_iff C (u - v)).mpr ⟨c, d, hc, hd, by rwa [hC₀, hC₁]⟩
      have hMinus := (sector_coordinates_pos_iff C (-(u - v))).mpr ⟨a, b, ha, hb, by rwa [hC₀, hC₁]⟩
      rw [map_neg, Finsupp.neg_apply] at hMinus
      exact (not_lt_of_ge hPlus.1.le) (neg_pos.mp hMinus.1)
    rw [if_neg (fun h => hnot h.2), measure_empty, add_zero]
    exact volume_union_farArrowheads_eq_near_union_of_reflex hAK hu hw.1 hz.1 hw.2.1 hz.2.1 hwz
      hw.2.2.1 hz.2.2.1 hw.2.2.2 hz.2.2.2 ha hb hReflex hr hR

/-- The two endpoint cancellations account for all removed and newly
created arrowheads. -/
theorem volume_removed_eq_endpointNear_add_created {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint} (hvu : v ≠ u)
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (removedFarArrowheads A {v, u} r) =
      volume (endpointNearArrowheads A v u r) + volume (endpointNearArrowheads A u v r) +
      volume (createdFarArrowheads A {v, u} he r) := by
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges :=
    (A.mem_edges_iff _).mpr ⟨(Geometry.SimplicialComplex.mem_facets.mp he).1, Finset.card_pair hvu⟩
  have heA' : ({u, v} : Finset PLPoint) ∈ A.edges := by rwa [Finset.pair_comm]
  obtain ⟨hRem, hNew⟩ := volumes_changedFarArrowheads_eq_endpoint_sums hAK hvu he hr hR
  rw [hRem, hNew, volume_endpointRemoved_eq_near_add_created hAK heA hr hR,
    volume_endpointRemoved_eq_near_add_created hAK heA' hr hR]
  ac_rfl

end SteinerProof

namespace FinitePlanarComplex

open SteinerProof

/-- After the endpoint cancellations, the area lost on deleting the open
edge is the area of its closed segment offset less the two endpoint disks. -/
theorem area_extendedBody_sdiff_eraseEdge_eq_segment_offset_sub_disks
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u : PLPoint} (hvu : v ≠ u) (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    (volume (extendedBody A.realization r \ extendedBody (A.eraseFacet {v, u} he).realization r)).toReal =
      (volume (offset (segment ℝ v u) r)).toReal - 2 * (Real.pi * r ^ 2) := by
  let B := A.eraseFacet {v, u} he
  let U := offset A.realization r
  let V := offset B.realization r
  let E := offset (segment ℝ v u) r
  let D := volume (Metric.ball v r) + volume (Metric.ball u r)
  let L := volume (endpointNearArrowheads A v u r) + volume (endpointNearArrowheads A u v r)
  let N := volume (createdFarArrowheads A {v, u} he r)
  have hBK : B.simplices.faces ⊆ K.simplices.faces := fun _ h => hAK h.1
  have hReal := A.realization_eq_eraseFacet_union_convexHull {v, u} he
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at hReal
  have hClosed : IsClosed (segment ℝ v u) := by
    rw [← convexHull_pair]
    exact ((finite_singleton u).insert v).isClosed_convexHull ℝ
  have hUnion : U = V ∪ E := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le A.isClosed_realization).mp hx
      rw [hReal] at hp
      rcases hp with hp | hp
      · exact Or.inl ((mem_offset_iff_exists_dist_le B.isClosed_realization).mpr ⟨p, hp, hxp⟩)
      · exact Or.inr ((mem_offset_iff_exists_dist_le hClosed).mpr ⟨p, hp, hxp⟩)
    · rintro (hx | hx)
      · exact offset_mono (by rw [hReal]; exact subset_union_left) r hx
      · exact offset_mono (by rw [hReal]; exact subset_union_right) r hx
  have hInt : volume (E ∩ V) = D + L := by
    dsimp only [E, V, B, D, L]
    rw [volume_inter_offset_eraseEdge_eq_endpoint_areas hAK hvu he hr hR]
    ac_rfl
  have hU : volume U < ⊤ :=
    (measure_mono (offset_subset_extendedBody A.realization r)).trans_lt (A.volume_extendedBody_lt_top r hr.le)
  have hV : volume V < ⊤ :=
    (measure_mono (offset_subset_extendedBody B.realization r)).trans_lt (B.volume_extendedBody_lt_top r hr.le)
  have hESub : E ⊆ U := by rw [hUnion]; exact subset_union_right
  have hE : volume E < ⊤ := (measure_mono hESub).trans_lt hU
  have hDL : D + L < ⊤ := by
    rw [← hInt]
    exact (measure_mono inter_subset_left).trans_lt hE
  obtain ⟨hD, hL⟩ := ENNReal.add_lt_top.mp hDL
  have hN : N < ⊤ := by
    have hsub : exteriorFarArrowheads B r ⊆ extendedBody B.realization r := by
      rw [extendedBody_eq_offset_union_exteriorFarArrowheads hBK hr hR]
      exact subset_union_right
    exact (measure_mono (createdFarArrowheads_subset.trans hsub)).trans_lt (B.volume_extendedBody_lt_top r hr.le)
  have hSum : volume U + (D + L) = volume E + volume V := by
    have h := measure_union_add_inter (μ := volume) E (measurableSet_offset B.realization r)
    change volume (E ∪ V) + volume (E ∩ V) = _ at h
    rwa [union_comm E V, ← hUnion, hInt] at h
  have hArea := congrArg ENNReal.toReal hSum
  rw [ENNReal.toReal_add hU.ne hDL.ne, ENNReal.toReal_add hD.ne hL.ne,
    ENNReal.toReal_add hE.ne hV.ne] at hArea
  have hDisk (p : PLPoint) : (volume (Metric.ball p r)).toReal = Real.pi * r ^ 2 := by
    rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_pos.le, mul_comm]
  have hAreaD : D.toReal = 2 * (Real.pi * r ^ 2) := by
    dsimp only [D]
    rw [ENNReal.toReal_add measure_ball_lt_top.ne measure_ball_lt_top.ne, hDisk, hDisk]
    ring
  have hCancel : volume (removedFarArrowheads A {v, u} r) = L + N :=
    volume_removed_eq_endpointNear_add_created hAK hvu he hr hR
  rw [volume_extendedBody_sdiff_eraseEdge_eq_offset_add_removed_sub_created hAK he (Finset.card_pair hvu) hr hR,
    hCancel, ENNReal.toReal_add hL.ne hN.ne, ← hAreaD]
  change (volume U).toReal - (volume V).toReal + (L.toReal + N.toReal) - N.toReal = (volume E).toReal - D.toReal
  linarith only [hArea]

/-- The isolated open-edge deletion area in Section 5. -/
theorem area_extendedBody_sdiff_eraseEdge
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u : PLPoint} (hvu : v ≠ u) (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    (volume (extendedBody A.realization r \ extendedBody (A.eraseFacet {v, u} he).realization r)).toReal =
      2 * r * dist v u - Real.pi * r ^ 2 := by
  rw [area_extendedBody_sdiff_eraseEdge_eq_segment_offset_sub_disks hAK hvu he hr hR,
    volume_offset_segment_toReal hvu hr.le]
  ring

end FinitePlanarComplex
