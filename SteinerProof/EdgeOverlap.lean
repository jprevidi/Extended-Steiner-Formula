import SteinerProof.ArrowheadChanges
import SteinerProof.EdgeOffsets

/-! Localizing the ordinary offset overlap of a deleted open edge. -/

open Set InnerProductGeometry NormedSpace MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

/-- A disjoint edge and planar face are separated by the vertex-face bound.
A nearest point on a triangle to an exterior point lies on its boundary,
so the edge-edge estimate also handles the triangle case. -/
theorem edge_face_separation_of_disjoint {K : FinitePlanarComplex}
    {v w p q : PLPoint} {s : Finset PLPoint} (he : ({v, w} : Finset PLPoint) ∈ K.edges)
    (hs : s ∈ K.simplices.faces) (hdisj : Disjoint ({v, w} : Finset PLPoint) s)
    (hp : p ∈ segment ℝ v w) (hq : q ∈ convexHull ℝ (s : Set PLPoint)) :
    K.vertexFaceSeparation ≤ dist p q := by
  have heF := ((K.mem_edges_iff _).mp he).1
  have hpHull : p ∈ convexHull ℝ (({v, w} : Finset PLPoint) : Set PLPoint) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hp
  have hpOut : p ∉ convexHull ℝ (s : Set PLPoint) := by
    intro h
    have hh : p ∈ convexHull ℝ (({v, w} : Finset PLPoint) : Set PLPoint) ∩
        convexHull ℝ (s : Set PLPoint) := ⟨hpHull, h⟩
    simpa only [K.simplices.convexHull_inter_convexHull heF hs, ← Finset.coe_inter,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] using hh
  have hCompact := s.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨z, hz, hmin⟩ := hCompact.exists_infDist_eq_dist ⟨q, hq⟩ p
  have hzq : dist p z ≤ dist p q := hmin ▸ Metric.infDist_le_dist_of_mem hq
  have hsmall : ∃ t : Finset PLPoint, t ∈ K.simplices.faces ∧ t ⊆ s ∧ t.card ≤ 2 ∧
      z ∈ convexHull ℝ (t : Set PLPoint) := by
    by_cases h : s.card ≤ 2
    · exact ⟨s, hs, Finset.Subset.refl s, h, hz⟩
    have hdim : s.card ≤ 3 := by
      have h := (K.simplices.indep hs).card_le_finrank_succ
      have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
      simp only [Fintype.card_coe] at h
      rw [finrank_euclideanSpace_fin] at hle
      omega
    have hcard : s.card = 3 := by omega
    have hzOut : z ∉ FinitePlanarComplex.openFace s := by
      rw [FinitePlanarComplex.openFace_eq_interior_of_card_three (K.triangleOfFace s hs hcard)
        (K.range_triangleOfFace s hs hcard)]
      exact FinitePlanarComplex.notMem_interior_of_nearest hpOut hz hmin
    have hzProper : z ∈ ⋃ t : Finset PLPoint, ⋃ (_ : t ⊂ s), convexHull ℝ (t : Set PLPoint) := by
      by_contra h
      exact hzOut ⟨hz, h⟩
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.mp hzProper
    have htNonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨z, hzt⟩)
    have htSub := (Finset.ssubset_iff_subset_ne.mp ht).1
    have htCard := Finset.card_lt_card ht
    exact ⟨t, K.simplices.down_closed hs htSub htNonempty, htSub, by omega, hzt⟩
  obtain ⟨t, ht, htSub, htCard, hzt⟩ := hsmall
  have hd := hdisj.mono_right htSub
  refine le_trans ?_ hzq
  by_cases hTwo : t.card = 2
  · obtain ⟨u, w', _, rfl⟩ := Finset.card_eq_two.mp hTwo
    have hzSeg : z ∈ segment ℝ u w' := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hzt
    exact edge_separation_of_disjoint he ((K.mem_edges_iff _).mpr ⟨ht, hTwo⟩) hd hp hzSeg
  · have hpCard := Finset.card_pos.mpr (K.simplices.nonempty_of_mem_faces ht)
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
    have hzu : z = u := by simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hzt
    have hu : u ∉ ({v, w} : Finset PLPoint) := fun h => Finset.disjoint_left.mp hd h (by simp)
    rw [hzu, dist_comm p u]
    exact K.vertexFaceSeparation_le_dist ht heF hu hpHull

/-- Every contribution to the ordinary offset overlap comes from a face
incident to exactly one endpoint of the deleted edge. -/
theorem exists_endpoint_incident_face_of_mem_offset_inter_eraseEdge {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v w x : PLPoint} (hvw : v ≠ w)
    (he : ({v, w} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx : x ∈ offset (segment ℝ v w) r ∩ offset (A.eraseFacet {v, w} he).realization r) :
    ∃ q : PLPoint, ∃ s : Finset PLPoint, s ∈ (A.eraseFacet {v, w} he).simplices.faces ∧
      q ∈ convexHull ℝ (s : Set PLPoint) ∧ dist x q ≤ r ∧
      ((v ∈ s ∧ w ∉ s) ∨ (w ∈ s ∧ v ∉ s)) := by
  let B := A.eraseFacet {v, w} he
  have hclosed : IsClosed (segment ℝ v w) := by
    rw [← convexHull_pair]
    exact ((finite_singleton w).insert v).isClosed_convexHull ℝ
  obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le hclosed).mp hx.1
  obtain ⟨q, hq, hxq⟩ := (mem_offset_iff_exists_dist_le B.isClosed_realization).mp hx.2
  obtain ⟨s, hs, hq⟩ := (B.mem_realization_iff q).mp hq
  have hsA : s ∈ A.simplices.faces := hs.1
  have htwo : ¬ (v ∈ s ∧ w ∈ s) := by
    rintro ⟨hv, hw⟩
    have hsub := Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hw⟩
    have hEq := (Geometry.SimplicialComplex.mem_facets.mp he).2 s hsA hsub
    exact hs.2 (Set.mem_singleton_iff.mpr hEq.symm)
  have heK : ({v, w} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK (Geometry.SimplicialComplex.mem_facets.mp he).1, Finset.card_pair hvw⟩
  have hone : v ∈ s ∨ w ∈ s := by
    by_contra! h
    have hd : Disjoint ({v, w} : Finset PLPoint) s := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro a (rfl | rfl)
      · exact h.1
      · exact h.2
    have hh := edge_face_separation_of_disjoint heK (hAK hsA) hd hp hq
    linarith [dist_triangle_left p q x, K.six_mul_lt_separation_of_lt_admissibleRadius hR]
  refine ⟨q, s, hs, hq, hxq, ?_⟩
  rcases hone with hv | hw
  · exact Or.inl ⟨hv, fun h => htwo ⟨hv, h⟩⟩
  · exact Or.inr ⟨hw, fun h => htwo ⟨h, hw⟩⟩

/-- A nearby point on an incident face contributes either to the endpoint
disk or to the near kite of a consecutive neighbor on its side of the
deleted edge. -/
theorem mem_closedBall_or_exists_consecutive_nearKite_of_close_incident_face
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u x y : PLPoint} {s : Finset PLPoint} (he : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hs : s ∈ A.simplices.faces) (hv : v ∈ s) (hu : u ∉ s)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx : x ∈ offset (segment ℝ v u) r) (hy : y ∈ convexHull ℝ (s : Set PLPoint)) (hxy : dist x y ≤ r) :
    x ∈ Metric.closedBall v r ∨ ∃ w : PLPoint, ({v, w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧
      ConsecutiveIncident A v u w ∧ angle (u - v) (w - v) < Real.pi ∧ x ∈ nearKite v u w r := by
  by_cases hxBall : x ∈ Metric.closedBall v r
  · exact Or.inl hxBall
  have huv := FinitePlanarComplex.edge_endpoints_ne he
  have hu₀ := sub_ne_zero.mpr huv
  let e := normalize (u - v)
  let c := ⟪e, y - v⟫
  let n := y - v - c • e
  have heNorm : ‖e‖ = 1 := norm_normalize hu₀
  have hen : ⟪e, n⟫ = 0 := by
    dsimp only [n]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, heNorm]
    dsimp only [c]
    ring
  have hne : ⟪n, e⟫ = 0 := (real_inner_comm _ _).trans hen
  have hclosedY : IsClosed (segment ℝ v y) := by
    rw [← convexHull_pair]
    exact ((finite_singleton y).insert v).isClosed_convexHull ℝ
  by_cases hn : n = 0
  · have hdir : y - v = (c / ‖u - v‖) • (u - v) := calc
      _ = c • e := sub_eq_zero.mp hn
      _ = (c / ‖u - v‖) • (‖u - v‖ • e) := by
        rw [smul_smul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu₀)]
      _ = _ := by rw [norm_smul_normalize]
    have hcoef : c / ‖u - v‖ ≤ 0 := by
      by_contra! h
      exact hu (vertex_mem_face_of_ray_mem_convexHull hs hv he hy h
        ((sub_eq_iff_eq_add.mp hdir).trans (add_comm _ _)))
    by_cases hzero : c / ‖u - v‖ = 0
    · have hyv : y = v := by
        rw [hzero, zero_smul] at hdir
        exact sub_eq_zero.mp hdir
      exact (hxBall (Metric.mem_closedBall.mpr (by rwa [hyv] at hxy))).elim
    · have hπ := angle_eq_pi_iff.mpr ⟨hu₀, c / ‖u - v‖, lt_of_le_of_ne hcoef hzero, hdir⟩
      have hyOff := (mem_offset_iff_exists_dist_le hclosedY).mpr ⟨y, right_mem_segment ℝ v y, hxy⟩
      exact (hxBall (inter_edge_offsets_of_angle_eq_pi hπ ▸
        (show x ∈ offset (segment ℝ v u) r ∩ offset (segment ℝ v y) r from ⟨hx, hyOff⟩))).elim
  have hySide : 0 < ⟪n, y - v⟫ := by
    have hEq : y - v = n + c • e := by dsimp only [n]; abel
    rw [hEq, inner_add_right, real_inner_smul_right, hne, mul_zero, add_zero, real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn)
  obtain ⟨z, hzS, hz₀⟩ : ∃ z ∈ s, 0 < ⟪n, z - v⟫ := by
    by_contra! hz
    let f : PLPoint →ᵃ[ℝ] ℝ :=
      (innerSL ℝ n).toLinearMap.toAffineMap.comp ((AffineMap.id ℝ PLPoint) - AffineMap.const ℝ PLPoint v)
    have hF (p : PLPoint) : f p = ⟪n, p - v⟫ := rfl
    have hL : convexHull ℝ (s : Set PLPoint) ⊆ f ⁻¹' Iic 0 := by
      apply convexHull_min _ ((convex_Iic _).affine_preimage _)
      intro p hp
      exact hz p hp
    exact (not_le_of_gt hySide) (show f y ≤ 0 from hL hy)
  have hzv : z ≠ v := by
    intro h
    rw [h, sub_self, inner_zero_right] at hz₀
    exact hz₀.false
  have hzFace : ({v, z} : Finset PLPoint) ∈ A.simplices.faces :=
    A.simplices.down_closed hs (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hzS⟩)
      ⟨v, Finset.mem_insert_self _ _⟩
  have hzEdge : ({v, z} : Finset PLPoint) ∈ A.edges := (A.mem_edges_iff _).mpr ⟨hzFace, Finset.card_pair hzv.symm⟩
  have hzDir : 0 < ⟪n, normalize (z - v)⟫ := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hzv))) hz₀
  obtain ⟨w, hw, hwSide, hc, _⟩ := exists_consecutive_incident_with_half_angle_ratio_ge he hzEdge hen hzDir
  have huw : u ≠ w := by
    intro h
    rw [← h] at hwSide
    exact (not_lt_of_ge hne.le) hwSide
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hθ := A.incident_angle_pos he hw huw
  have hπ : angle (u - v) (w - v) < Real.pi := by
    refine lt_of_le_of_ne (angle_le_pi _ _) fun h => ?_
    obtain ⟨_, a, ha, hrep⟩ := angle_eq_pi_iff.mp h
    rw [hrep, normalize_smul_of_neg ha, inner_neg_right, show ⟪n, normalize (u - v)⟫ = 0 from hne, neg_zero] at hwSide
    exact hwSide.false
  obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis huv hwv hθ hπ
  have hN₀ : ⟪n, u - v⟫ = 0 := calc
    _ = ⟪n, ‖u - v‖ • e⟫ := congrArg (fun p : PLPoint => ⟪n, p⟫) (norm_smul_normalize _).symm
    _ = _ := by rw [real_inner_smul_right, hne, mul_zero]
  have hN₁ : 0 < ⟪n, w - v⟫ := calc
    0 < ‖w - v‖ * ⟪n, normalize (w - v)⟫ := mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwv)) hwSide
    _ = ⟪n, ‖w - v‖ • normalize (w - v)⟫ := (real_inner_smul_right _ _ _).symm
    _ = _ := by rw [norm_smul_normalize]
  have hy₁ : 0 < B.repr (y - v) 1 := by
    have hrep := B.sum_repr (y - v)
    rw [Fin.sum_univ_two, hB₀, hB₁] at hrep
    have hprod : 0 < B.repr (y - v) 1 * ⟪n, w - v⟫ := by
      calc
        0 < ⟪n, y - v⟫ := hySide
        _ = _ := calc
          _ = ⟪n, B.repr (y - v) 0 • (u - v) + B.repr (y - v) 1 • (w - v)⟫ :=
            congrArg (fun p : PLPoint => ⟪n, p⟫) hrep.symm
          _ = _ := by simp only [inner_add_right, real_inner_smul_right, hN₀, mul_zero, zero_add]
    exact pos_of_mul_pos_left hprod hN₁.le
  have hy₀ : B.repr (y - v) 0 ≤ 0 := by
    by_contra! h
    exact hu (sector_endpoints_mem_face_of_pos_coordinates hs hv he hw hc hy B hB₀ hB₁ h hy₁).1
  have hLift {t : Finset PLPoint} (ht : t ∈ A.edges) : t ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp ht
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace, hCard⟩
  have hSide (p : PLPoint) (hp : p ∈ ({y} : Set PLPoint)) : B.repr (p - v) 0 ≤ 0 ∧ 0 ≤ B.repr (p - v) 1 := by
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact ⟨hy₀, hy₁.le⟩
  have hyOff : x ∈ offset ({y} : Set PLPoint) r :=
    (mem_offset_iff_exists_dist_le isClosed_singleton).mpr ⟨y, by simp, hxy⟩
  have hxW := inter_offset_subset_offset_of_intervening_edge (hLift he) (hLift hw) huw hπ hr hR
    B hB₀ hB₁ isClosed_singleton hSide (show x ∈ offset (segment ℝ v u) r ∩ offset ({y} : Set PLPoint) r from ⟨hx, hyOff⟩)
  have hxK : x ∈ Metric.closedBall v r ∪ nearKite v u w r :=
    (inter_edge_offsets_eq_closedBall_union_nearKite (hLift he) (hLift hw) huw hπ hr hR) ▸
      (show x ∈ offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r from ⟨hx, hxW⟩)
  exact Or.inr ⟨w, hw, huw, hc, hπ, hxK.resolve_left hxBall⟩

/-- The consecutive neighbors of the deleted direction at one endpoint. -/
def consecutiveNeighbors (A : FinitePlanarComplex) (v u : PLPoint) : Set PLPoint :=
  {w | ({v, w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
    angle (u - v) (w - v) < Real.pi}

def endpointNearArrowheads (A : FinitePlanarComplex) (v u : PLPoint) (r : ℝ) : Set PLPoint :=
  ⋃ w ∈ consecutiveNeighbors A v u, nearArrowhead v u w r

theorem countable_consecutiveNeighbors (A : FinitePlanarComplex) (v u : PLPoint) :
    (consecutiveNeighbors A v u).Countable := by
  classical
  apply (A.faceFinset.biUnion id).finite_toSet.countable.mono
  intro w hw
  have hE := (A.mem_edges_iff _).mp hw.1
  exact Finset.mem_biUnion.mpr ⟨{v, w}, (A.mem_faceFinset_iff _).mpr hE.1, by simp⟩

theorem measurableSet_endpointNearArrowheads (A : FinitePlanarComplex) (v u : PLPoint) (r : ℝ) :
    MeasurableSet (endpointNearArrowheads A v u r) :=
  MeasurableSet.biUnion (countable_consecutiveNeighbors A v u) (fun w _ => measurableSet_nearArrowhead v u w r)

/-- The ordinary offset overlap is exactly the two endpoint disks and the
closed near kites of the consecutive neighbors. -/
theorem inter_offset_eraseEdge_eq_closedBalls_union_nearKites {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint} (hvu : v ≠ u)
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    offset (segment ℝ v u) r ∩ offset (A.eraseFacet {v, u} he).realization r =
      (Metric.closedBall v r ∪ Metric.closedBall u r) ∪
      ((⋃ w ∈ consecutiveNeighbors A v u, nearKite v u w r) ∪
        (⋃ w ∈ consecutiveNeighbors A u v, nearKite u v w r)) := by
  let B := A.eraseFacet {v, u} he
  have heFace := (Geometry.SimplicialComplex.mem_facets.mp he).1
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges := (A.mem_edges_iff _).mpr ⟨heFace, Finset.card_pair hvu⟩
  have heA' : ({u, v} : Finset PLPoint) ∈ A.edges := by rwa [Finset.pair_comm]
  have hsClosed : IsClosed (segment ℝ v u) := by
    rw [← convexHull_pair]
    exact ((finite_singleton u).insert v).isClosed_convexHull ℝ
  have hVertex (z : PLPoint) (hz : z ∈ ({v, u} : Finset PLPoint)) : z ∈ B.realization := by
    have hface : ({z} : Finset PLPoint) ∈ A.simplices.faces :=
      A.simplices.down_closed heFace (Finset.singleton_subset_iff.mpr hz) (Finset.singleton_nonempty _)
    have hne : ({z} : Finset PLPoint) ≠ {v, u} := by
      intro h
      have hcard := congrArg Finset.card h
      rw [Finset.card_singleton, Finset.card_pair hvu] at hcard
      omega
    exact B.convexHull_face_subset_realization {z} ⟨hface, fun h => hne (Set.mem_singleton_iff.mp h)⟩
      (subset_convexHull ℝ _ (by simp))
  have hDisk (z : PLPoint) (hz : z ∈ ({v, u} : Finset PLPoint)) (hzS : z ∈ segment ℝ v u) :
      Metric.closedBall z r ⊆ offset (segment ℝ v u) r ∩ offset B.realization r := by
    intro x hx
    have hx' := Metric.mem_closedBall.mp hx
    exact ⟨(mem_offset_iff_exists_dist_le hsClosed).mpr ⟨z, hzS, hx'⟩,
      (mem_offset_iff_exists_dist_le B.isClosed_realization).mpr ⟨z, hVertex z hz, hx'⟩⟩
  have hLift {t : Finset PLPoint} (ht : t ∈ A.edges) : t ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp ht
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace, hCard⟩
  have hKite {p q : PLPoint} (hpq : ({p, q} : Finset PLPoint) = {v, u})
      (hpqEdge : ({p, q} : Finset PLPoint) ∈ A.edges) :
      (⋃ w ∈ consecutiveNeighbors A p q, nearKite p q w r) ⊆
        offset (segment ℝ p q) r ∩ offset B.realization r := by
    intro x hx
    obtain ⟨w, ⟨hw, hqw, _, hπ⟩, hx⟩ := Set.mem_iUnion₂.mp hx
    have hne : ({p, w} : Finset PLPoint) ≠ {v, u} := by
      intro h
      have hm : w ∈ ({p, q} : Finset PLPoint) :=
        (h.trans hpq.symm) ▸ (by simp : w ∈ ({p, w} : Finset PLPoint))
      rcases Finset.mem_insert.mp hm with hwp | hwq
      · exact (FinitePlanarComplex.edge_endpoints_ne hw) hwp
      · exact hqw (Finset.mem_singleton.mp hwq).symm
    have hwB := (mem_edges_eraseFacet_iff he).mpr ⟨hw, hne⟩
    have hSeg : segment ℝ p w ⊆ B.realization := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
        B.convexHull_face_subset_realization _ ((B.mem_edges_iff _).mp hwB).1
    have hx' : x ∈ offset (segment ℝ p q) r ∩ offset (segment ℝ p w) r :=
      (inter_edge_offsets_eq_closedBall_union_nearKite (hLift hpqEdge) (hLift hw) hqw hπ hr hR).symm ▸
        (show x ∈ Metric.closedBall p r ∪ nearKite p q w r from Or.inr hx)
    exact ⟨hx'.1, offset_mono hSeg r hx'.2⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, s, hs, hy, hxy, hEnd⟩ := exists_endpoint_incident_face_of_mem_offset_inter_eraseEdge hAK hvu he hr hR hx
    rcases hEnd with ⟨hv, hu⟩ | ⟨hu, hv⟩
    · rcases mem_closedBall_or_exists_consecutive_nearKite_of_close_incident_face hAK heA hs.1 hv hu
        hr hR hx.1 hy hxy with h | ⟨w, hw, hne, hc, hπ, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hne, hc, hπ⟩, h⟩))
    · have hx' : x ∈ offset (segment ℝ u v) r := by
        rw [segment_symm ℝ u v]
        exact hx.1
      rcases mem_closedBall_or_exists_consecutive_nearKite_of_close_incident_face hAK heA' hs.1 hu hv
        hr hR hx' hy hxy with h | ⟨w, hw, hne, hc, hπ, h⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hne, hc, hπ⟩, h⟩))
  · have hKite' := hKite (p := u) (q := v) (Finset.pair_comm u v) heA'
    rw [segment_symm ℝ u v] at hKite'
    exact union_subset (union_subset (hDisk v (by simp) (left_mem_segment ℝ v u))
      (hDisk u (by simp) (right_mem_segment ℝ v u))) (union_subset (hKite rfl heA) hKite')

private theorem endpoint_kite_union_ae_eq_ball_union_nearArrowheads {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ A.edges) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Metric.closedBall v r ∪ (⋃ w ∈ consecutiveNeighbors A v u, nearKite v u w r) =ᵐ[volume]
      Metric.ball v r ∪ endpointNearArrowheads A v u r := by
  classical
  have hLift {t : Finset PLPoint} (ht : t ∈ A.edges) : t ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp ht
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace, hCard⟩
  have hPieces : (⋃ w ∈ consecutiveNeighbors A v u, Metric.closedBall v r ∪ nearKite v u w r) =ᵐ[volume]
      ⋃ w ∈ consecutiveNeighbors A v u, Metric.ball v r ∪ nearArrowhead v u w r := by
    apply ae_eq_set_biUnion (countable_consecutiveNeighbors A v u)
    intro w hw
    obtain ⟨hw, huw, _, hπ⟩ := hw
    rw [← inter_edge_offsets_eq_closedBall_union_nearKite (hLift he) (hLift hw) huw hπ hr hR]
    exact inter_edge_offsets_ae_eq_ball_union_nearArrowhead (hLift he) (hLift hw) huw hπ hr hR
  have hBall : Metric.closedBall v r =ᵐ[volume] Metric.ball v r := by
    apply ae_eq_set.mpr
    refine ⟨?_, ?_⟩
    · rw [Metric.closedBall_sdiff_ball]
      exact Measure.addHaar_sphere volume v r
    · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]
  have hCover (D : Set PLPoint) (f : PLPoint → Set PLPoint) :
      D ∪ (⋃ w ∈ consecutiveNeighbors A v u, f w) =
        D ∪ (⋃ w ∈ consecutiveNeighbors A v u, D ∪ f w) := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | ⟨w, hw, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨w, hw, Or.inr hx⟩
    · rintro (hx | ⟨w, hw, hx | hx⟩)
      · exact Or.inl hx
      · exact Or.inl hx
      · exact Or.inr ⟨w, hw, hx⟩
  rw [endpointNearArrowheads, hCover (Metric.closedBall v r), hCover (Metric.ball v r)]
  exact ae_eq_set_union hBall hPieces

/-- The overlap formula of Section 5, up to sets of area zero. -/
theorem inter_offset_eraseEdge_ae_eq_balls_union_nearArrowheads {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint} (hvu : v ≠ u)
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    offset (segment ℝ v u) r ∩ offset (A.eraseFacet {v, u} he).realization r =ᵐ[volume]
      (Metric.ball v r ∪ Metric.ball u r) ∪ (endpointNearArrowheads A v u r ∪ endpointNearArrowheads A u v r) := by
  have heFace := (Geometry.SimplicialComplex.mem_facets.mp he).1
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges := (A.mem_edges_iff _).mpr ⟨heFace, Finset.card_pair hvu⟩
  have heA' : ({u, v} : Finset PLPoint) ∈ A.edges := by rwa [Finset.pair_comm]
  rw [inter_offset_eraseEdge_eq_closedBalls_union_nearKites hAK hvu he hr hR]
  have h₁ := endpoint_kite_union_ae_eq_ball_union_nearArrowheads hAK heA hr hR
  have h₂ := endpoint_kite_union_ae_eq_ball_union_nearArrowheads hAK heA' hr hR
  convert ae_eq_set_union h₁ h₂ using 1 <;> ext x <;> simp only [Set.mem_union] <;> tauto

/-- The disk and near pieces at each endpoint give the ordinary overlap
area, and the contributions at distinct endpoints add. -/
theorem volume_inter_offset_eraseEdge_eq_endpoint_areas {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint} (hvu : v ≠ u)
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (offset (segment ℝ v u) r ∩ offset (A.eraseFacet {v, u} he).realization r) =
      (volume (Metric.ball v r) + volume (endpointNearArrowheads A v u r)) +
      (volume (Metric.ball u r) + volume (endpointNearArrowheads A u v r)) := by
  let R (p q : PLPoint) := Metric.ball p r ∪ endpointNearArrowheads A p q r
  have hLift {t : Finset PLPoint} (ht : t ∈ A.edges) : t ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp ht
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace, hCard⟩
  have heFace := (Geometry.SimplicialComplex.mem_facets.mp he).1
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges := (A.mem_edges_iff _).mpr ⟨heFace, Finset.card_pair hvu⟩
  have heA' : ({u, v} : Finset PLPoint) ∈ A.edges := by rwa [Finset.pair_comm]
  have hrSmall : r < K.vertexFaceSeparation / 4 := by
    linarith [hR.trans_le K.admissibleRadius_le, K.vertexFaceSeparation_pos]
  have hSub {p q : PLPoint} (hpq : ({p, q} : Finset PLPoint) ∈ A.edges) :
      R p q ⊆ Metric.ball p (K.vertexFaceSeparation / 4) := by
    rintro x (hx | hx)
    · exact Metric.ball_subset_ball hrSmall.le hx
    · obtain ⟨w, ⟨hw, hn, _, hπ⟩, hx⟩ := Set.mem_iUnion₂.mp hx
      exact nearArrowhead_subset_separation_ball (hLift hpq) (hLift hw) hn hπ hr hR hx
  have hsep := FinitePlanarComplex.vertexFaceSeparation_le_edge_dist (hLift heA)
  have hdis : Disjoint (R v u) (R u v) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have h₁ := Metric.mem_ball.mp (hSub heA hx)
    have h₂ := Metric.mem_ball.mp (hSub heA' hx')
    linarith [dist_triangle_left v u x, K.vertexFaceSeparation_pos]
  have hDisBall (p q : PLPoint) : Disjoint (Metric.ball p r) (endpointNearArrowheads A p q r) := by
    apply Set.disjoint_left.mpr
    intro x hb hx
    obtain ⟨w, ⟨_, _, _, hπ⟩, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [nearArrowhead, ite_eq_left hπ] at hx
    exact hx.2 hb
  have hEq := inter_offset_eraseEdge_ae_eq_balls_union_nearArrowheads hAK hvu he hr hR
  have hEq' : (Metric.ball v r ∪ Metric.ball u r) ∪
      (endpointNearArrowheads A v u r ∪ endpointNearArrowheads A u v r) = R v u ∪ R u v := by
    ext x
    simp only [R, Set.mem_union]
    tauto
  rw [measure_congr hEq, hEq', measure_union hdis
    (Metric.isOpen_ball.measurableSet.union (measurableSet_endpointNearArrowheads A u v r))]
  dsimp only [R]
  rw [measure_union' (hDisBall v u) Metric.isOpen_ball.measurableSet,
    measure_union' (hDisBall u v) Metric.isOpen_ball.measurableSet]

end SteinerProof
