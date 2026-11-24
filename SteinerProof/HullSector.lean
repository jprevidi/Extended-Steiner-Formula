import SteinerProof.HullInterior
import SteinerProof.ArrowheadSectors

/-! Consecutive incident edges bounding a gap in a planar hull. -/

open Set

noncomputable section

namespace FinitePlanarComplex

private theorem vertexGapPath_meets_ray {v p n : PLPoint} {a b c d : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 0) (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hd : 0 < d) :
    ∃ t ∈ Ioo a b, ∃ k : ℝ, 0 < k ∧
      vertexGapPath v p n t - v = k • (c • (vertexGapPath v p n a - v) + d • (vertexGapPath v p n b - v)) := by
  let s := c * a + d * b
  let h := c * (1 + a) + d * (1 - b)
  have hpos : 0 < h := add_pos (mul_pos hc (by linarith [ha.1])) (mul_pos hd (sub_pos.mpr hb.2))
  let L := h + |s|
  have hL : 0 < L := add_pos_of_pos_of_nonneg hpos (abs_nonneg s)
  let t := s / L
  have hcross : 0 < b * (1 + a) - a * (1 - b) := sub_pos.mpr
    ((mul_neg_of_neg_of_pos ha.2 (sub_pos.mpr hb.2)).trans (mul_pos hb.1 (by linarith [ha.1])))
  have ht : t ∈ Ioo a b := by
    rcases le_total 0 s with hs | hs
    · refine ⟨ha.2.trans_le (div_nonneg hs hL.le), (div_lt_iff₀ hL).mpr ?_⟩
      change s < b * (h + |s|)
      rw [abs_of_nonneg hs]
      have hcross' := mul_pos hc hcross
      dsimp only [s, h]
      nlinarith only [hcross']
    · refine ⟨(lt_div_iff₀ hL).mpr ?_, (div_nonpos_of_nonpos_of_nonneg hs hL.le).trans_lt hb.1⟩
      change a * (h + |s|) < s
      rw [abs_of_nonpos hs]
      have hcross' := mul_pos hd hcross
      dsimp only [s, h]
      nlinarith only [hcross']
  refine ⟨t, ht, L⁻¹, inv_pos.mpr hL, ?_⟩
  have hr : 1 - |t| = L⁻¹ * h := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hL, ← div_eq_inv_mul]
    apply (eq_div_iff hL.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hL.ne']
    dsimp only [L]
    ring
  simp only [vertexGapPath, add_sub_cancel_left, hr, abs_of_neg ha.2, abs_of_pos hb.1]
  dsimp only [t, s, h]
  rw [div_eq_inv_mul]
  module

private theorem edgeDirection_eq_of_mem_openSegment {v u x : PLPoint}
    (hx : x ∈ openSegment ℝ v u) : ∃ a : ℝ, 0 < a ∧ x - v = a • (u - v) := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha.1, by rw [AffineMap.lineMap_apply_module', add_sub_cancel_right]⟩

private theorem mem_segment_of_near_pos_edgeDirection {K : FinitePlanarComplex} {v u x : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ K.edges) (hx : dist x v < K.vertexFaceSeparation)
    {a : ℝ} (ha : 0 < a) (hVec : x-v = a • (u-v)) : x ∈ segment ℝ v u := by
  have hD : K.vertexFaceSeparation ≤ dist u v := dist_comm v u ▸ K.vertexFaceSeparation_le_edge_dist he
  have hPos := K.vertexFaceSeparation_pos.trans_le hD
  have hDist : dist x v = a * dist u v := by
    rw [dist_eq_norm, hVec, norm_smul, Real.norm_eq_abs, abs_of_pos ha, ← dist_eq_norm]
  have ha₁ : a ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hPos).mp
    rw [one_mul, ← hDist]
    exact hx.le.trans hD
  rw [segment_eq_image_lineMap]
  exact ⟨a, ⟨ha.le, ha₁⟩, by rw [AffineMap.lineMap_apply_module', ← hVec, sub_add_cancel]⟩

private theorem consecutiveIncident_of_gap_interval {K : FinitePlanarComplex} {v u w p n : PLPoint} {a b : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 0) (hb : b ∈ Ioo (0 : ℝ) 1)
    (haOpen : vertexGapPath v p n a ∈ openSegment ℝ v u) (hbOpen : vertexGapPath v p n b ∈ openSegment ℝ v w)
    (hGap : ∀ t ∈ Ioo a b, vertexGapPath v p n t ∉ K.realization)
    (hBound : ∀ t ∈ Icc (-1 : ℝ) 1, dist (vertexGapPath v p n t) v < K.vertexFaceSeparation) :
    SteinerProof.ConsecutiveIncident K v u w := by
  obtain ⟨a', ha', hVa⟩ := edgeDirection_eq_of_mem_openSegment haOpen
  obtain ⟨b', hb', hVb⟩ := edgeDirection_eq_of_mem_openSegment hbOpen
  rintro z hz _ _ ⟨c, d, hc, hd, hDir⟩
  obtain ⟨t, ht, k, hk, hVec⟩ := vertexGapPath_meets_ray (v := v) (p := p) (n := n) ha hb
    (div_pos hc ha') (div_pos hd hb')
  rw [hVa, hVb, smul_smul, smul_smul, div_mul_cancel₀ _ ha'.ne', div_mul_cancel₀ _ hb'.ne', ← hDir] at hVec
  have htIcc : t ∈ Icc (-1 : ℝ) 1 := ⟨ha.1.le.trans ht.1.le, ht.2.le.trans hb.2.le⟩
  have htSeg := mem_segment_of_near_pos_edgeDirection hz (hBound t htIcc) hk hVec
  apply hGap t ht
  apply K.convexHull_face_subset_realization {v, z} ((K.mem_edges_iff _).mp hz).1
  simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using htSeg

private theorem positive_edge_combination_of_gap_interval {v u w p n : PLPoint} {a b : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 0) (hb : b ∈ Ioo (0 : ℝ) 1)
    (haOpen : vertexGapPath v p n a ∈ openSegment ℝ v u) (hbOpen : vertexGapPath v p n b ∈ openSegment ℝ v w) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ p - v = c • (u - v) + d • (w - v) := by
  obtain ⟨a', ha', hVa⟩ := edgeDirection_eq_of_mem_openSegment haOpen
  obtain ⟨b', hb', hVb⟩ := edgeDirection_eq_of_mem_openSegment hbOpen
  let L := b * (1 + a) - a * (1 - b)
  have hL : 0 < L := sub_pos.mpr
    ((mul_neg_of_neg_of_pos ha.2 (sub_pos.mpr hb.2)).trans (mul_pos hb.1 (by linarith [ha.1])))
  let c := b / L
  let d := -a / L
  have hc : 0 < c := div_pos hb.1 hL
  have hd : 0 < d := div_pos (neg_pos.mpr ha.2) hL
  have hSum : c * (1 + a) + d * (1 - b) = 1 := by
    dsimp only [c, d]
    field_simp
    dsimp only [L]
    ring
  have hZero : c*a + d*b = 0 := by
    dsimp only [c, d]
    field_simp
    ring
  refine ⟨c*a', d*b', mul_pos hc ha', mul_pos hd hb', ?_⟩
  calc
    _ = (c * (1 + a) + d * (1 - b)) • (p - v) + (c*a + d*b) • n := by rw [hSum, hZero, one_smul, zero_smul, add_zero]
    _ = c • (vertexGapPath v p n a - v) + d • (vertexGapPath v p n b - v) := by
      simp only [vertexGapPath, add_sub_cancel_left, abs_of_neg ha.2, abs_of_pos hb.1, sub_neg_eq_add]
      module
    _ = _ := by rw [hVa, hVb, smul_smul, smul_smul]

private theorem independent_edgeDirections_of_gap_interval {v u w p n : PLPoint} {a b : ℝ}
    {g : StrongDual ℝ PLPoint} (hp : g p < g v) (hn : g n = 0) (hnne : n ≠ 0) (hu : u ≠ v)
    (ha : a ∈ Ioo (-1 : ℝ) 0) (hb : b ∈ Ioo (0 : ℝ) 1)
    (haOpen : vertexGapPath v p n a ∈ openSegment ℝ v u) (hbOpen : vertexGapPath v p n b ∈ openSegment ℝ v w) :
    LinearIndependent ℝ ![u - v, w - v] := by
  have hd : p - v ≠ 0 := sub_ne_zero.mpr fun h => hp.ne (congrArg g h)
  have hdn : LinearIndependent ℝ ![p-v, n] := by
    apply (LinearIndependent.pair_iff' hd).mpr
    intro r hr
    have h := congrArg g hr
    rw [map_smul, map_sub, hn, smul_eq_mul] at h
    have hr0 := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hp.ne)
    exact hnne (by simpa [hr0] using hr.symm)
  let B := basisOfLinearIndependentOfCardEqFinrank hdn (by simp)
  have hB : (B : Fin 2 → PLPoint) = ![p-v, n] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hB₀ : B 0 = p-v := congrFun hB 0
  have hB₁ : B 1 = n := congrFun hB 1
  have hCoord {x : PLPoint} {t s : ℝ} (hs : 0 < s)
      (hDir : vertexGapPath v p n t - v = s • (x-v)) :
      B.repr (x-v) 0 = (1 - |t|) / s ∧ B.repr (x-v) 1 = t / s := by
    have h (i : Fin 2) := congrArg (fun y : PLPoint => B.repr y i) hDir
    simp only [vertexGapPath, add_sub_cancel_left, ← hB₀, ← hB₁, SteinerProof.sector_coordinate_of_combination,
      Module.Basis.repr_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    constructor
    · apply (eq_div_iff hs.ne').mpr
      simpa only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one,
        one_mul, mul_zero, zero_mul, add_zero, mul_comm] using (h 0).symm
    · apply (eq_div_iff hs.ne').mpr
      simpa only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one,
        one_mul, mul_zero, zero_mul, zero_add, mul_comm] using (h 1).symm
  obtain ⟨sa, hsa, hVa⟩ := edgeDirection_eq_of_mem_openSegment haOpen
  obtain ⟨sb, hsb, hVb⟩ := edgeDirection_eq_of_mem_openSegment hbOpen
  obtain ⟨hU0, hU1⟩ := hCoord hsa hVa
  obtain ⟨hW0, hW1⟩ := hCoord hsb hVb
  have hU0p : 0 < B.repr (u-v) 0 := by rw [hU0, abs_of_neg ha.2]; exact div_pos (by linarith [ha.1]) hsa
  have hW0p : 0 < B.repr (w-v) 0 := by rw [hW0, abs_of_pos hb.1]; exact div_pos (sub_pos.mpr hb.2) hsb
  have hU1n : B.repr (u-v) 1 < 0 := hU1 ▸ div_neg_of_neg_of_pos ha.2 hsa
  have hW1p : 0 < B.repr (w-v) 1 := hW1 ▸ div_pos hb.1 hsb
  apply (LinearIndependent.pair_iff' (sub_ne_zero.mpr hu)).mpr
  intro r hr
  have hi (i : Fin 2) : r * B.repr (u-v) i = B.repr (w-v) i := by
    rw [← hr, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hrp : 0 < r := pos_of_mul_pos_left ((hi 0).symm ▸ hW0p) hU0p.le
  exact (mul_neg_of_pos_of_neg hrp hU1n).not_ge ((hi 1).symm ▸ hW1p.le)

/-- A gap in a complex that covers the hull frontier lies between a
consecutive pair of incident edges at some vertex. -/
theorem exists_consecutive_edge_sector_of_hull_gap {K : FinitePlanarComplex}
    (hFrontier : frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization)
    (hGap : ¬ convexHull ℝ K.simplices.vertices ⊆ K.realization) :
    ∃ v u w p : PLPoint, ({v,u} : Finset PLPoint) ∈ K.edges ∧ ({v,w} : Finset PLPoint) ∈ K.edges ∧
      LinearIndependent ℝ ![u-v, w-v] ∧
      SteinerProof.ConsecutiveIncident K v u w ∧ dist p v < K.vertexFaceSeparation ∧
      p ∈ convexHull ℝ K.simplices.vertices \ K.realization ∧
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ p - v = c • (u - v) + d • (w - v) := by
  obtain ⟨g, hg, hgInjective⟩ := K.exists_vertex_separating_linearFunctional
  obtain ⟨v, hv, hvGap, hMax⟩ := exists_vertex_maxOn_closure_hull_sdiff hFrontier hg hgInjective hGap
  obtain ⟨p, n, hp, hn, hNorm, a, ha, b, hb, u, w, hu, hw, hau, hbw, hIn, hBound⟩ :=
    exists_gap_interval_between_incident_edges hFrontier hv hvGap hg hgInjective hMax
  have h0 : vertexGapPath v p n 0 = p := by simp [vertexGapPath]
  have h0I : (0 : ℝ) ∈ Ioo a b := ⟨ha.2, hb.1⟩
  have hnne : n ≠ 0 := fun h => (half_pos K.vertexFaceSeparation_pos).ne' (by simpa [h] using hNorm.symm)
  exact ⟨v, u, w, p, hu, hw,
    independent_edgeDirections_of_gap_interval hp hn hnne (K.edge_endpoints_ne hu) ha hb hau hbw,
    consecutiveIncident_of_gap_interval ha hb hau hbw (fun t ht => (hIn t ht).2) hBound,
    h0 ▸ hBound 0 (by norm_num), h0 ▸ hIn 0 h0I,
    positive_edge_combination_of_gap_interval ha hb hau hbw⟩

/-- A near point of a gap in the positive sector rules out the triangle
spanned by the two defining incident edges. -/
theorem triangle_notMem_faces_of_near_sector_gap {K : FinitePlanarComplex} {v u w p : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (hGap : p ∉ K.realization) (hp : dist p v < K.vertexFaceSeparation) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hVec : p - v = c • (u - v) + d • (w - v)) :
    ({v,u,w} : Finset PLPoint) ∉ K.simplices.faces := by
  classical
  intro hTri
  let e := c + d
  have he : 0 < e := add_pos hc hd
  let q := (c / e) • u + (d / e) • w
  have hq : q ∈ convexHull ℝ (({u,w} : Finset PLPoint) : Set PLPoint) := by
    apply (convex_convexHull ℝ _) (subset_convexHull ℝ _ (show u ∈ ({u,w} : Finset PLPoint) from by simp))
      (subset_convexHull ℝ _ (show w ∈ ({u,w} : Finset PLPoint) from by simp))
      (div_nonneg hc.le he.le) (div_nonneg hd.le he.le)
    rw [← add_div, div_self he.ne']
  have hOpp : ({u,w} : Finset PLPoint) ∈ K.simplices.faces := K.simplices.down_closed hTri (by simp) (by simp)
  have hvV : v ∈ K.simplices.vertices := K.simplices.down_closed ((K.mem_edges_iff _).mp hu).1
    (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
  have hvOpp : v ∉ ({u,w} : Finset PLPoint) := by
    simp [(K.edge_endpoints_ne hu).symm, (K.edge_endpoints_ne hw).symm]
  have hSep : K.vertexFaceSeparation ≤ dist q v := dist_comm v q ▸ K.vertexFaceSeparation_le_dist hvV hOpp hvOpp hq
  have hlink : p - v = e • (q - v) := by
    have hc' : e * (c / e) = c := by field_simp
    have hd' : e * (d / e) = d := by field_simp
    rw [hVec]
    simp only [smul_sub]
    rw [show e • q = c • u + d • w by dsimp [q]; rw [smul_add, smul_smul, smul_smul, hc', hd']]
    dsimp only [e]
    module
  have hDist : dist p v = e * dist q v := by
    rw [dist_eq_norm, hlink, norm_smul, Real.norm_eq_abs, abs_of_pos he, ← dist_eq_norm]
  have he₁ : e < 1 := (mul_lt_mul_iff_of_pos_right (K.vertexFaceSeparation_pos.trans_le hSep)).mp (by
    rw [← hDist, one_mul]
    exact hp.trans_le hSep)
  have hpSeg : p ∈ segment ℝ v q := by
    rw [segment_eq_image_lineMap]
    exact ⟨e, ⟨he.le, he₁.le⟩, by rw [AffineMap.lineMap_apply_module', ← hlink, sub_add_cancel]⟩
  have hqTri : q ∈ convexHull ℝ (({v,u,w} : Finset PLPoint) : Set PLPoint) :=
    convexHull_mono (fun _ hy => Finset.mem_insert_of_mem hy) hq
  exact hGap (K.convexHull_face_subset_realization _ hTri
    ((convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp)) hqTri hpSeg))

/-- An affine map on a finite convex hull has a vertex no higher than any given point. -/
theorem exists_le_face_vertex_of_mem_convexHull {s : Finset PLPoint} {x : PLPoint}
    (f : PLPoint →ᵃ[ℝ] ℝ) (hx : x ∈ convexHull ℝ (s : Set PLPoint)) : ∃ y ∈ s, f y ≤ f x := by
  by_contra! h
  have hsubset : (s : Set PLPoint) ⊆ f ⁻¹' Ioi (f x) := fun y hy => h y hy
  exact (lt_irrefl (f x)) (convexHull_min hsubset ((convex_Ioi _).affine_preimage f) hx)

/-- Below the first vertex in a consecutive sector, its interior is empty
unless the defining triangle already belongs to the complex. The height is
the sum of the two coordinates in the incident edge basis. -/
theorem notMem_realization_of_positive_coordinates_lt_vertex_height
    {K : FinitePlanarComplex} {v u w x : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (hc : SteinerProof.ConsecutiveIncident K v u w) (hTri : ({v,u,w} : Finset PLPoint) ∉ K.simplices.faces)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    {m : ℝ} (hm : m ≤ 1) (hVertex : ∀ y ∈ K.simplices.vertices,
      0 < B.repr (y-v) 0 → 0 < B.repr (y-v) 1 → m ≤ B.repr (y-v) 0 + B.repr (y-v) 1)
    (hx₀ : 0 < B.repr (x-v) 0) (hx₁ : 0 < B.repr (x-v) 1)
    (hxHeight : B.repr (x-v) 0 + B.repr (x-v) 1 < m) : x ∉ K.realization := by
  classical
  let F := (B.coord 0 + B.coord 1).toAffineMap.comp (AffineMap.id ℝ PLPoint - AffineMap.const ℝ PLPoint v)
  have hF (y : PLPoint) : F y = B.repr (y-v) 0 + B.repr (y-v) 1 := rfl
  intro hx
  obtain ⟨s, hs, hxs⟩ := (K.mem_realization_iff _).mp hx
  obtain ⟨y, hys, hyF⟩ := exists_le_face_vertex_of_mem_convexHull F hxs
  have hyV : y ∈ K.simplices.vertices := K.simplices.down_closed hs
    (Finset.singleton_subset_iff.mpr hys) (by simp)
  have hyOutside : min (B.repr (y-v) 0) (B.repr (y-v) 1) ≤ 0 := by
    by_contra! hy
    have h := lt_min_iff.mp hy
    rw [hF, hF] at hyF
    exact hxHeight.not_ge ((hVertex y hyV h.1 h.2).trans hyF)
  obtain ⟨q, hqSeg, i, a, ha, hqVec⟩ := SteinerProof.segment_meets_sector_boundary B hx₀ hx₁ hyOutside
  have hqS : q ∈ convexHull ℝ (s : Set PLPoint) :=
    (convex_convexHull ℝ _).segment_subset hxs (subset_convexHull ℝ _ hys) hqSeg
  have hqF : F q ≤ F x := ((convex_Iic (F x)).affine_preimage F).segment_subset
    (by change F x ≤ F x; rfl) hyF hqSeg
  have hqA : F q = a := by
    rw [hF, hqVec, add_sub_cancel_left, map_smul, Module.Basis.repr_self]
    fin_cases i <;> simp [Finsupp.single_eq_of_ne]
  have ha₁ : a < 1 := by
    rw [hqA, hF] at hqF
    exact hqF.trans_lt (hxHeight.trans_le hm)
  have hvS : v ∈ s := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_smul, add_zero] at hqVec
      have hvV : v ∈ K.simplices.vertices := K.simplices.down_closed ((K.mem_edges_iff _).mp hu).1
        (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
      exact (K.simplices.vertex_mem_convexHull_iff hvV hs).mp (hqVec ▸ hqS)
    · have hOn {z : PLPoint} (he : ({v,z} : Finset PLPoint) ∈ K.edges) (hVec : q = v + a • (z-v)) : v ∈ s :=
        (openSegment_endpoints_mem_face hs he hqS ⟨ha', ha₁⟩ (by rw [AffineMap.lineMap_apply_module', hVec, add_comm])).1
      fin_cases i
      · change q = v + a • B 0 at hqVec
        exact hOn hu (by rwa [hB₀] at hqVec)
      · change q = v + a • B 1 at hqVec
        exact hOn hw (by rwa [hB₁] at hqVec)
  obtain ⟨huS, hwS⟩ := SteinerProof.sector_endpoints_mem_face_of_pos_coordinates hs hvS hu hw hc hxs B hB₀ hB₁ hx₀ hx₁
  exact hTri (K.simplices.down_closed hs (Finset.insert_subset_iff.mpr
    ⟨hvS, Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hwS⟩⟩) (Finset.insert_nonempty _ _))

/-- If two vertices see each other along a segment avoiding the realization,
their edge can be adjoined, contradicting maximality. -/
theorem not_empty_openSegment_of_maximal {K : FinitePlanarComplex}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    {v u : PLPoint} (hv : v ∈ K.simplices.vertices) (hu : u ∈ K.simplices.vertices) (hvu : v ≠ u)
    (hOpen : ∀ p ∈ openSegment ℝ v u, p ∉ K.realization) : False := by
  classical
  let s : Finset PLPoint := {v,u}
  have hCard : s.card = 2 := Finset.card_pair hvu
  have hInd : AffineIndependent ℝ ((↑) : s → PLPoint) := by
    have hRange : range (![v,u] : Fin 2 → PLPoint) = (s : Set PLPoint) := by
      simp [s, Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    change AffineIndependent ℝ (fun x : ↥(s : Set PLPoint) => x.val)
    rw [← hRange]
    exact (affineIndependent_of_ne ℝ hvu).range
  have hProper (t : Finset PLPoint) (ht : t ⊂ s) (hne : t.Nonempty) : t ∈ K.simplices.faces := by
    have ht₂ := Finset.card_lt_card ht
    have ht₀ := Finset.card_pos.mpr hne
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
    have hp : p ∈ s := (ssubset_iff_subset_ne.mp ht).1 (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hv
    · rw [Finset.mem_singleton.mp hp]
      exact hu
  have hGlue (t : Finset PLPoint) (ht : t ∈ K.simplices.faces) :
      convexHull ℝ (s : Set PLPoint) ∩ convexHull ℝ (t : Set PLPoint) ⊆
        convexHull ℝ ((s : Set PLPoint) ∩ (t : Set PLPoint)) := by
    rintro p ⟨hps, hpt⟩
    have hSeg : p ∈ segment ℝ v u := by simpa [s, convexHull_pair] using hps
    rw [segment_eq_image_lineMap] at hSeg
    obtain ⟨a, ha, hap⟩ := hSeg
    rcases eq_or_lt_of_le ha.1 with h₀ | h₀
    · have hp : p = v := by simpa [← h₀] using hap.symm
      rw [hp] at hpt ⊢
      exact subset_convexHull ℝ _ ⟨by simp [s], (K.simplices.vertex_mem_convexHull_iff hv ht).mp hpt⟩
    rcases eq_or_lt_of_le ha.2 with h₁ | h₁
    · have hp : p = u := by simpa [h₁] using hap.symm
      rw [hp] at hpt ⊢
      exact subset_convexHull ℝ _ ⟨by simp [s], (K.simplices.vertex_mem_convexHull_iff hu ht).mp hpt⟩
    exact (hOpen p (by rw [openSegment_eq_image_lineMap]; exact ⟨a, ⟨h₀, h₁⟩, hap⟩)
      (K.convexHull_face_subset_realization t ht hpt)).elim
  let L := K.adjoinFace s (Finset.insert_nonempty _ _) hInd hProper hGlue
  have hKL : K.simplices.faces ⊆ L.simplices.faces := fun _ hs => Or.inr hs
  have hLV : L.simplices.vertices ⊆ K.simplices.vertices := by
    intro p hp
    change ({p} : Finset PLPoint) ∈ insert s K.simplices.faces at hp
    rcases hp with heq | hp
    · have h := congrArg Finset.card heq
      simp [hCard] at h
    · exact hp
  have hs : s ∈ K.simplices.faces := (hmax L hKL hLV) ▸ (show s ∈ L.simplices.faces from Or.inl rfl)
  have hMid : midpoint ℝ v u ∈ openSegment ℝ v u := midpoint_mem_openSegment v u
  apply hOpen (midpoint ℝ v u) hMid
  apply K.convexHull_face_subset_realization _ hs
  simpa [s, convexHull_pair] using openSegment_subset_segment ℝ v u hMid

/-- A maximal complex with a missing consecutive triangle has no vertex
in the open sector at or below the opposite edge of that triangle. -/
theorem one_lt_height_of_sector_vertex_of_maximal
    {K : FinitePlanarComplex} {v u w y : PLPoint}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (hc : SteinerProof.ConsecutiveIncident K v u w) (hTri : ({v,u,w} : Finset PLPoint) ∉ K.simplices.faces)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u - v) (hB₁ : B 1 = w - v)
    (hy : y ∈ K.simplices.vertices) (hy₀ : 0 < B.repr (y-v) 0) (hy₁ : 0 < B.repr (y-v) 1) :
    1 < B.repr (y-v) 0 + B.repr (y-v) 1 := by
  let f := fun z : PLPoint => B.repr (z-v) 0 + B.repr (z-v) 1
  let U := {z ∈ K.simplices.vertices | 0 < B.repr (z-v) 0 ∧ 0 < B.repr (z-v) 1}
  have hF : U.Finite := K.finite_vertexSet.subset fun _ hz => hz.1
  obtain ⟨z, hz, hMin⟩ := U.exists_min_image f hF ⟨y, hy, hy₀, hy₁⟩
  by_contra! h
  have hm : f z ≤ 1 := (hMin y ⟨hy, hy₀, hy₁⟩).trans h
  have hmPos : 0 < f z := add_pos hz.2.1 hz.2.2
  have hv : v ∈ K.simplices.vertices := K.simplices.down_closed ((K.mem_edges_iff _).mp hu).1
    (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
  have hvz : v ≠ z := fun h => by simp [← h, f] at hmPos
  apply not_empty_openSegment_of_maximal hmax hv hz.1 hvz
  intro p hp
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have hScale (i : Fin 2) : B.repr (AffineMap.lineMap v z t - v) i = t * B.repr (z-v) i := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply notMem_realization_of_positive_coordinates_lt_vertex_height hu hw hc hTri B hB₀ hB₁ hm
    (fun q hq hq₀ hq₁ => hMin q ⟨hq, hq₀, hq₁⟩)
  · rw [hScale]
    exact mul_pos ht.1 hz.2.1
  · rw [hScale]
    exact mul_pos ht.1 hz.2.2
  · rw [hScale, hScale, ← mul_add]
    have hLt := mul_lt_mul_of_pos_right ht.2 hmPos
    rwa [one_mul] at hLt

end FinitePlanarComplex
