import SteinerProof.ArrowheadGeometry
import SteinerProof.TriangleFacet
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Localization of nearest points for the bisector lemma in Section 3.1. -/

open Set InnerProductGeometry

noncomputable section

namespace FinitePlanarComplex

/-- Every point of the realization lies in the open part of one of its faces. -/
theorem exists_openFace_of_mem_realization {A : FinitePlanarComplex} {x : PLPoint}
    (hx : x ∈ A.realization) :
    ∃ s ∈ A.simplices.faces, x ∈ openFace s := by
  classical
  let faces := A.faceFinset.filter fun (s : Finset PLPoint) => x ∈ convexHull ℝ (s : Set PLPoint)
  obtain ⟨t, ht, hxt⟩ := (A.mem_realization_iff x).mp hx
  have hne : faces.Nonempty :=
    ⟨t, Finset.mem_filter.mpr ⟨(A.mem_faceFinset_iff t).mpr ht, hxt⟩⟩
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image faces Finset.card hne
  obtain ⟨hsA, hxs⟩ := Finset.mem_filter.mp hs
  have hface := (A.mem_faceFinset_iff s).mp hsA
  refine ⟨s, hface, hxs, ?_⟩
  intro hboundary
  obtain ⟨u, hus, hxu⟩ := Set.mem_iUnion₂.mp hboundary
  have hu : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxu⟩)
  have huA := A.simplices.down_closed hface (Finset.ssubset_iff_subset_ne.mp hus).1 hu
  have huMem : u ∈ faces := Finset.mem_filter.mpr ⟨(A.mem_faceFinset_iff u).mpr huA, hxu⟩
  exact (not_lt_of_ge (hmin u huMem)) (Finset.card_lt_card hus)

/-- The open face of a two-vertex simplex is contained in its open segment. -/
theorem openFace_pair_mem_openSegment {p v w : PLPoint} (hv : v ≠ w)
    (hp : p ∈ openFace ({v, w} : Finset PLPoint)) : p ∈ openSegment ℝ v w := by
  have hpSeg : p ∈ segment ℝ v w := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hp.1
  have hnotEndpoint (a : PLPoint) (ha : a ∈ ({v, w} : Finset PLPoint)) : p ≠ a := by
    have hsub : ({a} : Finset PLPoint) ⊂ {v, w} := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.singleton_subset_iff.mpr ha, ?_⟩
      intro heq
      have h := congrArg Finset.card heq
      rw [Finset.card_singleton, Finset.card_pair hv] at h
      omega
    intro hpa
    exact hp.2 (Set.mem_iUnion₂.mpr ⟨{a}, hsub, by simp [hpa]⟩)
  have hpv := hnotEndpoint v (by simp)
  have hpw := hnotEndpoint w (by simp)
  obtain ⟨t, ht, htp⟩ := (show p ∈ AffineMap.lineMap v w '' Icc (0 : ℝ) 1 by
    rwa [← segment_eq_image_lineMap])
  have ht₀ : 0 < t := by
    refine lt_of_le_of_ne ht.1 fun h => hpv ?_
    simpa [← h] using htp.symm
  have ht₁ : t < 1 := by
    refine lt_of_le_of_ne ht.2 fun h => hpw ?_
    simpa [h] using htp.symm
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, ⟨ht₀, ht₁⟩, htp⟩

theorem notMem_interior_of_nearest {S : Set PLPoint} {p z : PLPoint}
    (hp : p ∉ S) (hz : z ∈ S) (hmin : Metric.infDist p S = dist p z) :
    z ∉ interior S := by
  intro hzi
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzi
  let D := dist z p
  have hD : 0 < D := dist_pos.mpr (fun h => hp (h ▸ hz))
  let t := min (1 / 2 : ℝ) (ε / (2 * D))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht₁ : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let y := AffineMap.lineMap z p t
  have hdist : dist z y = t * D := by
    rw [show y = AffineMap.lineMap z p t from rfl, dist_left_lineMap, Real.norm_eq_abs,
      abs_of_nonneg ht.le]
  have hε₂ : ε / (2 * D) * D = ε / 2 := by
    field_simp [hD.ne']
  have hyball : y ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_comm y z, hdist]
    have htle := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (ε / (2 * D))) hD.le
    change t * D ≤ ε / (2 * D) * D at htle
    linarith
  have hydist : dist y p = (1 - t) * D := by
    rw [show y = AffineMap.lineMap z p t from rfl, dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht₁)]
  have hbound : Metric.infDist p S ≤ dist p y :=
    Metric.infDist_le_dist_of_mem (interior_subset (hball hyball))
  rw [hmin, dist_comm p z, dist_comm p y, hydist] at hbound
  change D ≤ (1 - t) * D at hbound
  nlinarith [mul_pos ht hD]

/-- The nearest point of a planar complex to an exterior point belongs to the
open part of a vertex or edge. -/
theorem exists_nearest_openFace_card_le_two {A : FinitePlanarComplex} {p : PLPoint}
    (hA : A.realization.Nonempty) (hp : p ∉ A.realization) :
    ∃ z s, s ∈ A.simplices.faces ∧ s.card ≤ 2 ∧ z ∈ openFace s ∧
      Metric.infDist p A.realization = dist p z := by
  obtain ⟨z, hz, hmin⟩ := A.isCompact_realization.exists_infDist_eq_dist hA p
  obtain ⟨s, hs, hzs⟩ := exists_openFace_of_mem_realization hz
  refine ⟨z, s, hs, ?_, hzs, hmin⟩
  have hdim : s.card ≤ 3 := by
    have h := (A.simplices.indep hs).card_le_finrank_succ
    have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
    simp only [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at hle
    omega
  by_contra! h
  have hcard : s.card = 3 := by omega
  rw [openFace_eq_interior_of_card_three (A.triangleOfFace s hs hcard)
    (A.range_triangleOfFace s hs hcard)] at hzs
  have hzInterior := interior_mono (A.convexHull_face_subset_realization s hs) hzs
  exact notMem_interior_of_nearest hp hz hmin hzInterior

end FinitePlanarComplex

namespace SteinerProof

/-- If an exterior bisector point has a point of the complex closer than
`α * r`, its nearest point belongs to a vertex or edge incident to `v`. -/
theorem exists_nearest_incident_openFace_of_infDist_lt
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint} (hv : v ∈ K.simplices.vertices)
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4)
    (hA : A.realization.Nonempty) (hp : arrowheadBisectorPoint v u w r α ∉ A.realization)
    (hnear : Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization < α * r) :
    ∃ z s, s ∈ A.simplices.faces ∧ s.card ≤ 2 ∧ v ∈ s ∧
      z ∈ FinitePlanarComplex.openFace s ∧ dist (arrowheadBisectorPoint v u w r α) z < α * r := by
  obtain ⟨z, s, hs, hcard, hz, hmin⟩ :=
    FinitePlanarComplex.exists_nearest_openFace_card_le_two hA hp
  rw [hmin] at hnear
  refine ⟨z, s, hs, hcard, ?_, hz, hnear⟩
  let c := (Real.sin (angle (u - v) (w - v) / 2))⁻¹
  have hθ := K.incident_angle_pos hu hw huw
  have hc : 0 ≤ c := inv_nonneg.mpr
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
  have hpDist := dist_arrowheadBisectorPoint v u w hr.le hα
    (FinitePlanarComplex.edge_endpoints_ne hu) (FinitePlanarComplex.edge_endpoints_ne hw) hθ hθπ
  have htri := dist_triangle v (arrowheadBisectorPoint v u w r α) z
  rw [dist_comm v (arrowheadBisectorPoint v u w r α), hpDist] at htri
  have hclose : dist v z < α * r * (1 + c) := by
    change dist v z ≤ α * r * c + dist (arrowheadBisectorPoint v u w r α) z at htri
    linarith
  have hM := K.four_mul_one_add_csc_lt_separation hu hw huw hθ hr hrK
  have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα₄ hr.le)
    (show 0 ≤ 1 + c by linarith)
  have hzclose := (hclose.trans_le hbound).trans (show 4 * r * (1 + c) < _ from hM)
  by_contra hvs
  exact (not_lt_of_ge (K.vertexFaceSeparation_le_dist hv (hAK hs) hvs hz.1)) hzclose

/-- A point closer than `α * r` to an exterior bisector point can be found
on a third edge at the common vertex. Neither defining edge nor the vertex can
supply such a point. -/
theorem exists_third_incident_edge_of_infDist_lt
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint} (hv : v ∈ K.simplices.vertices)
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4)
    (hA : A.realization.Nonempty) (hp : arrowheadBisectorPoint v u w r α ∉ A.realization)
    (hnear : Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization < α * r) :
    ∃ z x : PLPoint, ({v, x} : Finset PLPoint) ∈ A.edges ∧ x ≠ u ∧ x ≠ w ∧
      z ∈ segment ℝ v x ∧ z ≠ v ∧ dist (arrowheadBisectorPoint v u w r α) z < α * r := by
  obtain ⟨z, s, hs, hcard, hvs, hz, hdist⟩ :=
    exists_nearest_incident_openFace_of_infDist_lt hAK hv hu hw huw hθπ hr hrK hα hα₄ hA hp hnear
  have hθ := K.incident_angle_pos hu hw huw
  have hsin : 0 < Real.sin (angle (u - v) (w - v) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 1 ≤ (Real.sin (angle (u - v) (w - v) / 2))⁻¹ := by
    rw [← one_div, le_div_iff₀ hsin, one_mul]
    exact Real.sin_le_one _
  have hzv : z ≠ v := by
    intro heq
    rw [heq, dist_arrowheadBisectorPoint v u w hr.le hα
      (FinitePlanarComplex.edge_endpoints_ne hu) (FinitePlanarComplex.edge_endpoints_ne hw)
      hθ hθπ] at hdist
    exact (not_lt_of_ge (le_mul_of_one_le_right (mul_nonneg hα hr.le) hc)) hdist
  have hcard₂ : s.card = 2 := by
    have hpos := Finset.card_pos.mpr (A.simplices.nonempty_of_mem_faces hs)
    by_contra h₂
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
    have hvy : v = y := Finset.mem_singleton.mp hvs
    have hzy : z = y := by
      have h := hz.1
      simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using h
    exact hzv (hzy.trans hvy.symm)
  obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hcard₂
  have hsPair : ∃ x : PLPoint, ({a, b} : Finset PLPoint) = {v, x} := by
    rcases Finset.mem_insert.mp hvs with hab | hab
    · exact ⟨b, by rw [hab]⟩
    · have hb : v = b := Finset.mem_singleton.mp hab
      exact ⟨a, by rw [hb, Finset.pair_comm]⟩
  obtain ⟨x, hx⟩ := hsPair
  have hEdge : ({v, x} : Finset PLPoint) ∈ A.edges :=
    (A.mem_edges_iff _).mpr ⟨hx ▸ hs, hx ▸ hcard₂⟩
  have hzSeg : z ∈ segment ℝ v x := by
    have h := hz.1
    rwa [hx, Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at h
  refine ⟨z, x, hEdge, ?_, ?_, hzSeg, hzv, hdist⟩
  · intro heq
    subst x
    have h : Metric.infDist (arrowheadBisectorPoint v u w r α) (segment ℝ v u) ≤
        dist (arrowheadBisectorPoint v u w r α) z := Metric.infDist_le_dist_of_mem hzSeg
    rw [infDist_arrowheadBisectorPoint_edge hu hw huw hθπ hr hrK hα hα₄] at h
    exact (not_lt_of_ge h) hdist
  · intro heq
    subst x
    have h : Metric.infDist (arrowheadBisectorPoint v u w r α) (segment ℝ v w) ≤
        dist (arrowheadBisectorPoint v u w r α) z := Metric.infDist_le_dist_of_mem hzSeg
    rw [infDist_arrowheadBisectorPoint_other_edge hu hw huw hθπ hr hrK hα hα₄] at h
    exact (not_lt_of_ge h) hdist

/-- Either incident edge supplies the upper bound on the distance to the
realization in the bisector lemma. -/
theorem infDist_arrowheadBisectorPoint_realization_le
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint} (hu : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hθπ : angle (u - v) (w - v) < Real.pi)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4) :
    Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization ≤ α * r := by
  obtain ⟨huFace, huCard⟩ := (A.mem_edges_iff _).mp hu
  have huK : ({v, u} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK huFace, huCard⟩
  have hseg : segment ℝ v u ⊆ A.realization := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      A.convexHull_face_subset_realization _ huFace
  rw [← infDist_arrowheadBisectorPoint_edge huK hw huw hθπ hr hrK hα hα₄]
  exact Metric.infDist_le_infDist_of_subset hseg ⟨v, left_mem_segment ℝ v u⟩

/-- A segment from inside the open positive sector to a point outside it meets
one of the two nonnegative boundary rays. Coordinates are taken about `v`. -/
theorem segment_meets_sector_boundary (b : Module.Basis (Fin 2) ℝ PLPoint)
    {v p z : PLPoint}
    (hp₀ : 0 < b.repr (p - v) 0) (hp₁ : 0 < b.repr (p - v) 1)
    (hz : min (b.repr (z - v) 0) (b.repr (z - v) 1) ≤ 0) :
    ∃ q ∈ segment ℝ p z, ∃ (i : Fin 2) (a : ℝ), 0 ≤ a ∧ q = v + a • b i := by
  let g (i : Fin 2) (t : ℝ) := (1 - t) * b.repr (p - v) i + t * b.repr (z - v) i
  let f (t : ℝ) := min (g 0 t) (g 1 t)
  have hf : Continuous f := by
    dsimp [f, g]
    fun_prop
  have hf₀ : 0 < f 0 := by simpa [f, g, lt_min_iff] using And.intro hp₀ hp₁
  have hf₁ : f 1 ≤ 0 := by simpa [f, g] using hz
  obtain ⟨t, ht, hzero⟩ :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn
      (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨hf₁, hf₀.le⟩)
  let q := AffineMap.lineMap p z t
  have hq : q ∈ segment ℝ p z := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hlin : q - v = (1 - t) • (p - v) + t • (z - v) := by
    have hv : (1 - t) • v + t • v = v := by rw [← add_smul, sub_add_cancel, one_smul]
    dsimp [q]
    rw [AffineMap.lineMap_apply_module, smul_sub, smul_sub, sub_add_sub_comm, hv]
  have hcoord (i : Fin 2) : b.repr (q - v) i = g i t := by
    rw [hlin, map_add, map_smul, map_smul]
    rfl
  have hsum := b.sum_repr (q - v)
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1] at hsum
  refine ⟨q, hq, ?_⟩
  change min (g 0 t) (g 1 t) = 0 at hzero
  rcases le_total (g 0 t) (g 1 t) with h | h
  · rw [min_eq_left h] at hzero
    rw [hzero, zero_smul, zero_add] at hsum
    exact ⟨1, g 1 t, hzero ▸ h, by rw [hsum]; abel⟩
  · rw [min_eq_right h] at hzero
    rw [hzero, zero_smul, add_zero] at hsum
    exact ⟨0, g 0 t, hzero ▸ h, by rw [hsum]; abel⟩

/-- Inside the separation ball, the sector boundary rays agree with their
finite defining edges. Thus a local crossing meets an actual edge. -/
theorem segment_meets_incident_edge_of_sector_crossing
    {K : FinitePlanarComplex} {v u w p z : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (b : Module.Basis (Fin 2) ℝ PLPoint) (hb₀ : b 0 = u - v) (hb₁ : b 1 = w - v)
    (hp₀ : 0 < b.repr (p - v) 0) (hp₁ : 0 < b.repr (p - v) 1)
    (hz : min (b.repr (z - v) 0) (b.repr (z - v) 1) ≤ 0)
    (hpM : dist p v < K.vertexFaceSeparation) (hzM : dist z v < K.vertexFaceSeparation) :
    ∃ q ∈ segment ℝ p z, q ∈ segment ℝ v u ∪ segment ℝ v w := by
  obtain ⟨q, hq, i, a, ha, heq⟩ := segment_meets_sector_boundary b hp₀ hp₁ hz
  have hqM : dist q v < K.vertexFaceSeparation :=
    Metric.mem_ball.mp ((convex_ball v K.vertexFaceSeparation).segment_subset
      (Metric.mem_ball.mpr hpM) (Metric.mem_ball.mpr hzM) hq)
  have hRay (x : PLPoint) (hx : ({v, x} : Finset PLPoint) ∈ K.edges)
      (hqx : q = v + a • (x - v)) : q ∈ segment ℝ v x := by
    have hmap : AffineMap.lineMap v x a = q := by
      rw [AffineMap.lineMap_apply_module', hqx, add_comm]
    have hdist := dist_left_lineMap v x a
    rw [hmap, Real.norm_eq_abs, abs_of_nonneg ha] at hdist
    have hle := FinitePlanarComplex.vertexFaceSeparation_le_edge_dist hx
    have hpos := K.vertexFaceSeparation_pos.trans_le hle
    have hmul : a * dist v x ≤ 1 * dist v x := by
      rw [one_mul, ← hdist, dist_comm v q]
      exact hqM.le.trans hle
    rw [segment_eq_image_lineMap]
    exact ⟨a, ⟨ha, (mul_le_mul_iff_left₀ hpos).mp hmul⟩, hmap⟩
  refine ⟨q, hq, ?_⟩
  fin_cases i
  · change q = v + a • b 0 at heq
    exact Or.inl (hRay u hu (by rwa [hb₀] at heq))
  · change q = v + a • b 1 at heq
    exact Or.inr (hRay w hw (by rwa [hb₁] at heq))

/-- No third edge at `v) lies strictly inside the non-reflex sector from `u`
to `w`. This predicate uses positive coefficients in the two edge directions. -/
def ConsecutiveIncident (A : FinitePlanarComplex) (v u w : PLPoint) : Prop :=
  ∀ x : PLPoint, ({v, x} : Finset PLPoint) ∈ A.edges → x ≠ u → x ≠ w →
    ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x - v = a • (u - v) + b • (w - v)

theorem exists_incident_basis {v u w : PLPoint} (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hθπ : angle (u - v) (w - v) < Real.pi) :
    ∃ b : Module.Basis (Fin 2) ℝ PLPoint, b 0 = u - v ∧ b 1 = w - v := by
  have hind : LinearIndependent ℝ ![u - v, w - v] := by
    apply (LinearIndependent.pair_iff' (sub_ne_zero.mpr hu)).mpr
    intro a ha
    rcases lt_trichotomy a 0 with h | h | h
    · exact hθπ.ne (angle_eq_pi_iff.mpr ⟨sub_ne_zero.mpr hu, a, h, ha.symm⟩)
    · exact sub_ne_zero.mpr hw (by simpa [h] using ha.symm)
    · exact hθ.ne' (angle_eq_zero_iff.mpr ⟨sub_ne_zero.mpr hu, a, h, ha.symm⟩)
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  have hb : (b : Fin 2 → PLPoint) = ![u - v, w - v] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact ⟨b, congrFun hb 0, congrFun hb 1⟩

/-- Outside the realization, the bisector point of a consecutive pair is at
distance exactly `α * r` from the whole complex. -/
theorem infDist_arrowheadBisectorPoint_eq_of_consecutive
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) (hw : ({v, w} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    (hcon : ConsecutiveIncident A v u w)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4)
    (hp : arrowheadBisectorPoint v u w r α ∉ A.realization) :
    Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization = α * r := by
  let p := arrowheadBisectorPoint v u w r α
  have huFace := (A.mem_edges_iff _).mp hu
  have hwFace := (A.mem_edges_iff _).mp hw
  have huK : ({v, u} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK huFace.1, huFace.2⟩
  have hwK : ({v, w} : Finset PLPoint) ∈ K.edges :=
    (K.mem_edges_iff _).mpr ⟨hAK hwFace.1, hwFace.2⟩
  have hv : v ∈ K.simplices.vertices := by
    rw [K.simplices.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨{v, u}, hAK huFace.1, by simp⟩
  have hA : A.realization.Nonempty := ⟨v, A.convexHull_face_subset_realization _ huFace.1
    (subset_convexHull ℝ _ (by simp))⟩
  refine le_antisymm (infDist_arrowheadBisectorPoint_realization_le hAK hu hwK huw hθπ
    hr hrK hα hα₄) ?_
  by_contra! hlow
  have hαpos : 0 < α := pos_of_mul_pos_left (Metric.infDist_nonneg.trans_lt hlow) hr.le
  obtain ⟨z, x, hxe, hxu, hxw, hz, hzv, hdist⟩ :=
    exists_third_incident_edge_of_infDist_lt hAK hv huK hwK huw hθπ hr hrK hα hα₄ hA hp hlow
  have hθ := K.incident_angle_pos huK hwK huw
  have huv := FinitePlanarComplex.edge_endpoints_ne huK
  have hwv := FinitePlanarComplex.edge_endpoints_ne hwK
  obtain ⟨b, hb₀, hb₁⟩ := exists_incident_basis huv hwv hθ hθπ
  let d := α * r / Real.sin (angle (u - v) (w - v))
  have hd : 0 < d := div_pos (mul_pos hαpos hr) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
  have hpvec : p - v =
      (d * ‖u - v‖⁻¹) • b 0 + (d * ‖w - v‖⁻¹) • b 1 := by
    simp [p, arrowheadBisectorPoint, d, hb₀, hb₁, NormedSpace.normalize, smul_add, smul_smul]
  have hp₀ : 0 < b.repr (p - v) 0 := by
    rw [hpvec, map_add, map_smul, map_smul]
    simpa [Module.Basis.repr_self] using
      mul_pos hd (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr huv)))
  have hp₁ : 0 < b.repr (p - v) 1 := by
    rw [hpvec, map_add, map_smul, map_smul]
    simpa [Module.Basis.repr_self] using
      mul_pos hd (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hwv)))
  have hzOutside : min (b.repr (z - v) 0) (b.repr (z - v) 1) ≤ 0 := by
    by_contra! h
    have hcoord := lt_min_iff.mp h
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have htpos : 0 < t := by
      refine lt_of_le_of_ne ht.1 fun hzero => hzv ?_
      simpa [← hzero] using htz.symm
    have hvec : z - v = t • (x - v) := by
      rw [← htz, AffineMap.lineMap_apply_module', add_sub_cancel_right]
    have hbpos (i : Fin 2) (hzi : 0 < b.repr (z - v) i) :
        0 < b.repr (x - v) i := by
      rw [hvec, map_smul] at hzi
      exact pos_of_mul_pos_right hzi htpos.le
    apply hcon x hxe hxu hxw
    have hsum := b.sum_repr (x - v)
    rw [Fin.sum_univ_two, hb₀, hb₁] at hsum
    exact ⟨_, _, hbpos 0 hcoord.1, hbpos 1 hcoord.2, hsum.symm⟩
  have hpM := dist_arrowheadBisectorPoint_lt_separation huK hwK huw hθπ hr hrK hα hα₄
  have hzM : dist z v < K.vertexFaceSeparation := by
    let c := (Real.sin (angle (u - v) (w - v) / 2))⁻¹
    have hc : 0 ≤ c := inv_nonneg.mpr
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
    have htri := dist_triangle z p v
    rw [dist_comm z p, dist_arrowheadBisectorPoint v u w hr.le hα huv hwv hθ hθπ] at htri
    have hle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα₄ hr.le)
      (show 0 ≤ 1 + c by linarith)
    have hM := K.four_mul_one_add_csc_lt_separation huK hwK huw hθ hr hrK
    change dist z v ≤ dist p z + α * r * c at htri
    change dist p z < α * r at hdist
    change 4 * r * (1 + c) < K.vertexFaceSeparation at hM
    linarith
  obtain ⟨q, hq, hEdge⟩ :=
    segment_meets_incident_edge_of_sector_crossing huK hwK b hb₀ hb₁ hp₀ hp₁ hzOutside hpM hzM
  have hqDist := Metric.mem_closedBall.mp (segment_subset_closedBall_left p z hq)
  have hqLe : dist p q ≤ dist p z := by simpa only [dist_comm q p] using hqDist
  have hqClose := hqLe.trans_lt hdist
  rcases hEdge with hqu | hqw
  · have h := Metric.infDist_le_dist_of_mem (x := p) hqu
    rw [infDist_arrowheadBisectorPoint_edge huK hwK huw hθπ hr hrK hα hα₄] at h
    exact (not_lt_of_ge h) hqClose
  · have h := Metric.infDist_le_dist_of_mem (x := p) hqw
    rw [infDist_arrowheadBisectorPoint_other_edge huK hwK huw hθπ hr hrK hα hα₄] at h
    exact (not_lt_of_ge h) hqClose

/-- The distance dichotomy of the bisector lemma, including the endpoints
of the parameter interval. -/
theorem infDist_arrowheadBisectorPoint_eq_zero_or
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) (hw : ({v, w} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    (hcon : ConsecutiveIncident A v u w)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 ≤ α) (hα₄ : α ≤ 4) :
    Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization = 0 ∨
      Metric.infDist (arrowheadBisectorPoint v u w r α) A.realization = α * r := by
  by_cases hp : arrowheadBisectorPoint v u w r α ∈ A.realization
  · exact Or.inl (Metric.infDist_zero_of_mem hp)
  · exact Or.inr (infDist_arrowheadBisectorPoint_eq_of_consecutive hAK hu hw huw hθπ hcon
      hr hrK hα hα₄ hp)

/-- For an interior parameter, a bisector point outside the realization lies
on the frontier of the corresponding offset. -/
theorem arrowheadBisectorPoint_mem_realization_or_frontier
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) (hw : ({v, w} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hθπ : angle (u - v) (w - v) < Real.pi)
    (hcon : ConsecutiveIncident A v u w)
    {r α : ℝ} (hr : 0 < r) (hrK : r < K.admissibleRadius) (hα : 0 < α) (hα₄ : α < 4) :
    arrowheadBisectorPoint v u w r α ∈
      A.realization ∪ frontier (offset A.realization (α * r)) := by
  let f (β : ℝ) := arrowheadBisectorPoint v u w r β
  by_cases hp : f α ∈ A.realization
  · exact Or.inl hp
  · apply Or.inr
    rw [frontier_eq_closure_inter_closure]
    have hA : A.realization.Nonempty :=
      ⟨v, A.convexHull_face_subset_realization _ ((A.mem_edges_iff _).mp hu).1
        (subset_convexHull ℝ _ (by simp))⟩
    have hd := infDist_arrowheadBisectorPoint_eq_of_consecutive hAK hu hw huw hθπ hcon
      hr hrK hα.le hα₄.le hp
    refine ⟨subset_closure ⟨hA, hd.le⟩, ?_⟩
    have hf : Continuous f := by
      dsimp [f, arrowheadBisectorPoint]
      fun_prop
    have hopen : IsOpen (f ⁻¹' A.realizationᶜ) := A.isClosed_realization.isOpen_compl.preimage hf
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen α hp
    let βmax := min 4 (α + ε)
    have hmax : α < βmax := lt_min hα₄ (by linarith)
    have hclosure : α ∈ closure (Ioo α βmax) := by
      rw [closure_Ioo hmax.ne]
      exact left_mem_Icc.mpr hmax.le
    have himage : f '' Ioo α βmax ⊆ (offset A.realization (α * r))ᶜ := by
      rintro _ ⟨β, hβ, rfl⟩
      have hbε : β ∈ Metric.ball α ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ.1)]
        have h := hβ.2.trans_le (min_le_right 4 (α + ε))
        linarith
      have hβnot : f β ∉ A.realization := hball hbε
      have hdβ := infDist_arrowheadBisectorPoint_eq_of_consecutive hAK hu hw huw hθπ hcon
        hr hrK (hα.trans hβ.1).le (hβ.2.le.trans (min_le_left _ _)) hβnot
      intro hOff
      have hle : Metric.infDist (f β) A.realization ≤ α * r := hOff.2
      change Metric.infDist (f β) A.realization = β * r at hdβ
      rw [hdβ] at hle
      exact (not_le_of_gt (mul_lt_mul_of_pos_right hβ.1 hr)) hle
    exact closure_mono himage (image_closure_subset_closure_image hf ⟨α, hclosure, rfl⟩)

end SteinerProof
