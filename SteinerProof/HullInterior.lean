import SteinerProof.HullRefinement
import SteinerProof.ArrowheadLocalization
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Locating an extremal point of an unfilled region of a planar hull. -/

open Set Filter
open scoped Topology

noncomputable section

namespace FinitePlanarComplex

private theorem face_card_cases {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.simplices.faces) : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by
  have hpos := Finset.card_pos.mpr (K.simplices.nonempty_of_mem_faces hs)
  have h := (K.simplices.indep hs).card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
  simp only [Fintype.card_coe] at h
  rw [finrank_euclideanSpace_fin] at hle
  omega

/-- A generic linear functional takes distinct values on the vertices of a
finite planar complex. -/
theorem exists_vertex_separating_linearFunctional (K : FinitePlanarComplex) :
    ∃ g : StrongDual ℝ PLPoint, g ≠ 0 ∧ InjOn g K.simplices.vertices := by
  let slope : PLPoint × PLPoint → ℝ := fun pq => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)
  have hFinite := (K.finite_vertexSet.prod K.finite_vertexSet).image slope
  obtain ⟨m, hm⟩ := hFinite.exists_notMem
  let c₀ : StrongDual ℝ PLPoint := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  let c₁ : StrongDual ℝ PLPoint := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  let g := c₀ + m • c₁
  have hApply (p : PLPoint) : g p = p 0 + m * p 1 := rfl
  refine ⟨g, ?_, ?_⟩
  · intro h
    have h1 : g (EuclideanSpace.single 0 1) = 1 := by simp [hApply, EuclideanSpace.single]
    simp [h] at h1
  intro p hp q hq heq
  rw [hApply, hApply] at heq
  have h₁ : p 1 = q 1 := by
    by_contra hneq
    apply hm
    refine ⟨(p,q), ⟨hp,hq⟩, ?_⟩
    change (q 0 - p 0) / (p 1 - q 1) = m
    apply (div_eq_iff (sub_ne_zero.mpr hneq)).mpr
    linarith only [heq, mul_sub m (p 1) (q 1)]
  rw [h₁, add_left_inj] at heq
  ext i
  fin_cases i
  · exact heq
  · exact h₁

private theorem open_hull_sdiff {K : FinitePlanarComplex}
    (hFrontier : frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization) :
    IsOpen (convexHull ℝ K.simplices.vertices \ K.realization) := by
  let C := convexHull ℝ K.simplices.vertices
  have hUeq : C \ K.realization = interior C \ K.realization := by
    refine Subset.antisymm ?_ (Set.sdiff_subset_sdiff_left interior_subset)
    rintro y ⟨hyC, hyK⟩
    refine ⟨?_, hyK⟩
    by_contra hyInt
    exact hyK (hFrontier ⟨subset_closure hyC, hyInt⟩)
  rw [hUeq]
  exact isOpen_interior.sdiff K.isClosed_realization

private theorem linearFunctional_lt_maxOn_closure_of_mem_open {U : Set PLPoint} {x y : PLPoint}
    (hU : IsOpen U) {g : StrongDual ℝ PLPoint} (hg : g ≠ 0) (hMax : IsMaxOn g (closure U) x)
    (hy : y ∈ U) : g y < g x := by
  have hImage := g.isOpenMap_of_ne_zero hg U hU
  obtain ⟨a, b, hab, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hImage.mem_nhds (mem_image_of_mem g hy))
  obtain ⟨c, hyc, hcb⟩ := exists_between hab.2
  obtain ⟨z, hz, rfl⟩ := hIoo ⟨hab.1.trans hyc, hcb⟩
  exact hyc.trans_le (isMaxOn_iff.mp hMax z (subset_closure hz))

/-- A boundary point of a hull gap near a vertex, other than the vertex
itself, belongs to the open part of an incident edge. -/
theorem exists_incident_edge_of_mem_frontier_hull_sdiff {K : FinitePlanarComplex}
    (hFrontier : frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization)
    {v x : PLPoint} (hv : v ∈ K.simplices.vertices)
    (hxGap : x ∈ frontier (convexHull ℝ K.simplices.vertices \ K.realization))
    (hxDist : dist x v < K.vertexFaceSeparation) (hxne : x ≠ v) :
    ∃ u, ({v,u} : Finset PLPoint) ∈ K.edges ∧ x ∈ openSegment ℝ v u := by
  classical
  have hC := K.finite_vertexSet.isClosed_convexHull ℝ
  have hxC := closure_minimal sdiff_subset hC hxGap.1
  have hxK : x ∈ K.realization := by
    by_contra hNot
    exact hxGap.2 ((open_hull_sdiff hFrontier).interior_eq.symm ▸ ⟨hxC, hNot⟩)
  obtain ⟨s, hs, hxs⟩ := exists_openFace_of_mem_realization hxK
  have hvs : v ∈ s := by
    by_contra hNot
    exact hxDist.not_ge (dist_comm v x ▸ K.vertexFaceSeparation_le_dist hv hs hNot hxs.1)
  rcases face_card_cases hs with hs₁ | hs₂ | hs₃
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hs₁
    have hx : x = u := by simpa using hxs.1
    exact (hxne (hx.trans (Finset.mem_singleton.mp hvs).symm)).elim
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs₂
    rcases Finset.mem_insert.mp hvs with rfl | h
    · exact ⟨b, (K.mem_edges_iff _).mpr ⟨hs,hs₂⟩, openFace_pair_mem_openSegment hab hxs⟩
    · have hvb := Finset.mem_singleton.mp h
      subst v
      rw [Finset.pair_comm a b] at hs hxs
      exact ⟨a, (K.mem_edges_iff _).mpr ⟨hs, Finset.card_pair hab.symm⟩,
        openFace_pair_mem_openSegment hab.symm hxs⟩
  · have hxInt : x ∈ interior (convexHull ℝ (s : Set PLPoint)) :=
      (openFace_eq_interior_of_card_three (K.triangleOfFace s hs hs₃) (K.range_triangleOfFace s hs hs₃)) ▸ hxs
    obtain ⟨y, hy, _, hyNot⟩ := mem_closure_iff.mp hxGap.1 _ isOpen_interior hxInt
    exact (hyNot (K.convexHull_face_subset_realization s hs (interior_subset hy))).elim

private theorem exists_face_vertex_coordinate {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.simplices.faces) {u v : PLPoint} (hu : u ∈ s) (hv : v ∈ s) (hvu : v ≠ u) :
    ∃ f : PLPoint →ᵃ[ℝ] ℝ, f u = 1 ∧ ∀ p ∈ s, p ≠ u → f p = 0 := by
  let S := (s : Set PLPoint) \ {u}
  let P := affineSpan ℝ S
  have hind : AffineIndepOn ℝ id (s : Set PLPoint) := K.simplices.indep hs
  have huP : u ∉ P := by
    have h := hind.notMem_affineSpan_sdiff hu
    change u ∉ affineSpan ℝ (id '' S) at h
    rwa [Set.image_id] at h
  have hvP : v ∈ P := mem_affineSpan ℝ ⟨hv, hvu⟩
  have hd : u - v ∉ P.direction := by
    intro hh
    have h := AffineSubspace.vadd_mem_of_mem_direction hh hvP
    apply huP
    simpa only [vadd_eq_add, sub_add_cancel] using h
  obtain ⟨g, hg, hgu⟩ := LinearMap.exists_extend_of_notMem (0 : P.direction →ₗ[ℝ] ℝ) hd 1
  let f := g.toAffineMap.comp ((AffineMap.id ℝ PLPoint) - AffineMap.const ℝ PLPoint v)
  refine ⟨f, hgu, fun p hp hpne => ?_⟩
  have hpP : p ∈ P := mem_affineSpan ℝ ⟨hp, hpne⟩
  have hpD : p - v ∈ P.direction := AffineSubspace.vsub_mem_direction hpP hvP
  exact LinearMap.congr_fun hg ⟨p - v, hpD⟩

/-- A face containing an interior point of a complex edge contains both vertices. -/
theorem openSegment_endpoints_mem_face {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.simplices.faces) {u v x : PLPoint} (he : ({v, u} : Finset PLPoint) ∈ K.edges)
    (hxs : x ∈ convexHull ℝ (s : Set PLPoint)) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : AffineMap.lineMap v u a = x) : v ∈ s ∧ u ∈ s := by
  have hne := K.edge_endpoints_ne he
  have hi := AffineMap.lineMap_injective ℝ hne.symm
  have hxv : x ≠ v := fun h => ha.1.ne' (hi (by rw [hx, h, AffineMap.lineMap_apply_zero]))
  have hxu : x ≠ u := fun h => ha.2.ne (hi (by rw [hx, h, AffineMap.lineMap_apply_one]))
  have hxE : x ∈ convexHull ℝ (({v, u} : Finset PLPoint) : Set PLPoint) := by
    rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_image_lineMap]
    exact ⟨a, ⟨ha.1.le, ha.2.le⟩, hx⟩
  have hInter := K.simplices.inter_subset_convexHull ((K.mem_edges_iff _).mp he).1 hs ⟨hxE, hxs⟩
  constructor
  · by_contra hv
    have hOnly : (({v, u} : Finset PLPoint) : Set PLPoint) ∩ (s : Set PLPoint) ⊆ {u} := by
      rintro z ⟨hz, hzs⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hv hzs).elim
      · exact Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp hz)
    exact hxu (by simpa only [convexHull_singleton, Set.mem_singleton_iff] using convexHull_mono hOnly hInter)
  · by_contra hu
    have hOnly : (({v, u} : Finset PLPoint) : Set PLPoint) ∩ (s : Set PLPoint) ⊆ {v} := by
      rintro z ⟨hz, hzs⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rfl
      · exact (hu ((Finset.mem_singleton.mp hz) ▸ hzs)).elim
    exact hxv (by simpa only [convexHull_singleton, Set.mem_singleton_iff] using convexHull_mono hOnly hInter)

private theorem mem_face_of_midpoint_mem_face {s : Finset PLPoint}
    {u v y : PLPoint} (hu : u ∈ s) (hv : v ∈ s) (hvu : v ≠ u)
    {f : PLPoint →ᵃ[ℝ] ℝ} (hfu : f u = 1) (hf : ∀ p ∈ s, p ≠ u → f p = 0)
    (hy : AffineMap.lineMap y u (1 / 2 : ℝ) ∈ convexHull ℝ (s : Set PLPoint))
    (hfy : 1 / 2 < f (AffineMap.lineMap y u (1 / 2 : ℝ))) : y ∈ convexHull ℝ (s : Set PLPoint) := by
  classical
  let S := (s : Set PLPoint) \ {u}
  have hS : S.Nonempty := ⟨v, hv, hvu⟩
  have hInsert : insert u S = (s : Set PLPoint) := by
    ext p
    simp [S, hu]
  have hZero : convexHull ℝ S ⊆ f ⁻¹' ({0} : Set ℝ) :=
    convexHull_min (fun p hp => hf p hp.1 hp.2) ((convex_singleton _).affine_preimage f)
  rw [← hInsert, convexHull_insert hS, convexJoin_comm, mem_convexJoin] at hy
  obtain ⟨p, hp, u', hu', hSeg⟩ := hy
  have hu'eq : u' = u := hu'
  subst u'
  rw [segment_eq_image_lineMap] at hSeg
  obtain ⟨a, ha, heq⟩ := hSeg
  have ha_gt : 1 / 2 < a := by
    rw [← heq, f.apply_lineMap, hZero hp, hfu] at hfy
    simpa [AffineMap.lineMap_apply_module] using hfy
  have hMid : AffineMap.lineMap (AffineMap.lineMap p u (2 * a - 1)) u (1 / 2 : ℝ) =
      AffineMap.lineMap p u a := by
    simp only [AffineMap.lineMap_apply_module]
    module
  have hInjective : Function.Injective (fun x : PLPoint => AffineMap.lineMap x u (1 / 2 : ℝ)) := by
    intro x₁ x₂ he
    simp only [AffineMap.lineMap_apply_module, add_left_inj] at he
    exact smul_right_injective PLPoint (by norm_num : (1 : ℝ) - 1 / 2 ≠ 0) he
  rw [← hInjective (hMid.trans heq)]
  apply (convex_convexHull ℝ (s : Set PLPoint)).segment_subset
    (convexHull_mono sdiff_subset hp) (subset_convexHull ℝ _ hu)
  apply lineMap_mem_segment
  exact ⟨by linarith, by linarith [ha.2]⟩

/-- If a gap in a convex set accumulates at an interior point of an edge,
it also accumulates at the midpoint toward either endpoint of that edge. -/
theorem midpoint_mem_closure_sdiff_realization_of_mem_openSegment {K : FinitePlanarComplex}
    {C : Set PLPoint} (hC : Convex ℝ C) {u v x : PLPoint} (he : ({v, u} : Finset PLPoint) ∈ K.edges)
    (huC : u ∈ C) (hx : x ∈ openSegment ℝ v u) (hxGap : x ∈ closure (C \ K.realization)) :
    AffineMap.lineMap x u (1 / 2 : ℝ) ∈ closure (C \ K.realization) := by
  let T := fun y : PLPoint => AffineMap.lineMap y u (1 / 2 : ℝ)
  have hT : Continuous T := by
    simp only [T, AffineMap.lineMap_apply_module]
    fun_prop
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨a, ha, hax⟩ := hx
  have hTx : AffineMap.lineMap v u ((1 + a) / 2) = T x := by
    rw [← hax]
    simp only [T, AffineMap.lineMap_apply_module]
    module
  have ha' : (1 + a) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hev : ∀ᶠ y in 𝓝 x, ∀ s ∈ K.simplices.faces,
      T y ∈ convexHull ℝ (s : Set PLPoint) → y ∈ convexHull ℝ (s : Set PLPoint) := by
    apply (eventually_all_finite K.finite_faces).mpr
    intro s hs
    by_cases hTxS : T x ∈ convexHull ℝ (s : Set PLPoint)
    · obtain ⟨hv, hu⟩ := openSegment_endpoints_mem_face hs he hTxS ha' hTx
      have hne := K.edge_endpoints_ne he
      obtain ⟨f, hfu, hf⟩ := exists_face_vertex_coordinate hs hu hv hne.symm
      have hfTx : (1 : ℝ) / 2 < f (T x) := by
        rw [← hTx, f.apply_lineMap, hf v hv hne.symm, hfu]
        simp only [AffineMap.lineMap_apply_module, smul_eq_mul, mul_one]
        linarith [ha.1]
      have hf_cont := f.continuous_of_finiteDimensional
      have hopen : IsOpen {y | (1 : ℝ) / 2 < f (T y)} := isOpen_lt continuous_const (hf_cont.comp hT)
      filter_upwards [hopen.mem_nhds hfTx] with y hy
      exact fun hyS => mem_face_of_midpoint_mem_face hu hv hne.symm hfu hf hyS hy
    · have hopen := ((s.finite_toSet.isClosed_convexHull ℝ).isOpen_compl.preimage hT)
      filter_upwards [hopen.mem_nhds hTxS] with y hy
      exact fun hyS => (hy hyS).elim
  apply mem_closure_iff_nhds.mpr
  intro W hW
  have hpre : T ⁻¹' W ∈ 𝓝 x := hT.continuousAt hW
  obtain ⟨y, ⟨hyW, hyFaces⟩, hyC, hyNot⟩ := mem_closure_iff_nhds.mp hxGap _ (inter_mem hpre hev)
  refine ⟨T y, hyW, (hC.segment_subset hyC huC (lineMap_mem_segment ℝ y u (by norm_num))), ?_⟩
  intro hy
  obtain ⟨s, hs, hys⟩ := (K.mem_realization_iff _).mp hy
  exact hyNot (K.convexHull_face_subset_realization s hs (hyFaces s hs hys))

/-- If the hull boundary is filled but the hull has a gap, a linear
functional separating the vertices attains its maximum over the closure of
the gap at a vertex. -/
theorem exists_vertex_maxOn_closure_hull_sdiff {K : FinitePlanarComplex}
    (hFrontier : frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization)
    {g : StrongDual ℝ PLPoint} (hg : g ≠ 0) (hgInjective : InjOn g K.simplices.vertices)
    (hGap : ¬ convexHull ℝ K.simplices.vertices ⊆ K.realization) :
    ∃ v ∈ K.simplices.vertices, v ∈ closure (convexHull ℝ K.simplices.vertices \ K.realization) ∧
      IsMaxOn g (closure (convexHull ℝ K.simplices.vertices \ K.realization)) v := by
  classical
  let C := convexHull ℝ K.simplices.vertices
  let U := C \ K.realization
  have hC : Convex ℝ C := convex_convexHull _ _
  have hCcompact : IsCompact C := K.finite_vertexSet.isCompact_convexHull ℝ
  obtain ⟨x₀, hx₀, hx₀Not⟩ := Set.not_subset.mp hGap
  have hU_cpt : IsCompact (closure U) :=
    hCcompact.of_isClosed_subset isClosed_closure (closure_minimal sdiff_subset hCcompact.isClosed)
  obtain ⟨x, hx, hMax⟩ := hU_cpt.exists_isMaxOn ⟨x₀, subset_closure ⟨hx₀, hx₀Not⟩⟩ g.continuous.continuousOn
  have hMax' : ∀ y ∈ closure U, g y ≤ g x := isMaxOn_iff.mp hMax
  have hxK : x ∈ K.realization := by
    by_contra hxNot
    have hxC : x ∈ C := closure_minimal sdiff_subset hCcompact.isClosed hx
    exact (linearFunctional_lt_maxOn_closure_of_mem_open (open_hull_sdiff hFrontier) hg hMax
      ⟨hxC, hxNot⟩).false
  obtain ⟨s, hs, hxs⟩ := exists_openFace_of_mem_realization hxK
  rcases face_card_cases hs with hs₁ | hs₂ | hs₃
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs₁
    have hxv : x = v := by simpa using hxs.1
    exact ⟨x, hxv.symm ▸ hs, hx, hMax⟩
  · obtain ⟨v, u, hvu, rfl⟩ := Finset.card_eq_two.mp hs₂
    have hV {a b : PLPoint} (hE : ({a, b} : Finset PLPoint) ∈ K.edges) : a ∈ K.simplices.vertices :=
      K.simplices.down_closed ((K.mem_edges_iff _).mp hE).1 (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
    have he : ({v, u} : Finset PLPoint) ∈ K.edges := (K.mem_edges_iff _).mpr ⟨hs, hs₂⟩
    have he' : ({u, v} : Finset PLPoint) ∈ K.edges := Finset.pair_comm v u ▸ he
    have hcontr {a b : PLPoint} (hE : ({a, b} : Finset PLPoint) ∈ K.edges)
        (hOpen : x ∈ openSegment ℝ a b) (hb : b ∈ K.simplices.vertices) (hlt : g a < g b) : False := by
      have hMid := midpoint_mem_closure_sdiff_realization_of_mem_openSegment hC hE
        (subset_convexHull ℝ _ hb) hOpen hx
      have hxlt : g x < g b := by
        rw [openSegment_eq_image_lineMap] at hOpen
        obtain ⟨t, ht, htx⟩ := hOpen
        rw [← htx, AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
        change (1 - t) * g a + t * g b < g b
        nlinarith [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hlt)]
      have hlt' : g x < g (AffineMap.lineMap x b (1 / 2 : ℝ)) := by
        rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
        change g x < (1 - 1 / 2) * g x + (1 / 2) * g b
        linarith
      exact hlt'.not_ge (hMax' _ hMid)
    have hxSeg := openFace_pair_mem_openSegment hvu hxs
    rcases lt_or_gt_of_ne (fun h => hvu (hgInjective (hV he) (hV he') h)) with hlt | hlt
    · exact (hcontr he hxSeg (hV he') hlt).elim
    · rw [openSegment_symm] at hxSeg
      exact (hcontr he' hxSeg (hV he) hlt).elim
  · have hxInt : x ∈ interior (convexHull ℝ (s : Set PLPoint)) :=
      (openFace_eq_interior_of_card_three (K.triangleOfFace s hs hs₃) (K.range_triangleOfFace s hs hs₃)) ▸ hxs
    obtain ⟨y, hy, _, hyNot⟩ := mem_closure_iff.mp hx _ isOpen_interior hxInt
    exact (hyNot (K.convexHull_face_subset_realization s hs (interior_subset hy))).elim

private theorem exists_interval_frontier_endpoints {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {γ : ℝ → X} (hγ : Continuous γ) (h0 : γ 0 ∈ U)
    (hLeft : γ (-1) ∉ closure U) (hRight : γ 1 ∉ closure U) :
    ∃ a ∈ Ioo (-1 : ℝ) 0, ∃ b ∈ Ioo (0 : ℝ) 1,
      γ a ∈ frontier U ∧ γ b ∈ frontier U ∧ ∀ t ∈ Ioo a b, γ t ∈ U := by
  let L := Icc (-1 : ℝ) 0 \ γ ⁻¹' U
  let R := Icc (0 : ℝ) 1 \ γ ⁻¹' U
  have hLc : IsCompact L := isCompact_Icc.of_isClosed_subset (isClosed_Icc.sdiff (hU.preimage hγ)) sdiff_subset
  have hRc : IsCompact R := isCompact_Icc.of_isClosed_subset (isClosed_Icc.sdiff (hU.preimage hγ)) sdiff_subset
  have hLan : (-1 : ℝ) ∈ L := ⟨by norm_num, fun h => hLeft (subset_closure h)⟩
  have hRbn : (1 : ℝ) ∈ R := ⟨by norm_num, fun h => hRight (subset_closure h)⟩
  obtain ⟨a, ha, hMax⟩ := hLc.exists_isMaxOn ⟨_, hLan⟩ continuous_id.continuousOn
  obtain ⟨b, hb, hMin⟩ := hRc.exists_isMinOn ⟨_, hRbn⟩ continuous_id.continuousOn
  have ha₀ : a < 0 := lt_of_le_of_ne ha.1.2 fun h => ha.2 (h.symm ▸ h0)
  have hb₀ : 0 < b := lt_of_le_of_ne hb.1.1 fun h => hb.2 (h ▸ h0)
  have hL (t : ℝ) (ht : t ∈ Ioo a 0) : γ t ∈ U := by
    by_contra h
    exact ht.1.not_ge (hMax (show t ∈ L from ⟨⟨ha.1.1.trans ht.1.le, ht.2.le⟩, h⟩))
  have hR (t : ℝ) (ht : t ∈ Ioo 0 b) : γ t ∈ U := by
    by_contra h
    exact ht.2.not_ge (hMin (show t ∈ R from ⟨⟨ht.1.le, ht.2.le.trans hb.1.2⟩, h⟩))
  have haCl : γ a ∈ closure U := by
    apply closure_mono (image_subset_iff.mpr hL) (image_closure_subset_closure_image hγ ?_)
    exact ⟨a, by rw [closure_Ioo ha₀.ne]; exact ⟨le_rfl, ha₀.le⟩, rfl⟩
  have hbCl : γ b ∈ closure U := by
    apply closure_mono (image_subset_iff.mpr hR) (image_closure_subset_closure_image hγ ?_)
    exact ⟨b, by rw [closure_Ioo hb₀.ne]; exact ⟨hb₀.le, le_rfl⟩, rfl⟩
  refine ⟨a, ⟨lt_of_le_of_ne ha.1.1 fun h => hLeft (h.symm ▸ haCl), ha₀⟩,
    b, ⟨hb₀, lt_of_le_of_ne hb.1.2 fun h => hRight (h ▸ hbCl)⟩,
    ⟨haCl, fun h => ha.2 (show γ a ∈ U from interior_subset h)⟩,
    ⟨hbCl, fun h => hb.2 (show γ b ∈ U from interior_subset h)⟩, ?_⟩
  intro t ht
  rcases lt_trichotomy t 0 with h | rfl | h
  · exact hL t ⟨ht.1, h⟩
  · exact h0
  · exact hR t ⟨h, ht.2⟩

/-- A two-segment path from `v - n` to `v + n` through a nearby gap point `p`. -/
def vertexGapPath (v p n : PLPoint) (t : ℝ) : PLPoint :=
  v + ((1 - |t|) • (p - v) + t • n)

private theorem exists_kernel_vector_of_norm (g : StrongDual ℝ PLPoint) {r : ℝ} (hr : 0 < r) :
    ∃ n : PLPoint, g n = 0 ∧ ‖n‖ = r := by
  have hRank := g.toLinearMap.finrank_range_add_finrank_ker
  rw [finrank_euclideanSpace_fin] at hRank
  have hRange : Module.finrank ℝ g.toLinearMap.range ≤ 1 := by simpa using Submodule.finrank_le g.toLinearMap.range
  have hK : 0 < Module.finrank ℝ g.toLinearMap.ker := by omega
  let _ : Nontrivial g.toLinearMap.ker := (Module.finrank_pos_iff_of_free ℝ _).mp hK
  obtain ⟨d, hd⟩ := exists_ne (0 : g.toLinearMap.ker)
  have hd' : (d : PLPoint) ≠ 0 := fun h => hd (Subtype.ext h)
  have hNorm := norm_pos_iff.mpr hd'
  refine ⟨(r / ‖(d : PLPoint)‖) • (d : PLPoint), ?_, ?_⟩
  · rw [map_smul, show g (d : PLPoint) = 0 from LinearMap.mem_ker.mp d.property, smul_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.le hNorm.le), div_mul_cancel₀ _ hNorm.ne']

/-- At a vertex maximizing a separating functional over the closure of a
hull gap, a short path around the vertex crosses a gap interval whose
endpoints lie in two incident open edges. -/
theorem exists_gap_interval_between_incident_edges {K : FinitePlanarComplex}
    (hFrontier : frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization)
    {v : PLPoint} (hv : v ∈ K.simplices.vertices)
    (hvGap : v ∈ closure (convexHull ℝ K.simplices.vertices \ K.realization))
    {g : StrongDual ℝ PLPoint} (hg : g ≠ 0) (hgInjective : InjOn g K.simplices.vertices)
    (hMax : IsMaxOn g (closure (convexHull ℝ K.simplices.vertices \ K.realization)) v) :
    ∃ p n : PLPoint, g p < g v ∧ g n = 0 ∧ ‖n‖ = K.vertexFaceSeparation / 2 ∧
      ∃ a ∈ Ioo (-1 : ℝ) 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∃ u w : PLPoint,
        ({v,u} : Finset PLPoint) ∈ K.edges ∧ ({v,w} : Finset PLPoint) ∈ K.edges ∧
        vertexGapPath v p n a ∈ openSegment ℝ v u ∧ vertexGapPath v p n b ∈ openSegment ℝ v w ∧
        (∀ t ∈ Ioo a b, vertexGapPath v p n t ∈ convexHull ℝ K.simplices.vertices \ K.realization) ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, dist (vertexGapPath v p n t) v < K.vertexFaceSeparation := by
  let U := convexHull ℝ K.simplices.vertices \ K.realization
  let M := K.vertexFaceSeparation
  have hM : 0 < M := K.vertexFaceSeparation_pos
  have hU : IsOpen U := open_hull_sdiff hFrontier
  obtain ⟨p, hpB, hpU⟩ := mem_closure_iff.mp hvGap (Metric.ball v (M / 2)) Metric.isOpen_ball
    (Metric.mem_ball_self (half_pos hM))
  have hp : g p < g v := linearFunctional_lt_maxOn_closure_of_mem_open hU hg hMax hpU
  obtain ⟨n, hn, hNorm⟩ := exists_kernel_vector_of_norm g (half_pos hM)
  let γ := vertexGapPath v p n
  have hγ : Continuous γ := by
    change Continuous (fun t : ℝ => v + ((1 - |t|) • (p - v) + t • n))
    fun_prop
  have hγ0 : γ 0 ∈ U := by
    have hzero : γ 0 = p := by simp [γ, vertexGapPath]
    rw [hzero]
    exact hpU
  have hBound (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : dist (γ t) v < M := by
    have habs : |t| ≤ 1 := abs_le.mpr ht
    have ht' : 0 ≤ 1 - |t| := sub_nonneg.mpr habs
    have hp' : ‖p - v‖ ≤ M / 2 := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hpB).le
    rw [dist_eq_norm]
    change ‖v + ((1 - |t|) • (p - v) + t • n) - v‖ < M
    rw [add_sub_cancel_left]
    calc
      _ ≤ ‖(1 - |t|) • (p - v)‖ + ‖t • n‖ := norm_add_le _ _
      _ = (1 - |t|) * ‖p-v‖ + |t| * (M/2) := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ht', hNorm]
      _ ≤ (1 - |t|) * (M/2) + |t| * (M/2) := add_le_add (mul_le_mul_of_nonneg_left hp' ht') le_rfl
      _ = M/2 := by ring
      _ < M := by linarith
  have hHeight (t : ℝ) : g (γ t) = g v + (1 - |t|) * (g p - g v) := by
    simp [γ, vertexGapPath, map_add, map_sub, map_smul, hn]
  have hHorizontal (x : PLPoint) (hx : dist x v < M) (hxne : x ≠ v) (h : g x = g v) :
      x ∉ closure U := by
    intro hxC
    have hxU : x ∉ U := fun hh => (linearFunctional_lt_maxOn_closure_of_mem_open hU hg hMax hh).ne h
    have hxFr : x ∈ frontier U := ⟨hxC, fun hh => hxU (interior_subset hh)⟩
    obtain ⟨u, he, hxu⟩ := exists_incident_edge_of_mem_frontier_hull_sdiff hFrontier hv hxFr hx hxne
    have hu : u ∈ K.simplices.vertices := K.simplices.down_closed ((K.mem_edges_iff _).mp he).1
      (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
    rw [openSegment_eq_image_lineMap] at hxu
    obtain ⟨a, ha, hax⟩ := hxu
    have hgu : g u = g v := by
      rw [← hax, AffineMap.lineMap_apply_module, map_add, map_smul, map_smul] at h
      change (1-a) * g v + a * g u = g v at h
      have hZero : a * (g u - g v) = 0 := by linarith only [h, mul_sub a (g u) (g v), sub_mul 1 a (g v)]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_left ha.1.ne')
    exact K.edge_endpoints_ne he (hgInjective hu hv hgu)
  have hEnd (t : ℝ) (ht : |t| = 1) : γ t ∉ closure U := by
    have hne : γ t ≠ v := by
      have htn : t ≠ 0 := by intro h; simp [h] at ht
      have hnz : n ≠ 0 := fun h => (half_pos hM).ne' (by simpa [h] using hNorm.symm)
      simpa [γ, vertexGapPath, ht] using smul_ne_zero htn hnz
    exact hHorizontal (γ t) (hBound t (abs_le.mp ht.le)) hne (by simp [hHeight, ht])
  obtain ⟨a, ha, b, hb, haFr, hbFr, hIn⟩ := exists_interval_frontier_endpoints hU hγ hγ0
    (hEnd (-1) (by norm_num)) (hEnd 1 (by norm_num))
  have hOpenEdge (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) (htFr : γ t ∈ frontier U) :
      ∃ u, ({v,u} : Finset PLPoint) ∈ K.edges ∧ γ t ∈ openSegment ℝ v u := by
    have hStrict : g (γ t) < g v := by
      rw [hHeight]
      have ht' : 0 < 1 - |t| := sub_pos.mpr (abs_lt.mpr ht)
      linarith [mul_neg_of_pos_of_neg ht' (sub_neg.mpr hp)]
    exact exists_incident_edge_of_mem_frontier_hull_sdiff hFrontier hv htFr (hBound t ⟨ht.1.le, ht.2.le⟩)
      (fun h => hStrict.ne (congrArg g h))
  obtain ⟨u, hu, hau⟩ := hOpenEdge a ⟨ha.1, ha.2.trans (by norm_num)⟩ haFr
  obtain ⟨w, hw, hbw⟩ := hOpenEdge b ⟨(by norm_num : (-1 : ℝ) < 0).trans hb.1, hb.2⟩ hbFr
  exact ⟨p, n, hp, hn, hNorm, a, ha, b, hb, u, w, hu, hw, hau, hbw, hIn, hBound⟩

end FinitePlanarComplex
