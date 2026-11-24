import SteinerProof.ArrowheadInclusion

/-! Nearest-point arguments for the reverse arrowhead characterization. -/

open Set
open InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

/-- A point of the extended body is at least one radius away from every
frontier point of the doubled offset. -/
theorem le_dist_of_mem_frontier_offset_of_mem_extendedBody {A : Set PLPoint}
    {r : ℝ} {x z : PLPoint} (hx : x ∈ extendedBody A r)
    (hz : z ∈ frontier (offset A (2 * r))) : r ≤ dist x z := by
  by_contra! h
  have hzBall : z ∈ Metric.ball x r := Metric.mem_ball.mpr (by simpa [dist_comm] using h)
  have hzCompl : z ∈ closure (offset A (2 * r))ᶜ :=
    by rw [frontier_eq_closure_inter_closure] at hz; exact hz.2
  obtain ⟨y, hy, hyOut⟩ := mem_closure_iff.mp hzCompl _ Metric.isOpen_ball hzBall
  exact hyOut (extendedBody_subset_erosion A r hx (Metric.ball_subset_closedBall hy))

private theorem infDist_along_nearest_vertex_ray
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {x v : PLPoint} (hv : v ∈ A.simplices.vertices) (hδ : 0 < dist x v)
    (hmin : Metric.infDist x A.realization = dist x v)
    {t : ℝ} (ht : 0 ≤ t) (htM : t ≤ K.vertexFaceSeparation / 2) :
    Metric.infDist (v + (t / dist x v) • (x-v)) A.realization = t := by
  let z := v + (t / dist x v) • (x-v)
  have hvR : v ∈ A.realization := A.simplices.vertices_subset_space hv
  have hvK : v ∈ K.simplices.vertices := hAK hv
  have hzv : dist z v = t := by
    rw [dist_eq_norm, show z - v = (t / dist x v) • (x-v) from add_sub_cancel_left _ _,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht hδ.le), ← dist_eq_norm,
      div_mul_cancel₀ _ hδ.ne']
  refine le_antisymm ((Metric.infDist_le_dist_of_mem hvR).trans_eq hzv) ?_
  apply (Metric.le_infDist ⟨v, hvR⟩).mpr
  intro a ha
  obtain ⟨s, hs, has⟩ := (A.mem_realization_iff a).mp ha
  by_cases hvs : v ∈ s
  · let F := convexHull ℝ (s : Set PLPoint)
    have hvF : v ∈ F := subset_convexHull ℝ _ hvs
    have hF : F ⊆ A.realization := A.convexHull_face_subset_realization s hs
    have hproj : Metric.infDist x F = dist x v := by
      refine le_antisymm (Metric.infDist_le_dist_of_mem hvF) ?_
      rw [← hmin]
      exact Metric.infDist_le_infDist_of_subset hF ⟨v, hvF⟩
    have hnormal := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) hvF).mp
      (show ‖x-v‖ = ⨅ w : F, ‖x - w‖ from by
        simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hproj.symm)
    have hzproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) (u := z) hvF).mpr
      (fun w hw => by
        rw [show z-v = (t / dist x v) • (x-v) from add_sub_cancel_left _ _,
          real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht hδ.le) (hnormal w hw))
    have hzmin : Metric.infDist z F = dist z v := by
      simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hzproj.symm
    exact hzv.symm.le.trans (hzmin.symm.le.trans (Metric.infDist_le_dist_of_mem has))
  · have hsep := K.vertexFaceSeparation_le_dist hvK (hAK hs) hvs has
    have htri := dist_triangle v z a
    rw [dist_comm v z, hzv] at htri
    linarith

/-- The nearest-vertex lemma of Section 4. The radial point at distance
`2r` from the vertex lies on the doubled-offset frontier. -/
theorem exists_near_frontier_of_nearest_vertex
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    {x v : PLPoint} (hv : v ∈ A.simplices.vertices)
    (hmin : Metric.infDist x A.realization = dist x v)
    (hδ₁ : r < dist x v) (hδ₂ : dist x v ≤ 2 * r) :
    ∃ z ∈ frontier (offset A.realization (2 * r)), dist x z < r := by
  let δ := dist x v
  let f (t : ℝ) := v + (t / δ) • (x-v)
  have hδ : 0 < δ := hr.trans hδ₁
  have hM : 2 * r < K.vertexFaceSeparation / 2 := by
    linarith [hR.trans_le K.admissibleRadius_le, K.vertexFaceSeparation_pos]
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hvR : v ∈ A.realization := A.simplices.vertices_subset_space hv
  have hdist (t : ℝ) (ht : 0 ≤ t) (htM : t ≤ K.vertexFaceSeparation / 2) :
      Metric.infDist (f t) A.realization = t :=
    infDist_along_nearest_vertex_ray hAK hv hδ hmin ht htM
  refine ⟨f (2 * r), ?_, ?_⟩
  · rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure ⟨⟨v, hvR⟩, (hdist _ (by positivity) hM.le).le⟩, ?_⟩
    have hsubset : f '' Ioo (2 * r) (K.vertexFaceSeparation / 2) ⊆
        (offset A.realization (2 * r))ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ ho
      have h := hdist t (by linarith [ht.1]) ht.2.le
      exact (not_le_of_gt ht.1) (h ▸ ho.2)
    apply closure_mono hsubset (image_closure_subset_closure_image hf ?_)
    refine ⟨2 * r, ?_, rfl⟩
    rw [closure_Ioo hM.ne]
    exact left_mem_Icc.mpr hM.le
  · have h : f (2 * r) - x = ((2 * r - δ) / δ) • (x-v) := by
      have hsc : (2 * r - δ) / δ = 2 * r / δ - 1 := by
        rw [sub_div, div_self hδ.ne']
      rw [hsc, sub_smul, one_smul]
      dsimp [f]
      abel
    rw [dist_comm x, dist_eq_norm, h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sub_nonneg.mpr hδ₂) hδ.le)]
    change (2 * r - δ) / δ * δ < r
    rw [div_mul_cancel₀ _ hδ.ne']
    linarith

/-- A point added by the extension has a nearest point in the open part of
an edge of the original complex. -/
theorem exists_nearest_open_edge_of_mem_extendedBody_sdiff_offset
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) {x : PLPoint}
    (hx : x ∈ extendedBody A.realization r \ offset A.realization r) :
    ∃ p e, e ∈ A.edges ∧ p ∈ FinitePlanarComplex.openFace e ∧
      Metric.infDist x A.realization = dist x p := by
  have h₂ := extendedBody_subset_offset_twice _ _ hr.le hx.1
  have hA : A.realization.Nonempty := h₂.1
  have hδ : r < Metric.infDist x A.realization := lt_of_not_ge (fun h => hx.2 ⟨hA, h⟩)
  have hxA : x ∉ A.realization := by
    intro h
    rw [Metric.infDist_zero_of_mem h] at hδ
    linarith
  obtain ⟨p, s, hs, hcard, hp, hmin⟩ :=
    FinitePlanarComplex.exists_nearest_openFace_card_le_two hA hxA
  refine ⟨p, s, (A.mem_edges_iff s).mpr ⟨hs, ?_⟩, hp, hmin⟩
  by_contra hn
  have hpos := Finset.card_pos.mpr (A.simplices.nonempty_of_mem_faces hs)
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
  have hpv : p = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hp.1
  subst p
  have h₂' : Metric.infDist x A.realization ≤ 2 * r := h₂.2
  rw [hmin] at h₂' hδ
  obtain ⟨z, hz, hzclose⟩ := exists_near_frontier_of_nearest_vertex hAK hr hR hs hmin hδ h₂'
  exact (not_lt_of_ge (le_dist_of_mem_frontier_offset_of_mem_extendedBody hx.1 hz)) hzclose

private theorem inner_eq_zero_of_nearest_mem_openSegment {x p v w : PLPoint}
    (hp : p ∈ openSegment ℝ v w) (hmin : Metric.infDist x (segment ℝ v w) = dist x p) :
    ⟪x-p, w-v⟫ = 0 := by
  have hnormal := (norm_eq_iInf_iff_real_inner_le_zero (convex_segment v w)
    (openSegment_subset_segment ℝ v w hp)).mp
    (show ‖x-p‖ = ⨅ a : segment ℝ v w, ‖x-a‖ from by
      simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hmin.symm)
  obtain ⟨t, ⟨ht₀, ht₁⟩, htp⟩ := (openSegment_eq_image_lineMap ℝ v w) ▸ hp
  have hvsub : v - p = (-t) • (w-v) := by
    rw [← htp, AffineMap.lineMap_apply_module', neg_smul]
    abel
  have hwsub : w - p = (1 - t) • (w-v) := by
    rw [← htp, AffineMap.lineMap_apply_module', sub_smul, one_smul]
    abel
  have hleft := hnormal v (left_mem_segment ℝ v w)
  have hright := hnormal w (right_mem_segment ℝ v w)
  rw [hvsub, real_inner_smul_right] at hleft
  rw [hwsub, real_inner_smul_right] at hright
  exact le_antisymm
    (le_of_not_gt (fun hn => (not_lt_of_ge hright) (mul_pos (sub_pos.mpr ht₁) hn)))
    (le_of_not_gt (fun hn => (not_lt_of_ge hleft) (mul_pos_of_neg_of_neg (neg_neg_of_pos ht₀) hn)))

private theorem exists_endpoint_minimizing_pair {v w a b : PLPoint}
    (hvw : v ≠ w) (hab : a ≠ b) (hdisj : Disjoint (segment ℝ v w) (segment ℝ a b)) :
    ∃ p ∈ segment ℝ v w, ∃ q ∈ segment ℝ a b,
      (p = v ∨ p = w ∨ q = a ∨ q = b) ∧
      ∀ x ∈ segment ℝ v w, ∀ y ∈ segment ℝ a b, dist p q ≤ dist x y := by
  let I := Icc (0 : ℝ) 1
  let f : ℝ →ᵃ[ℝ] PLPoint := AffineMap.lineMap v w
  let g : ℝ →ᵃ[ℝ] PLPoint := AffineMap.lineMap a b
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hfc : ∀ t ∈ I, f t ∈ segment ℝ v w := fun t ht =>
    (segment_eq_image_lineMap ℝ v w).symm ▸ ⟨t, ht, rfl⟩
  have hgc : ∀ t ∈ I, g t ∈ segment ℝ a b := fun t ht =>
    (segment_eq_image_lineMap ℝ a b).symm ▸ ⟨t, ht, rfl⟩
  let D (z : ℝ × ℝ) := dist (f z.1) (g z.2)
  have hD : Continuous D := (hf.comp continuous_fst).dist (hg.comp continuous_snd)
  obtain ⟨⟨s, t⟩, ⟨hs, ht⟩, hmin⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (I ×ˢ I)).exists_isMinOn (show (I ×ˢ I).Nonempty from ⟨(0, 0), by norm_num [I]⟩)
      hD.continuousOn
  let p := f s
  let q := g t
  have hp := hfc s hs
  have hq := hgc t ht
  have hle (x) (hx : x ∈ segment ℝ v w) (y) (hy : y ∈ segment ℝ a b) :
      dist p q ≤ dist x y := by
    obtain ⟨s', hs', rfl⟩ := (segment_eq_image_lineMap ℝ v w) ▸ hx
    obtain ⟨t', ht', rfl⟩ := (segment_eq_image_lineMap ℝ a b) ▸ hy
    exact isMinOn_iff.mp hmin (s', t') (show (s', t') ∈ I ×ˢ I from ⟨hs', ht'⟩)
  have hfinish (s' t' : ℝ) (hs' : s' ∈ I) (ht' : t' ∈ I)
      (he : s' = 0 ∨ s' = 1 ∨ t' = 0 ∨ t' = 1) (hd : dist (f s') (g t') = dist p q) :
      ∃ p ∈ segment ℝ v w, ∃ q ∈ segment ℝ a b,
        (p = v ∨ p = w ∨ q = a ∨ q = b) ∧
        ∀ x ∈ segment ℝ v w, ∀ y ∈ segment ℝ a b, dist p q ≤ dist x y := by
    refine ⟨f s', hfc s' hs', g t', hgc t' ht', ?_, fun x hx y hy => hd ▸ hle x hx y hy⟩
    rcases he with h | h | h | h
    · exact Or.inl (by simp [f, h])
    · exact Or.inr (Or.inl (by simp [f, h]))
    · exact Or.inr (Or.inr (Or.inl (by simp [g, h])))
    · exact Or.inr (Or.inr (Or.inr (by simp [g, h])))
  by_cases he : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1
  · exact hfinish s t hs ht he rfl
  push Not at he
  have hsOpen : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 he.1.symm, lt_of_le_of_ne hs.2 he.2.1⟩
  have htOpen : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 he.2.2.1.symm, lt_of_le_of_ne ht.2 he.2.2.2⟩
  have hpo : p ∈ openSegment ℝ v w := (openSegment_eq_image_lineMap ℝ v w).symm ▸ ⟨s, hsOpen, rfl⟩
  have hqo : q ∈ openSegment ℝ a b := (openSegment_eq_image_lineMap ℝ a b).symm ▸ ⟨t, htOpen, rfl⟩
  have hpmin : Metric.infDist q (segment ℝ v w) = dist q p := by
    refine le_antisymm (Metric.infDist_le_dist_of_mem hp) ((Metric.le_infDist ⟨p, hp⟩).mpr ?_)
    intro x hx
    simpa only [dist_comm q p, dist_comm q x] using hle x hx q hq
  have hqmin : Metric.infDist p (segment ℝ a b) = dist p q :=
    le_antisymm (Metric.infDist_le_dist_of_mem hq) ((Metric.le_infDist ⟨q, hq⟩).mpr (hle p hp))
  have h₀ := inner_eq_zero_of_nearest_mem_openSegment hpo hpmin
  have h₁ := inner_eq_zero_of_nearest_mem_openSegment hqo hqmin
  have h₁' : ⟪q-p, b-a⟫ = 0 := by rw [← neg_sub p q, inner_neg_left, h₁, neg_zero]
  have hdep : ¬ LinearIndependent ℝ ![w-v, b-a] := by
    intro hind
    let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
    have hB : (B : Fin 2 → PLPoint) = ![w-v, b-a] :=
      coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have hd := B.sum_repr (q-p)
    rw [Fin.sum_univ_two, hB] at hd
    change B.repr (q-p) 0 • (w-v) + B.repr (q-p) 1 • (b-a) = q-p at hd
    have hz : ⟪q-p, q-p⟫ = 0 := calc
      _ = ⟪q-p, B.repr (q-p) 0 • (w-v) + B.repr (q-p) 1 • (b-a)⟫ :=
        congrArg (fun z : PLPoint => ⟪q-p, z⟫) hd.symm
      _ = 0 := by simp only [inner_add_right, real_inner_smul_right, h₀, h₁', mul_zero, add_zero]
    have heq := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
    have hq' : p ∈ segment ℝ a b := by rwa [← heq]
    exact Set.disjoint_left.mp hdisj hp hq'
  rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr hvw.symm)] at hdep
  push Not at hdep
  obtain ⟨c, hc⟩ := hdep
  have hc₀ : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hab (sub_eq_zero.mp hc.symm).symm
  let T : ℝ := if 0 < c then 1 else 0
  let k := c * (T - t)
  have hT : T ∈ I ∧ (T = 0 ∨ T = 1) := by
    dsimp [T, I]
    split <;> norm_num
  have hk : 0 < k := by
    dsimp [k, T]
    split
    · exact mul_pos ‹0 < c› (sub_pos.mpr htOpen.2)
    · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt ‹¬ 0 < c›) hc₀)
        (sub_neg.mpr htOpen.1)
  let d := min (1 - s) k
  have hd : 0 ≤ d := le_min (sub_nonneg.mpr hs.2) hk.le
  let s' := s + d
  let t' := t + (d / k) * (T - t)
  have hs' : s' ∈ I := by
    have := min_le_left (1 - s) k
    exact ⟨by dsimp [s']; linarith [hs.1], by dsimp [s', d]; linarith⟩
  have ht' : t' ∈ I := by
    have hα := div_nonneg hd hk.le
    have hβ := (div_le_one hk).mpr (min_le_right (1-s) k)
    have hh := convex_Icc (0 : ℝ) 1 ht hT.1 (sub_nonneg.mpr hβ) hα (by ring : 1 - d / k + d / k = 1)
    convert hh using 1 <;> simp [t', smul_eq_mul] <;> ring
  have hshift : c * ((d / k) * (T - t)) = d := by
    calc
      _ = (d / k) * k := by dsimp [k]; ring
      _ = d := div_mul_cancel₀ _ hk.ne'
  apply hfinish s' t' hs' ht'
  · rcases min_choice (1-s) k with heq | heq
    · exact Or.inr (Or.inl (by dsimp [s', d]; linarith))
    · have heq' : t' = T := by dsimp [t', d]; rw [heq, div_self hk.ne', one_mul]; ring
      exact Or.inr (Or.inr (by simpa only [heq'] using hT.2))
  · rw [dist_eq_norm, dist_eq_norm]
    congr 1
    dsimp [p, q, f, g, s', t']
    simp only [AffineMap.lineMap_apply_module', add_smul, ← hc, smul_smul]
    rw [add_mul, mul_comm ((d / k) * (T - t)) c, hshift, add_smul]
    abel

/-- Points on two disjoint edges are separated by the complex's vertex-face bound. -/
theorem edge_separation_of_disjoint {K : FinitePlanarComplex} {v w a b p q : PLPoint}
    (he : ({v, w} : Finset PLPoint) ∈ K.edges) (hf : ({a, b} : Finset PLPoint) ∈ K.edges)
    (hdisj : Disjoint ({v, w} : Finset PLPoint) {a, b})
    (hp : p ∈ segment ℝ v w) (hq : q ∈ segment ℝ a b) : K.vertexFaceSeparation ≤ dist p q := by
  have heF := ((K.mem_edges_iff _).mp he).1
  have hfF := ((K.mem_edges_iff _).mp hf).1
  have heHull : convexHull ℝ (({v,w} : Finset PLPoint) : Set PLPoint) = segment ℝ v w := by
    simp only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair]
  have hfHull : convexHull ℝ (({a,b} : Finset PLPoint) : Set PLPoint) = segment ℝ a b := by
    simp only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair]
  have hseg : Disjoint (segment ℝ v w) (segment ℝ a b) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← heHull, ← hfHull,
      K.simplices.convexHull_inter_convexHull heF hfF, ← Finset.coe_inter,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.coe_empty, convexHull_empty]
  obtain ⟨p', hp', q', hq', hEndpoint, hMin⟩ := exists_endpoint_minimizing_pair
    (FinitePlanarComplex.edge_endpoints_ne he).symm (FinitePlanarComplex.edge_endpoints_ne hf).symm hseg
  refine le_trans ?_ (hMin p hp q hq)
  have hvertex {x y : PLPoint} {s t : Finset PLPoint}
      (hs : s ∈ K.simplices.faces) (ht : t ∈ K.simplices.faces)
      (hst : Disjoint s t) (hx : x ∈ s) (hy : y ∈ convexHull ℝ (t : Set PLPoint)) :
      K.vertexFaceSeparation ≤ dist x y := by
    have hxV : x ∈ K.simplices.vertices := by
      rw [K.simplices.vertices_eq]
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hx⟩
    exact K.vertexFaceSeparation_le_dist hxV ht (fun h => Finset.disjoint_left.mp hst hx h) hy
  have hpHull := heHull.symm ▸ hp'
  have hqHull := hfHull.symm ▸ hq'
  rcases hEndpoint with rfl | rfl | rfl | rfl
  · exact hvertex heF hfF hdisj (by simp) hqHull
  · exact hvertex heF hfF hdisj (by simp) hqHull
  · rw [dist_comm]
    exact hvertex hfF heF hdisj.symm (by simp) hpHull
  · rw [dist_comm]
    exact hvertex hfF heF hdisj.symm (by simp) hpHull

/-- A nearest point in the open part of an edge is in its relative
interior, and the displacement to the exterior point is normal to the edge. -/
theorem nearest_open_edge_is_perpendicular {A : FinitePlanarComplex}
    {x p v w : PLPoint} (hv : v ≠ w)
    (he : ({v, w} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v, w} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p) :
    p ∈ openSegment ℝ v w ∧ ⟪x-p, w-v⟫ = 0 := by
  have hseg : segment ℝ v w ⊆ A.realization := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      A.convexHull_face_subset_realization _ ((A.mem_edges_iff _).mp he).1
  have hpOpen := FinitePlanarComplex.openFace_pair_mem_openSegment hv hp
  have hpSeg := openSegment_subset_segment ℝ v w hpOpen
  refine ⟨hpOpen, inner_eq_zero_of_nearest_mem_openSegment hpOpen ?_⟩
  refine le_antisymm (Metric.infDist_le_dist_of_mem hpSeg) ?_
  rw [← hmin]
  exact Metric.infDist_le_infDist_of_subset hseg ⟨p, hpSeg⟩

/-- The outward probe used in the incident-edge localization lies in the
doubled offset, although its distance to the original edge exceeds `2r`. -/
theorem outward_probe_of_nearest_open_edge {A : FinitePlanarComplex}
    {x p v w : PLPoint} (hvw : v ≠ w)
    (he : ({v, w} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v, w} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : ε < dist x p - r)
    (hδ₂ : dist x p ≤ 2 * r) (hx : x ∈ extendedBody A.realization r) :
    let y := p + ((2 * r + ε) / dist x p) • (x-p)
    y ∈ offset A.realization (2 * r) ∧ dist y x < r ∧ dist y p = 2 * r + ε ∧
      Metric.infDist y (segment ℝ v w) = 2 * r + ε := by
  obtain ⟨hOpen, hnormal⟩ := nearest_open_edge_is_perpendicular hvw he hp hmin
  let δ := dist x p
  let t := (2 * r + ε) / δ
  let y := p + t • (x-p)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ht : 0 < t := div_pos (by linarith) hδ
  have htδ : t * δ = 2 * r + ε := div_mul_cancel₀ _ hδ.ne'
  have ht₁ : 1 ≤ t := (le_div_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hyvec : y - p = t • (x-p) := add_sub_cancel_left _ _
  have hyx : dist y x = (t - 1) * δ := by
    have heq : y - x = (t - 1) • (x-p) := by
      rw [sub_smul, one_smul]
      dsimp [y]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁)]
    rfl
  have hyClose : dist y x < r := by
    rw [hyx, sub_mul, htδ, one_mul]
    dsimp [δ]
    linarith
  have hyOff := extendedBody_subset_erosion _ _ hx (Metric.mem_closedBall.mpr hyClose.le)
  have hyp : dist y p = 2 * r + ε := by
    rw [dist_eq_norm, hyvec, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
    exact htδ
  refine ⟨hyOff, hyClose, hyp, ?_⟩
  have hpSeg := openSegment_subset_segment ℝ v w hOpen
  obtain ⟨a, _, hap⟩ : p ∈ AffineMap.lineMap v w '' Icc (0 : ℝ) 1 := by
    rwa [← segment_eq_image_lineMap]
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_segment v w) (u := y) hpSeg).mpr
    (fun z hz => by
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨b, _, rfl⟩ := hz
      have hzp : AffineMap.lineMap v w b - p = (b-a) • (w-v) := by
        rw [← hap, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', sub_smul]
        abel
      rw [hyvec, hzp, real_inner_smul_left, real_inner_smul_right, hnormal, mul_zero, mul_zero])
  have heq : Metric.infDist y (segment ℝ v w) = ‖y-p‖ := by
    simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hproj.symm
  rwa [heq, ← dist_eq_norm]

private theorem exists_openFace_near_probe {A : FinitePlanarComplex}
    {x y : PLPoint} {r : ℝ} (hr : 0 < r) (hx : x ∉ A.realization)
    (hy : y ∈ offset A.realization (2 * r)) (hyx : dist y x < r) :
    ∃ q s, s ∈ A.simplices.faces ∧ s.card ≤ 2 ∧ q ∈ FinitePlanarComplex.openFace s ∧
      dist y q ≤ 2 * r ∧ (q ∈ segment ℝ x y ∨ Metric.infDist y A.realization = dist y q) := by
  by_cases hyA : y ∈ A.realization
  · have hC := A.isClosed_realization
    have hCross : (segment ℝ x y ∩ frontier A.realization).Nonempty := by
      by_contra h
      have hsub : segment ℝ x y ⊆ A.realizationᶜ := by
        apply (convex_segment x y).isPreconnected.subset_of_closure_inter_subset hC.isOpen_compl
          ⟨x, left_mem_segment ℝ x y, hx⟩
        rintro z ⟨hzCl, hzSeg⟩
        by_contra hzOut
        have hzFr : z ∈ frontier A.realization := by
          rw [← frontier_compl A.realization, hC.isOpen_compl.frontier_eq]
          exact ⟨hzCl, hzOut⟩
        exact h ⟨z, hzSeg, hzFr⟩
      exact hsub (right_mem_segment ℝ x y) hyA
    obtain ⟨q, hqSeg, hqFr⟩ := hCross
    obtain ⟨s, hs, hq⟩ := FinitePlanarComplex.exists_openFace_of_mem_realization (hC.frontier_subset hqFr)
    have hsCard : s.card ≤ 2 := by
      have h := (A.simplices.indep hs).card_le_finrank_succ
      have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
      simp only [Fintype.card_coe] at h
      rw [finrank_euclideanSpace_fin] at hdim
      by_contra! hlarge
      have hcard : s.card = 3 := by omega
      rw [FinitePlanarComplex.openFace_eq_interior_of_card_three (A.triangleOfFace s hs hcard)
        (A.range_triangleOfFace s hs hcard)] at hq
      rw [hC.frontier_eq] at hqFr
      exact hqFr.2 (interior_mono (A.convexHull_face_subset_realization _ hs) hq)
    have hdist := Metric.mem_closedBall.mp (segment_subset_closedBall_right x y hqSeg)
    refine ⟨q, s, hs, hsCard, hq, ?_, Or.inl hqSeg⟩
    rw [dist_comm x y] at hdist
    rw [dist_comm y q]
    linarith
  · obtain ⟨q, s, hs, hcard, hq, hmin⟩ := FinitePlanarComplex.exists_nearest_openFace_card_le_two hy.1 hyA
    exact ⟨q, s, hs, hcard, hq, hmin ▸ hy.2, Or.inr hmin⟩

/-- Each sufficiently short outward probe locates another edge meeting the
edge on which the nearest point lies. The witness lies on the probe segment
if the probe reaches the realization, and is a nearest point otherwise. -/
theorem exists_incident_edge_near_outward_probe {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v w x p : PLPoint}
    (he : ({v, w} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v, w} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r ε : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hε : 0 < ε) (hεR : ε < K.admissibleRadius - r) (hεδ : ε < dist x p - r)
    (hx : x ∈ extendedBody A.realization r) :
    let y := p + ((2 * r + ε) / dist x p) • (x-p)
    ∃ q a b : PLPoint, ({a,b} : Finset PLPoint) ∈ A.edges ∧
      ({a,b} : Finset PLPoint) ≠ {v,w} ∧ ¬ Disjoint ({v,w} : Finset PLPoint) {a,b} ∧
      q ∈ openSegment ℝ a b ∧ dist y q ≤ 2 * r ∧
      (q ∈ segment ℝ x y ∨ ⟪y-q, b-a⟫ = 0) := by
  let y := p + ((2 * r + ε) / dist x p) • (x-p)
  have hvw := (FinitePlanarComplex.edge_endpoints_ne he).symm
  have hδ₂ : dist x p ≤ 2 * r := hmin ▸ (extendedBody_subset_offset_twice _ _ hr.le hx).2
  obtain ⟨hy, hyx, hyp, hySeg⟩ := outward_probe_of_nearest_open_edge hvw he hp hmin hr hε hεδ hδ₂ hx
  have hxA : x ∉ A.realization := by
    intro h
    rw [Metric.infDist_zero_of_mem h] at hmin
    linarith
  obtain ⟨q, s, hs, hsCard, hq, hyq, hqCase⟩ := exists_openFace_near_probe hr hxA hy hyx
  have hpSeg := openSegment_subset_segment ℝ v w (FinitePlanarComplex.openFace_pair_mem_openSegment hvw hp)
  have hqNot : q ∉ segment ℝ v w := by
    intro h
    have h' := Metric.infDist_le_dist_of_mem (x := y) h
    rw [hySeg] at h'
    linarith
  have hclose : dist p q < K.vertexFaceSeparation := by
    have h := dist_triangle p y q
    rw [dist_comm p y, hyp] at h
    linarith [K.admissibleRadius_le, K.vertexFaceSeparation_pos]
  have heF := (A.mem_edges_iff _).mp he
  have hcard : s.card = 2 := by
    by_contra hn
    have hpos := Finset.card_pos.mpr (A.simplices.nonempty_of_mem_faces hs)
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
    have hzq : q = z := by
      simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hq.1
    subst q
    have hz : z ∉ ({v,w} : Finset PLPoint) := by
      intro hz
      apply hqNot
      rcases Finset.mem_insert.mp hz with hzv | hzw
      · rw [hzv]
        exact left_mem_segment ℝ v w
      · rw [Finset.mem_singleton.mp hzw]
        exact right_mem_segment ℝ v w
    have hpHull : p ∈ convexHull ℝ (({v,w} : Finset PLPoint) : Set PLPoint) := hp.1
    have hsep := K.vertexFaceSeparation_le_dist (hAK hs) (hAK heF.1) hz hpHull
    exact (not_le_of_gt hclose) ((dist_comm z p) ▸ hsep)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hf : ({a,b} : Finset PLPoint) ∈ A.edges := (A.mem_edges_iff _).mpr ⟨hs, hcard⟩
  have hqOpen := FinitePlanarComplex.openFace_pair_mem_openSegment hab hq
  have hqSeg := openSegment_subset_segment ℝ a b hqOpen
  refine ⟨q, a, b, hf, ?_, ?_, hqOpen, hyq, hqCase.imp_right ?_⟩
  · intro heq
    exact hqNot (openSegment_subset_segment ℝ v w (FinitePlanarComplex.openFace_pair_mem_openSegment hvw (heq ▸ hq)))
  · intro hdisj
    have heK : ({v,w} : Finset PLPoint) ∈ K.edges := (K.mem_edges_iff _).mpr ⟨hAK heF.1, heF.2⟩
    have hfK : ({a,b} : Finset PLPoint) ∈ K.edges := (K.mem_edges_iff _).mpr ⟨hAK hs, hcard⟩
    exact (not_le_of_gt hclose) (edge_separation_of_disjoint heK hfK hdisj hpSeg hqSeg)
  · intro hqmin
    exact (nearest_open_edge_is_perpendicular hab hf hq hqmin).2

private theorem orthonormal_pair_coordinates {e n : PLPoint}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : ⟪e,n⟫ = 0) (z : PLPoint) :
    z = ⟪e,z⟫ • e + ⟪n,z⟫ • n := by
  have hne : ⟪n,e⟫ = 0 := (real_inner_comm _ _).trans hen
  have hon : Orthonormal ℝ (![e,n] : Fin 2 → PLPoint) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [real_inner_self_eq_norm_sq, he, hn, hen, hne]
  let B := basisOfOrthonormalOfCardEqFinrank hon (by simp)
  have hB : (B : Fin 2 → PLPoint) = ![e,n] := coe_basisOfOrthonormalOfCardEqFinrank _ _
  let O := B.toOrthonormalBasis (hB.symm ▸ hon)
  have hO : (O : Fin 2 → PLPoint) = ![e,n] := (B.coe_toOrthonormalBasis _).trans hB
  have h := O.sum_repr' z
  rw [Fin.sum_univ_two, hO] at h
  exact h.symm

private theorem inner_normalize_eq_zero {e n : PLPoint} (h : ⟪e,n⟫ = 0) :
    ⟪normalize e, normalize n⟫ = 0 := by
  simp only [NormedSpace.normalize, real_inner_smul_right, real_inner_smul_left, h, mul_zero]

private theorem sub_eq_dist_smul_normalize_of_mem_openSegment {v u p : PLPoint}
    (hu : u ≠ v) (hp : p ∈ openSegment ℝ v u) :
    0 < dist p v ∧ p-v = dist p v • normalize (u-v) := by
  obtain ⟨t, ht, htp⟩ := (openSegment_eq_image_lineMap ℝ v u) ▸ hp
  have hsub : p-v = t • (u-v) := by
    rw [← htp, AffineMap.lineMap_apply_module', add_sub_cancel_right]
  have hdist : dist p v = t * ‖u-v‖ := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
  refine ⟨hdist ▸ ?_, ?_⟩
  · exact mul_pos ht.1 (norm_pos_iff.mpr (sub_ne_zero.mpr hu))
  · rw [hdist, mul_smul, norm_smul_normalize, hsub]

/-- A probe at height `H > 2r` which is within `2r` of the open incident
edge singles out the same half-plane and bounds the tangential coordinate. -/
private theorem outward_probe_coordinates {e n d : PLPoint} {a b H r : ℝ}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : ⟪e,n⟫ = 0) (hd : ‖d‖ = 1)
    (hb : 0 < b) (hH : 2*r < H) (hclose : ‖a • e + H • n - b • d‖ ≤ 2*r) :
    0 < ⟪n,d⟫ ∧ a * ⟪n,d⟫ ≤ H * ⟪e,d⟫ + 2*r := by
  let c := ⟪e,d⟫
  let s := ⟪n,d⟫
  let z := a • e + H • n - b • d
  let m := s • e - c • n
  have hne : ⟪n,e⟫ = 0 := (real_inner_comm _ _).trans hen
  have he₁ : ⟪e,e⟫ = 1 := by simp [real_inner_self_eq_norm_sq, he]
  have hn₁ : ⟪n,n⟫ = 1 := by simp [real_inner_self_eq_norm_sq, hn]
  have hz_n : ⟪n,z⟫ = H - b*s := by
    simp only [z, inner_sub_right, inner_add_right, real_inner_smul_right, hne, hn₁, mul_zero,
      mul_one, zero_add, s]
  have hz_e : ⟪e,z⟫ = a - b*c := by
    simp only [z, inner_sub_right, inner_add_right, real_inner_smul_right, hen, he₁, mul_zero,
      mul_one, add_zero, c]
  have hns : 0 < s := by
    by_contra! hs
    have hh := real_inner_le_norm n z
    rw [hn, one_mul, hz_n] at hh
    exact (not_le_of_gt hH) (le_trans (by linarith [mul_nonpos_of_nonneg_of_nonpos hb.le hs])
      (hh.trans hclose))
  have hrep := orthonormal_pair_coordinates he hn hen d
  have hunit : c^2 + s^2 = 1 := by
    have hh : ⟪d,d⟫ = 1 := by simp [real_inner_self_eq_norm_sq, hd]
    have hh' : ⟪d,d⟫ = c*c + s*s := calc
      _ = ⟪c • e + s • n, d⟫ := congrArg (fun z : PLPoint => ⟪z,d⟫) hrep
      _ = _ := by simp only [inner_add_left, real_inner_smul_left, c, s]
    nlinarith
  have hm : ‖m‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, hn,
      mul_one, mul_one, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, hen]
    linarith
  have hzm : ⟪m,z⟫ = a*s - H*c := by
    dsimp only [m]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hz_n, hz_e]
    ring
  have hh := real_inner_le_norm m z
  rw [hm, one_mul, hzm] at hh
  exact ⟨hns, by linarith [hh.trans hclose]⟩

private theorem exists_incident_edge_satisfying_probe_bound {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v₀ v₁ x p : PLPoint}
    (he : ({v₀,v₁} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v₀,v₁} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r ε : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hε : 0 < ε) (hεR : ε < K.admissibleRadius - r) (hεδ : ε < dist x p - r)
    (hx : x ∈ extendedBody A.realization r) :
    ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) = {v₀,v₁} ∧
      ({v,w} : Finset PLPoint) ∈ A.edges ∧ w ≠ u ∧
      0 < ⟪normalize (x-p), normalize (w-v)⟫ ∧
      dist p v * ⟪normalize (x-p), normalize (w-v)⟫ ≤
        (2*r + ε) * ⟪normalize (u-v), normalize (w-v)⟫ + 2*r := by
  classical
  let y := p + ((2*r + ε) / dist x p) • (x-p)
  obtain ⟨q, a, b, hf, hne, hdisj, hq, hdist, _⟩ :=
    exists_incident_edge_near_outward_probe hAK he hp hmin hr hR hε hεR hεδ hx
  obtain ⟨v, hv, hv'⟩ := Finset.not_disjoint_iff.mp hdisj
  have hu : ∃ u : PLPoint, ({v,u} : Finset PLPoint) = {v₀,v₁} := by
    rcases Finset.mem_insert.mp hv with hv₀ | hv₁
    · exact ⟨v₁, by rw [hv₀]⟩
    · exact ⟨v₀, by rw [Finset.mem_singleton.mp hv₁, Finset.pair_comm]⟩
  have hw : ∃ w : PLPoint, ({v,w} : Finset PLPoint) = {a,b} ∧ q ∈ openSegment ℝ v w := by
    rcases Finset.mem_insert.mp hv' with hva | hvb
    · exact ⟨b, by rw [hva], hva.symm ▸ hq⟩
    · have hvb' := Finset.mem_singleton.mp hvb
      refine ⟨a, by rw [hvb', Finset.pair_comm], ?_⟩
      rw [hvb', openSegment_symm]
      exact hq
  obtain ⟨u, hu⟩ := hu
  obtain ⟨w, hw, hqw⟩ := hw
  have he' : ({v,u} : Finset PLPoint) ∈ A.edges := hu.symm ▸ he
  have hf' : ({v,w} : Finset PLPoint) ∈ A.edges := hw.symm ▸ hf
  have huw : w ≠ u := by
    intro h
    exact hne (hw.symm.trans (h ▸ hu))
  have huv := FinitePlanarComplex.edge_endpoints_ne he'
  have hwv := FinitePlanarComplex.edge_endpoints_ne hf'
  obtain ⟨hp', hnorm⟩ := nearest_open_edge_is_perpendicular huv.symm he' (hu.symm ▸ hp) hmin
  let e := normalize (u-v)
  let n := normalize (x-p)
  let d := normalize (w-v)
  have hδ : 0 < dist x p := by linarith
  have hxp : x-p ≠ 0 := by simpa only [dist_eq_norm, norm_pos_iff] using hδ
  have he₁ : ‖e‖ = 1 := norm_normalize (sub_ne_zero.mpr huv)
  have hn₁ : ‖n‖ = 1 := norm_normalize hxp
  have hd₁ : ‖d‖ = 1 := norm_normalize (sub_ne_zero.mpr hwv)
  have hen : ⟪e,n⟫ = 0 := inner_normalize_eq_zero ((real_inner_comm _ _).trans hnorm)
  obtain ⟨_, hprepr⟩ := sub_eq_dist_smul_normalize_of_mem_openSegment huv hp'
  obtain ⟨hb, hqrepr⟩ := sub_eq_dist_smul_normalize_of_mem_openSegment hwv hqw
  have hxrep : dist x p • n = x-p := by rw [dist_eq_norm]; exact norm_smul_normalize _
  have hyrep : y-v = dist p v • e + (2*r+ε) • n := calc
    _ = p-v + ((2*r+ε) / dist x p) • (x-p) := by dsimp [y]; abel
    _ = _ := by rw [hprepr, ← hxrep, smul_smul, div_mul_cancel₀ _ hδ.ne']
  have hclose : ‖dist p v • e + (2*r + ε) • n - dist q v • d‖ ≤ 2*r := by
    change dist y q ≤ 2*r at hdist
    rw [dist_eq_norm, show y-q = (y-v) - (q-v) by abel, hyrep, hqrepr] at hdist
    exact hdist
  exact ⟨v, u, w, hu, hf', huw, outward_probe_coordinates he₁ hn₁ hen hd₁ hb (by linarith) hclose⟩

/-- Restricting to the finitely many possible pairs of edges allows the probe
height to tend down to `2r` with a fixed incident edge. -/
theorem exists_incident_edge_satisfying_limit_bound {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v₀ v₁ x p : PLPoint}
    (he : ({v₀,v₁} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v₀,v₁} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) (hδ : r < dist x p)
    (hx : x ∈ extendedBody A.realization r) :
    ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) = {v₀,v₁} ∧
      ({v,w} : Finset PLPoint) ∈ A.edges ∧ w ≠ u ∧
      0 < ⟪normalize (x-p), normalize (w-v)⟫ ∧
      dist p v * ⟪normalize (x-p), normalize (w-v)⟫ ≤
        2*r * (1 + ⟪normalize (u-v), normalize (w-v)⟫) := by
  classical
  let V : Finset PLPoint := {v₀,v₁}
  let C := (V ×ˢ V ×ˢ A.faceFinset.biUnion id).filter (fun t =>
    ({t.1,t.2.1} : Finset PLPoint) = V ∧ ({t.1,t.2.2} : Finset PLPoint) ∈ A.edges ∧
      t.2.2 ≠ t.2.1 ∧ 0 < ⟪normalize (x-p), normalize (t.2.2-t.1)⟫)
  let S (t : PLPoint × PLPoint × PLPoint) : Set ℝ := {ε |
    dist p t.1 * ⟪normalize (x-p), normalize (t.2.2-t.1)⟫ ≤
      (2*r + ε) * ⟪normalize (t.2.1-t.1), normalize (t.2.2-t.1)⟫ + 2*r}
  have hClosed : IsClosed (⋃ t ∈ C, S t) := by
    apply isClosed_biUnion_finset
    intro t _
    dsimp only [S]
    exact isClosed_le continuous_const (by fun_prop)
  let εmax := min (K.admissibleRadius-r) (dist x p-r)
  have hεmax : 0 < εmax := lt_min (sub_pos.mpr hR) (sub_pos.mpr hδ)
  have hSub : Ioo (0 : ℝ) εmax ⊆ ⋃ t ∈ C, S t := by
    rintro ε ⟨hε, hεMax⟩
    have hεR := hεMax.trans_le (min_le_left (K.admissibleRadius-r) (dist x p-r))
    have hεδ := hεMax.trans_le (min_le_right (K.admissibleRadius-r) (dist x p-r))
    obtain ⟨v, u, w, huv, hw, hwu, hn, hbound⟩ :=
      exists_incident_edge_satisfying_probe_bound hAK he hp hmin hr hR hε hεR hεδ hx
    have hwF := (A.mem_faceFinset_iff _).mpr ((A.mem_edges_iff _).mp hw).1
    have hvV : v ∈ V := by change v ∈ ({v₀,v₁} : Finset PLPoint); rw [← huv]; simp
    have huV : u ∈ V := by change u ∈ ({v₀,v₁} : Finset PLPoint); rw [← huv]; simp
    have hwV : w ∈ A.faceFinset.biUnion id := Finset.mem_biUnion.mpr ⟨{v,w}, hwF, by simp⟩
    exact Set.mem_iUnion₂.mpr ⟨(v,u,w), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hvV, Finset.mem_product.mpr ⟨huV,hwV⟩⟩, huv, hw, hwu, hn⟩,
      hbound⟩
  have hZero : (0 : ℝ) ∈ closure (Ioo 0 εmax) := by
    rw [closure_Ioo hεmax.ne]
    exact left_mem_Icc.mpr hεmax.le
  have h : (0 : ℝ) ∈ ⋃ t ∈ C, S t := hClosed.closure_subset_iff.mpr hSub hZero
  obtain ⟨⟨v,u,w⟩, ht, hb⟩ := Set.mem_iUnion₂.mp h
  obtain ⟨_, huv, hw, hwu, hn⟩ := Finset.mem_filter.mp ht
  refine ⟨v,u,w,huv,hw,hwu,hn,?_⟩
  simp only [S, Set.mem_setOf_eq, add_zero] at hb
  simpa only [mul_add, mul_one, add_comm (2*r)] using hb

private theorem half_angle_ratio_lt_of_positive_combination {e n d z : PLPoint}
    (he : ‖e‖ = 1) (hd : ‖d‖ = 1) (hen : ⟪e,n⟫ = 0) (hs : 0 < ⟪n,d⟫)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : z = a • e + b • d) :
    0 < ⟪n,normalize z⟫ ∧
      (1 + ⟪e,d⟫) / ⟪n,d⟫ < (1 + ⟪e,normalize z⟫) / ⟪n,normalize z⟫ := by
  let c := ⟪e,d⟫
  let s := ⟪n,d⟫
  let L := ‖z‖
  have hne : ⟪n,e⟫ = 0 := (real_inner_comm _ _).trans hen
  have hens : ⟪n,z⟫ = b*s := by
    simp only [hz, inner_add_right, real_inner_smul_right, hne, mul_zero, zero_add, s]
  have hez : ⟪e,z⟫ = a+b*c := by
    simp only [hz, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he,
      one_pow, mul_one, c]
  have hz₀ : z ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hens
    exact (mul_pos hb hs).ne' hens.symm
  have hL : 0 < L := norm_pos_iff.mpr hz₀
  have hcp : 0 < 1+c := by
    have hsq : ‖e+d‖^2 = 2*(1+c) := by rw [norm_add_sq_real, he, hd]; ring
    have hnz : e+d ≠ 0 := by
      intro h
      have hh : ⟪n,e+d⟫ = 0 := by rw [h, inner_zero_right]
      rw [inner_add_right, hne, zero_add] at hh
      exact hs.ne' hh
    nlinarith [sq_pos_of_ne_zero (norm_pos_iff.mpr hnz).ne']
  have hLs : L^2 - (b-a)^2 = 2*a*b*(1+c) := by
    dsimp only [L]
    rw [hz, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ha, abs_of_pos hb, he, hd, real_inner_smul_left, real_inner_smul_right]
    dsimp only [c]
    ring
  have hDiff : 0 < L+a-b := by
    by_contra! hh
    have hle : L^2 ≤ (b-a)^2 := pow_le_pow_left₀ hL.le (by linarith) 2
    linarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) ha) hb) hcp]
  have hns : ⟪n,normalize z⟫ = b*s / L := by
    rw [NormedSpace.normalize, real_inner_smul_right, hens, div_eq_mul_inv, mul_comm]
  have hec : ⟪e,normalize z⟫ = (a+b*c) / L := by
    rw [NormedSpace.normalize, real_inner_smul_right, hez, div_eq_mul_inv, mul_comm]
  have hscore : (1+(a+b*c)/L)/(b*s/L) = (1+c)/s + (L+a-b)/(b*s) := by
    field_simp [hL.ne', hb.ne', hs.ne']
    ring
  refine ⟨by rw [hns]; exact div_pos (mul_pos hb hs) hL, ?_⟩
  change (1+c)/s < _
  rw [hns, hec, hscore]
  exact lt_add_of_pos_right _ (div_pos hDiff (mul_pos hb hs))

/-- Maximize the half-angle cotangent among edges on the indicated side of
the first edge. Any edge in the open sector would increase that value. -/
theorem exists_consecutive_incident_with_half_angle_ratio_ge {A : FinitePlanarComplex}
    {v u w n : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ A.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (hen : ⟪normalize (u-v),n⟫ = 0) (hs : 0 < ⟪n,normalize (w-v)⟫) :
    ∃ z : PLPoint, ({v,z} : Finset PLPoint) ∈ A.edges ∧ 0 < ⟪n,normalize (z-v)⟫ ∧
      ConsecutiveIncident A v u z ∧
      (1+⟪normalize (u-v), normalize (w-v)⟫)/⟪n,normalize (w-v)⟫ ≤
        (1+⟪normalize (u-v), normalize (z-v)⟫)/⟪n,normalize (z-v)⟫ := by
  classical
  let e := normalize (u-v)
  let C := (A.faceFinset.biUnion id).filter (fun z =>
    ({v,z} : Finset PLPoint) ∈ A.edges ∧ 0 < ⟪n,normalize (z-v)⟫)
  let F (z : PLPoint) : ℝ := (1+⟪e,normalize (z-v)⟫)/⟪n,normalize (z-v)⟫
  have hC (z : PLPoint) (hez : ({v,z} : Finset PLPoint) ∈ A.edges) (hz : 0 < ⟪n,normalize (z-v)⟫) :
      z ∈ C := by
    apply Finset.mem_filter.mpr
    have hf := (A.mem_faceFinset_iff _).mpr ((A.mem_edges_iff _).mp hez).1
    exact ⟨Finset.mem_biUnion.mpr ⟨{v,z}, hf, by simp⟩, hez, hz⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image C F ⟨w, hC w hw hs⟩
  obtain ⟨_, hez, hzs⟩ := Finset.mem_filter.mp hz
  refine ⟨z, hez, hzs, ?_, hmax _ (hC w hw hs)⟩
  intro k hke _ _
  rintro ⟨a,b,ha,hb,hrep⟩
  have huv := sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hu)
  have hzv := sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hez)
  have hrep' : k-v = (a*‖u-v‖) • e + (b*‖z-v‖) • normalize (z-v) := by
    rw [mul_smul, mul_smul]
    exact hrep.trans (by rw [show ‖u-v‖ • e = u-v from norm_smul_normalize _, norm_smul_normalize])
  obtain ⟨hks, hlt⟩ := half_angle_ratio_lt_of_positive_combination (norm_normalize huv)
    (norm_normalize hzv) hen hzs (mul_pos ha (norm_pos_iff.mpr huv))
    (mul_pos hb (norm_pos_iff.mpr hzv)) hrep'
  exact (not_lt_of_ge (hmax k (hC k hke hks))) hlt

private theorem normalize_eq_cos_sin_of_inner_pos {d e n : PLPoint} (hd : d ≠ 0) (he : e ≠ 0)
    (hn : ‖n‖ = 1) (hen : ⟪normalize e,n⟫ = 0) (hs : 0 < ⟪n,normalize d⟫) :
    let θ := angle e d
    ⟪n,normalize d⟫ = Real.sin θ ∧ 0 < θ ∧ θ < Real.pi ∧
      normalize d = Real.cos θ • normalize e + Real.sin θ • n := by
  let θ := angle e d
  have hcos := inner_normalize_eq_cos_angle he hd
  have hrep := orthonormal_pair_coordinates (norm_normalize he) hn hen (normalize d)
  rw [hcos] at hrep
  have hvec : normalize d - Real.cos θ • normalize e = ⟪n,normalize d⟫ • n := by
    nth_rw 1 [hrep]
    abel
  have hsin : ⟪n,normalize d⟫ = Real.sin θ := by
    have hh := norm_normalize_sub_cos_smul he hd
    change ‖normalize d - Real.cos θ • normalize e‖ = Real.sin θ at hh
    rwa [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hs, hn, mul_one] at hh
  have hh : 0 < Real.sin θ := hsin ▸ hs
  have h₀ : 0 < θ := lt_of_le_of_ne (angle_nonneg e d) (fun h => by rw [← h, Real.sin_zero] at hh; exact hh.false)
  have hπ : θ < Real.pi := lt_of_le_of_ne (angle_le_pi e d) (fun h => by rw [h, Real.sin_pi] at hh; exact hh.false)
  exact ⟨hsin, h₀, hπ, hsin ▸ hrep⟩

/-- The localization lemma gives a strict half-angle bound for the first
consecutive edge. Equality would put the bisector tip within `r` of `x`. -/
theorem exists_consecutive_incident_satisfying_strict_bound {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v₀ v₁ x p : PLPoint}
    (he : ({v₀,v₁} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v₀,v₁} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx : x ∈ extendedBody A.realization r \ offset A.realization r) :
    ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) = {v₀,v₁} ∧
      ({v,w} : Finset PLPoint) ∈ A.edges ∧ ConsecutiveIncident A v u w ∧
      let θ := angle (u-v) (w-v)
      0 < θ ∧ θ < Real.pi ∧
      normalize (w-v) = Real.cos θ • normalize (u-v) + Real.sin θ • normalize (x-p) ∧
      dist p v * Real.sin θ < 2*r*(1+Real.cos θ) := by
  have hx₂ := extendedBody_subset_offset_twice _ _ hr.le hx.1
  have hδ : r < dist x p := lt_of_not_ge (fun h => hx.2 ⟨hx₂.1, hmin.symm ▸ h⟩)
  have hδ₂ : dist x p ≤ 2*r := hmin ▸ hx₂.2
  obtain ⟨v,u,f,hvu,hf,_,hsf,hbound⟩ :=
    exists_incident_edge_satisfying_limit_bound hAK he hp hmin hr hR hδ hx.1
  have hu : ({v,u} : Finset PLPoint) ∈ A.edges := hvu.symm ▸ he
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  obtain ⟨hpOpen, hnormal⟩ := nearest_open_edge_is_perpendicular huv.symm hu (hvu.symm ▸ hp) hmin
  let e := normalize (u-v)
  let n := normalize (x-p)
  have hxp : x-p ≠ 0 := by simpa only [dist_eq_norm, norm_pos_iff] using hr.trans hδ
  have hn : ‖n‖ = 1 := norm_normalize hxp
  have hen : ⟪e,n⟫ = 0 := inner_normalize_eq_zero ((real_inner_comm _ _).trans hnormal)
  obtain ⟨w,hw,hsw,hcon,horder⟩ := exists_consecutive_incident_with_half_angle_ratio_ge hu hf hen hsf
  have hwu : w ≠ u := by
    intro h
    subst w
    change 0 < ⟪n,e⟫ at hsw
    have hne : ⟪n,e⟫ = 0 := (real_inner_comm _ _).trans hen
    rw [hne] at hsw
    exact hsw.false
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  let θ := angle (u-v) (w-v)
  obtain ⟨hsin,hθ,hπ,hrep⟩ := normalize_eq_cos_sin_of_inner_pos (sub_ne_zero.mpr hwv)
    (sub_ne_zero.mpr huv) hn hen hsw
  have hcos := inner_normalize_eq_cos_angle (sub_ne_zero.mpr huv) (sub_ne_zero.mpr hwv)
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hsle : dist p v * Real.sin θ ≤ 2*r*(1+Real.cos θ) := by
    have ha := (le_div_iff₀ hsf).mpr hbound
    rw [mul_div_assoc] at ha
    have hb := ha.trans (mul_le_mul_of_nonneg_left horder (by positivity : 0 ≤ 2*r))
    rw [hcos, hsin, ← mul_div_assoc] at hb
    exact (le_div_iff₀ hs).mp hb
  refine ⟨v,u,w,hvu,hw,hcon,hθ,hπ,hrep,lt_of_le_of_ne hsle ?_⟩
  intro heq
  obtain ⟨_, hprep⟩ := sub_eq_dist_smul_normalize_of_mem_openSegment huv hpOpen
  have htip : arrowheadBisectorPoint v u w r 2 - v = dist p v • e + (2*r) • n := by
    have hc : (2*r / Real.sin θ) * (1+Real.cos θ) = dist p v := by
      field_simp [hs.ne']
      linarith only [heq]
    have hh : e+normalize (w-v) = (1+Real.cos θ) • e + Real.sin θ • n := by
      rw [hrep, add_smul, one_smul, add_assoc]
    rw [arrowheadBisectorPoint, add_sub_cancel_left]
    change (2*r / Real.sin θ) • (e+normalize (w-v)) = _
    rw [hh, smul_add, smul_smul, smul_smul, hc, div_mul_cancel₀ _ hs.ne']
  have hxrep : x-p = dist x p • n := by rw [dist_eq_norm, norm_smul_normalize]
  have hsub : x - arrowheadBisectorPoint v u w r 2 = (dist x p - 2*r) • n := by
    rw [show x - arrowheadBisectorPoint v u w r 2 =
      (x-p) + (p-v) - (arrowheadBisectorPoint v u w r 2-v) by abel,
      hxrep, hprep, htip, sub_smul]
    abel
  have hdist : dist x (arrowheadBisectorPoint v u w r 2) < r := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hδ₂), hn, mul_one]
    linarith
  have hTip := arrowheadBisectorPoint_mem_realization_or_frontier hAK hu hw hwu.symm hπ hcon hr hR
    (show (0 : ℝ) < 2 by norm_num) (by norm_num)
  rcases hTip with hA | hFront
  · exact hx.2 ((mem_offset_iff_exists_dist_le A.isClosed_realization).mpr ⟨_, hA, hdist.le⟩)
  · exact (not_lt_of_ge (le_dist_of_mem_frontier_offset_of_mem_extendedBody hx.1 hFront)) hdist

private theorem projection_pos_of_half_angle_bound {a δ c s r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hδ : r < δ) (hs : 0 < s) (hunit : s^2+c^2 = 1)
    (haUpper : a*s < 2*r*(1+c)) : 0 < a*c+δ*s := by
  have hδ₀ := hr.trans hδ
  by_contra! h
  have hc : c < 0 := by
    by_contra! hc
    linarith [mul_nonneg ha.le hc, mul_pos hδ₀ hs]
  have hprod := mul_le_mul_of_nonneg_right h hs.le
  have hstrict := mul_lt_mul_of_neg_right haUpper hc
  have hsq : r*s^2 < δ*s^2 := mul_lt_mul_of_pos_right hδ (by positivity)
  have hnc : -2*r*c*(1+c) ≤ r*s^2 := by
    have hh : r*s^2 - (-2*r*c*(1+c)) = r*(1+c)^2 := by
      linear_combination r*hunit
    linarith [mul_nonneg hr.le (sq_nonneg (1+c))]
  nlinarith only [hprod, hstrict, hsq, hnc]

private theorem kite_bounds_of_projected_distance {a δ c s r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hδ : r < δ) (hs : 0 < s) (hc₀ : -1 < c) (hc₁ : c ≤ 1)
    (hunit : s^2+c^2 = 1) (haUpper : a*s < 2*r*(1+c)) (hdist : δ ≤ |a*s-δ*c|) :
    δ < 2*r ∧ r < a*s-δ*c ∧ a*c+δ*s < 2*r*(1+c)/s := by
  have hδ₀ := hr.trans hδ
  have hd : δ ≤ a*s-δ*c := by
    by_contra! h
    apply (not_lt_of_ge hdist)
    apply abs_lt.mpr
    refine ⟨?_, h⟩
    linarith [mul_le_mul_of_nonneg_left hc₁ hδ₀.le, mul_pos ha hs]
  have haLower : δ*(1+c) ≤ a*s := by linarith
  have hcp : 0 < 1+c := by linarith
  have hδ₂ : δ < 2*r := by
    by_contra! h
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right h hcp.le)) (haLower.trans_lt haUpper)
  refine ⟨hδ₂,hδ.trans_le hd,(lt_div_iff₀ hs).mpr ?_⟩
  have hiden : (1+c)*c+s^2 = 1+c := by nlinarith
  by_cases hc : 0 ≤ c
  · calc
      _ = (a*s)*c + δ*s^2 := by ring
      _ < (2*r*(1+c))*c + 2*r*s^2 := add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_right haUpper.le hc) (mul_lt_mul_of_pos_right hδ₂ (by positivity))
      _ = _ := by linear_combination 2*r*hiden
  · calc
      _ = (a*s)*c + δ*s^2 := by ring
      _ ≤ (δ*(1+c))*c + δ*s^2 := add_le_add
        (mul_le_mul_of_nonpos_right haLower (le_of_not_ge hc)) le_rfl
      _ = δ*(1+c) := by linear_combination δ*hiden
      _ < _ := mul_lt_mul_of_pos_right hδ₂ hcp

/-- The nearest edge and its first consecutive neighbor provide all four
strict kite inequalities in the coordinates of Section 4. -/
theorem exists_consecutive_incident_satisfying_kite_bounds {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v₀ v₁ x p : PLPoint}
    (he : ({v₀,v₁} : Finset PLPoint) ∈ A.edges)
    (hp : p ∈ FinitePlanarComplex.openFace ({v₀,v₁} : Finset PLPoint))
    (hmin : Metric.infDist x A.realization = dist x p)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx : x ∈ extendedBody A.realization r \ offset A.realization r) :
    ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) = {v₀,v₁} ∧
      ({v,w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
      let θ := angle (u-v) (w-v)
      let e := normalize (u-v)
      let n := normalize (x-p)
      let a := dist p v
      let δ := dist x p
      let L := 2*r*(1+Real.cos θ)/Real.sin θ
      0 < θ ∧ θ < Real.pi ∧ ‖n‖ = 1 ∧ ⟪e,n⟫ = 0 ∧
      normalize (w-v) = Real.cos θ • e + Real.sin θ • n ∧ x-v = a • e + δ • n ∧
      r < δ ∧ r < a*Real.sin θ-δ*Real.cos θ ∧ a < L ∧ a*Real.cos θ+δ*Real.sin θ < L := by
  obtain ⟨v,u,w,hvu,hw,hcon,hθ,hπ,hdir,hUpper⟩ :=
    exists_consecutive_incident_satisfying_strict_bound hAK he hp hmin hr hR hx
  have hu : ({v,u} : Finset PLPoint) ∈ A.edges := hvu.symm ▸ he
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have huw : u ≠ w := by
    intro h
    subst w
    exact hθ.ne' (angle_self (sub_ne_zero.mpr huv))
  obtain ⟨hpOpen, hnormal⟩ := nearest_open_edge_is_perpendicular huv.symm hu (hvu.symm ▸ hp) hmin
  obtain ⟨huFace, huCard⟩ := (A.mem_edges_iff _).mp hu
  obtain ⟨hwFace, hwCard⟩ := (A.mem_edges_iff _).mp hw
  have huK := (K.mem_edges_iff _).mpr ⟨hAK huFace, huCard⟩
  have hwK := (K.mem_edges_iff _).mpr ⟨hAK hwFace, hwCard⟩
  have htwice := extendedBody_subset_offset_twice _ _ hr.le hx.1
  let a := dist p v
  let δ := dist x p
  let e := normalize (u-v)
  let d := normalize (w-v)
  let n := normalize (x-p)
  let θ := angle (u-v) (w-v)
  let s := Real.sin θ
  let c := Real.cos θ
  let L := 2*r*(1+c)/s
  let τ := a*c+δ*s
  have hδ : r < δ := lt_of_not_ge (fun h => hx.2 ⟨htwice.1, hmin.symm ▸ h⟩)
  have hδ₂ : δ ≤ 2*r := by
    change dist x p ≤ 2*r
    rw [← hmin]
    exact htwice.2
  have hxp : x-p ≠ 0 := by simpa only [δ, dist_eq_norm, norm_pos_iff] using hr.trans hδ
  have he₁ : ‖e‖ = 1 := norm_normalize (sub_ne_zero.mpr huv)
  have hd₁ : ‖d‖ = 1 := norm_normalize (sub_ne_zero.mpr hwv)
  have hn₁ : ‖n‖ = 1 := norm_normalize hxp
  have hen : ⟪e,n⟫ = 0 := inner_normalize_eq_zero ((real_inner_comm _ _).trans hnormal)
  obtain ⟨ha, hprepr⟩ := sub_eq_dist_smul_normalize_of_mem_openSegment huv hpOpen
  have hxrepr : x-v = a • e + δ • n := by
    rw [show x-v = (p-v) + (x-p) by abel, hprepr, show x-p = δ • n from
      (norm_smul_normalize (x-p)).symm]
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hc : -1 < c := by
    simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le le_rfl hπ
  have hunit : s^2+c^2 = 1 := Real.sin_sq_add_cos_sq θ
  have hUp : a < L := (lt_div_iff₀ hs).mpr hUpper
  have hτ : 0 < τ := projection_pos_of_half_angle_bound ha hr hδ hs hunit hUpper
  have hcos : ⟪e,d⟫ = c := inner_normalize_eq_cos_angle (sub_ne_zero.mpr huv) (sub_ne_zero.mpr hwv)
  have hd : d = c • e + s • n := hdir
  have hsin : ⟪n,d⟫ = s := by
    rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      show ⟪n,e⟫ = 0 from (real_inner_comm _ _).trans hen, real_inner_self_eq_norm_sq, hn₁]
    ring
  have hproj : ⟪x-v,d⟫ = τ := by
    rw [hxrepr, inner_add_left, real_inner_smul_left, real_inner_smul_left, hcos, hsin]
  have htipProj : ⟪arrowheadBisectorPoint v u w r 2-v,e⟫ = L := by
    rw [arrowheadBisectorPoint, add_sub_cancel_left]
    change ⟪(2*r/s) • (e+d),e⟫ = L
    rw [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, he₁,
      show ⟪d,e⟫ = c from (real_inner_comm _ _).trans hcos]
    dsimp [L]
    ring
  have htipLe : L ≤ dist (arrowheadBisectorPoint v u w r 2) v := by
    simpa only [htipProj, he₁, mul_one, ← dist_eq_norm] using
      real_inner_le_norm (arrowheadBisectorPoint v u w r 2-v) e
  have hM : dist x v < K.vertexFaceSeparation := by
    have hh := K.four_mul_one_add_csc_lt_separation huK hwK huw hθ hr hR
    have htip := dist_arrowheadBisectorPoint v u w hr.le (by norm_num : (0:ℝ) ≤ 2) huv hwv hθ hπ
    rw [htip] at htipLe
    have htri : dist x v ≤ δ+a := dist_triangle x p v
    linarith only [hh, htipLe, hUp, hδ₂, htri, K.vertexFaceSeparation_pos]
  have hτL : τ < ‖w-v‖ := by
    have hh : τ ≤ dist x v := by
      simpa only [hproj, hd₁, mul_one, ← dist_eq_norm] using real_inner_le_norm (x-v) d
    have hlen := FinitePlanarComplex.vertexFaceSeparation_le_edge_dist hwK
    rw [dist_comm v w, dist_eq_norm] at hlen
    exact (hh.trans_lt hM).trans_le hlen
  let y := v + τ • d
  have hy : y ∈ segment ℝ v w := by
    have hlen : 0 < ‖w-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwv)
    rw [segment_eq_image_lineMap]
    refine ⟨τ/‖w-v‖, ⟨div_nonneg hτ.le hlen.le, (div_le_one hlen).mpr hτL.le⟩, ?_⟩
    have hscale : (τ/‖w-v‖) • (w-v) = τ • d := calc
      _ = (τ/‖w-v‖) • (‖w-v‖ • d) := congrArg _ (norm_smul_normalize _).symm
      _ = _ := by rw [smul_smul, div_mul_cancel₀ _ hlen.ne']
    rw [AffineMap.lineMap_apply_module', hscale]
    exact add_comm _ _
  have hyA : y ∈ A.realization := A.convexHull_face_subset_realization _ hwFace (by
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hy)
  have hdist : δ ≤ dist x y := by
    change dist x p ≤ dist x y
    rw [← hmin]
    exact Metric.infDist_le_dist_of_mem hyA
  have hym : x-y = (a*s-δ*c) • (s • e-c • n) := by
    have h₁ : a-τ*c = (a*s-δ*c)*s := by dsimp only [τ]; linear_combination -a*hunit
    have h₂ : δ-τ*s = -((a*s-δ*c)*c) := by dsimp only [τ]; linear_combination -δ*hunit
    calc
      x-y = (x-v) - τ • d := by dsimp [y]; abel
      _ = (a-τ*c) • e + (δ-τ*s) • n := by
        rw [hxrepr, hd, smul_add, smul_smul, smul_smul, sub_smul, sub_smul]
        abel
      _ = _ := by
        rw [h₁, h₂, neg_smul, smul_sub, smul_smul, smul_smul]
        abel
  have hm : ‖s • e-c • n‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he₁, hn₁,
      mul_one, mul_one, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, hen]
    linarith
  rw [dist_eq_norm, hym, norm_smul, Real.norm_eq_abs, hm, mul_one] at hdist
  obtain ⟨_, hDist, hLong⟩ := kite_bounds_of_projected_distance ha hr hδ hs hc (Real.cos_le_one θ)
    hunit hUpper hdist
  exact ⟨v,u,w,hvu,hw,huw,hcon,hθ,hπ,hn₁,hen,hdir,hxrepr,hδ,hDist,hUp,hLong⟩

theorem convex_three_point_mem {S : Set PLPoint} (hS : Convex ℝ S)
    {P Q T : PLPoint} (hP : P ∈ S) (hQ : Q ∈ S) (hT : T ∈ S)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    (1-a-b) • P + a • Q + b • T ∈ S := by
  let weights : Fin 3 → ℝ := ![1-a-b,a,b]
  let points : Fin 3 → PLPoint := ![P,Q,T]
  have hweights (i : Fin 3) : 0 ≤ weights i := by
    fin_cases i <;> simp [weights, ha, hb] <;> linarith
  have hsum : ∑ i : Fin 3, weights i = 1 := by
    simp [Fin.sum_univ_three, weights]
    ring
  have hpoints (i : Fin 3) : points i ∈ S := by
    fin_cases i <;> simp [points, hP, hQ, hT]
  simpa [Fin.sum_univ_three, weights, points, add_assoc] using
    hS.sum_mem (t := Finset.univ) (fun i _ => hweights i) hsum (fun i _ => hpoints i)

/-- The four strict inequalities describe the interior of the paper's far kite.
The diagonal between the two bisector points splits the closed kite into
the two triangles used below. -/
theorem mem_interior_farKite_of_coordinate_bounds {v u w x n : PLPoint} {a δ r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hr : 0 < r)
    (hθ : 0 < angle (u-v) (w-v)) (hπ : angle (u-v) (w-v) < Real.pi)
    (hn : ‖n‖ = 1) (hen : ⟪normalize (u-v),n⟫ = 0)
    (hdir : normalize (w-v) = Real.cos (angle (u-v) (w-v)) • normalize (u-v) +
      Real.sin (angle (u-v) (w-v)) • n)
    (hx : x-v = a • normalize (u-v) + δ • n)
    (h₀ : r < δ) (h₁ : r < a*Real.sin (angle (u-v) (w-v))-δ*Real.cos (angle (u-v) (w-v)))
    (h₂ : a < 2*r*(1+Real.cos (angle (u-v) (w-v)))/Real.sin (angle (u-v) (w-v)))
    (h₃ : a*Real.cos (angle (u-v) (w-v))+δ*Real.sin (angle (u-v) (w-v)) <
      2*r*(1+Real.cos (angle (u-v) (w-v)))/Real.sin (angle (u-v) (w-v))) :
    x ∈ interior (farKite v u w r) := by
  let θ := angle (u-v) (w-v)
  let c := Real.cos θ
  let s := Real.sin θ
  let e := normalize (u-v)
  let d := normalize (w-v)
  let k := r/s
  let L := k*(1+c)
  let Q := arrowheadBisectorPoint v u w r 1
  let P := arrowheadBisectorPoint v u w r 2
  let E := farKiteShoulder v u w r
  let D := farKiteShoulder v w u r
  let K := farKite v u w r
  change d = c • e + s • n at hdir
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hk : 0 < k := div_pos hr hs
  have hL : 0 < L := mul_pos hk (by
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le (le_refl Real.pi) hπ
    rw [Real.cos_pi] at hc
    change -1 < c at hc
    linarith)
  have hunit : s^2+c^2 = 1 := Real.sin_sq_add_cos_sq θ
  have hq : Q = v + k • (e+d) := by simp only [Q,arrowheadBisectorPoint,one_mul,k,s,θ,e,d]
  have hP : P = Q + k • e + k • d := by
    change v + (2*r/s) • (e+d) = Q + k • e + k • d
    rw [hq, show 2*r/s = k+k by dsimp [k]; ring, add_smul, smul_add]
    abel
  have hshoulder {u' w' : PLPoint} (hu' : u' ≠ v) (hw' : w' ≠ v)
      (hangle : angle (u'-v) (w'-v) = θ) (hb : arrowheadBisectorPoint v u' w' r 1 = Q)
      (hb₂ : arrowheadBisectorPoint v u' w' r 2 = P)
      (hrep : P = Q + k • normalize (u'-v) + k • normalize (w'-v)) :
      farKiteShoulder v u' w' r = Q + L • normalize (u'-v) := by
    have hh := nearKiteShoulder_sub_vertex_eq (r := r) hu' hw'
    rw [hangle] at hh
    change nearKiteShoulder v u' w' r-v = k • (normalize (w'-v)-c • normalize (u'-v)) at hh
    calc
      _ = P - (nearKiteShoulder v u' w' r-v) := by
        rw [farKiteShoulder, AffineIsometryEquiv.pointReflection_apply, hb, ← hb₂,
          ← pointReflection_bisectorPoint, AffineIsometryEquiv.pointReflection_apply, hb]
        change (Q - nearKiteShoulder v u' w' r) + Q = (Q-v) + Q - (nearKiteShoulder v u' w' r-v)
        abel
      _ = _ := by rw [hrep, hh, smul_sub, smul_smul, show L=k+k*c by dsimp [L]; ring, add_smul]; abel
  have hE : E = Q + L • e := hshoulder hu hw rfl rfl rfl hP
  have hD : D = Q + L • d := hshoulder hw hu (angle_comm _ _)
    (arrowheadBisectorPoint_comm v w u r 1) (arrowheadBisectorPoint_comm v w u r 2)
    (by rw [hP]; abel)
  have hHull : K = convexHull ℝ {P,Q,E,D} := farKite_eq_convexHull _ _ _ _
  have hConv : Convex ℝ K := hHull.symm ▸ convex_convexHull ℝ _
  have hmem : ({P,Q,E,D} : Set PLPoint) ⊆ K := hHull.symm ▸ subset_convexHull ℝ _
  have hmemP : P ∈ K := hmem (by simp)
  have hmemQ : Q ∈ K := hmem (by simp)
  have hmemE : E ∈ K := hmem (by simp)
  have hmemD : D ∈ K := hmem (by simp)
  have hside {F G Y : PLPoint} {α β : ℝ} (hY : Y ∈ K) (hYrepr : Y = Q + L • F)
      (hPrepr : P = Q + k • F + k • G) (hβα : β ≤ α) (hβ : 0 ≤ β)
      (hαβ : α+c*β ≤ L) : Q + α • F + β • G ∈ K := by
    let t := (α-β)/L
    let b := β/k
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hβα) hL.le
    have hb : 0 ≤ b := div_nonneg hβ hk.le
    have htL : t*L = α-β := div_mul_cancel₀ _ hL.ne'
    have hbk : b*k = β := div_mul_cancel₀ _ hk.ne'
    have hab : t+b ≤ 1 := by
      apply (le_of_mul_le_mul_right ?_ hL)
      have hbL : b*L = β*(1+c) := by dsimp [L]; rw [← mul_assoc,hbk]
      rw [add_mul, htL, hbL, one_mul]
      linarith only [hαβ]
    have hh := convex_three_point_mem hConv hmemQ hY hmemP ht hb hab
    simp only [hYrepr, hPrepr, smul_add, smul_smul, htL, hbk, sub_smul, one_smul] at hh
    convert hh using 1 <;> abel
  let X (z : PLPoint) := ⟪e,z-v⟫
  let N (z : PLPoint) := ⟪n,z-v⟫
  let α (z : PLPoint) := X z - c*(N z/s) - k
  let β (z : PLPoint) := N z/s - k
  have hrepr (z : PLPoint) : z = Q + α z • e + β z • d := by
    have hz := orthonormal_pair_coordinates (norm_normalize (sub_ne_zero.mpr hu)) hn hen (z-v)
    have hfits : (N z/s)*s = N z := div_mul_cancel₀ _ hs.ne'
    have hvec : (X z-c*(N z/s)) • e + (N z/s) • d = z-v := by
      rw [hdir, smul_add, smul_smul, smul_smul, hfits, sub_smul, mul_comm (N z/s) c]
      rw [hz]
      change X z • e - (c*(N z/s)) • e + ((c*(N z/s)) • e + N z • n) = _
      abel
    calc
      z = v+(z-v) := by abel
      _ = v+((X z-c*(N z/s)) • e + (N z/s) • d) := by rw [hvec]
      _ = Q + α z • e + β z • d := by
        rw [hq]
        simp only [α,β,smul_add,sub_smul]
        abel
  let U : Set PLPoint := {z | 0 < α z} ∩ {z | 0 < β z} ∩
    {z | α z+c*β z < L} ∩ {z | β z+c*α z < L}
  have hOpen : IsOpen U := by
    have hα : Continuous α := by dsimp [α,X,N]; fun_prop
    have hβ : Continuous β := by dsimp [β,N]; fun_prop
    exact (((isOpen_lt continuous_const hα).inter (isOpen_lt continuous_const hβ)).inter
      (isOpen_lt (hα.add (continuous_const.mul hβ)) continuous_const)).inter
      (isOpen_lt (hβ.add (continuous_const.mul hα)) continuous_const)
  have hSub : U ⊆ K := by
    rintro z ⟨⟨⟨hzα,hzβ⟩,hz₁⟩,hz₂⟩
    change 0 < α z at hzα
    change 0 < β z at hzβ
    change α z+c*β z < L at hz₁
    change β z+c*α z < L at hz₂
    rw [hrepr z]
    rcases le_total (β z) (α z) with h | h
    · exact hside hmemE hE hP h hzβ.le hz₁.le
    · rw [add_right_comm]
      exact hside hmemD hD (by rw [hP, add_right_comm]) h hzα.le hz₂.le
  apply interior_maximal hSub hOpen
  have hX : X x = a := by
    dsimp only [X]
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_normalize (sub_ne_zero.mpr hu), hen]
    ring
  have hN : N x = δ := by
    dsimp only [N]
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      show ⟪n,e⟫ = 0 from (real_inner_comm _ _).trans hen, real_inner_self_eq_norm_sq, hn]
    ring
  have hα : α x = (a*s-δ*c-r)/s := by
    dsimp only [α,k]
    rw [hX,hN]
    field_simp [hs.ne']
  have hβ : β x = (δ-r)/s := by dsimp only [β,k]; rw [hN, sub_div]
  have hlong₁ : α x+c*β x = a-L := by
    dsimp only [α,β,L]
    rw [hX,hN]
    ring
  have hlong₂ : β x+c*α x = a*c+δ*s-L := by
    dsimp only [α,β,L]
    rw [hX,hN]
    field_simp [hs.ne']
    linear_combination -δ*hunit
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · change 0 < α x
    rw [hα]
    exact div_pos (sub_pos.mpr h₁) hs
  · change 0 < β x
    rw [hβ]
    exact div_pos (sub_pos.mpr h₀) hs
  · change α x+c*β x < L
    rw [hlong₁]
    have hh : a < L+L := h₂.trans_eq (by dsimp [L,k]; ring)
    linarith
  · change β x+c*α x < L
    rw [hlong₂]
    have hh : a*c+δ*s < L+L := h₃.trans_eq (by dsimp [L,k]; ring)
    linarith

/-- Once a point outside the ordinary offset lies in the open kite of a
consecutive pair, the bisector-point lemma excludes the removed disk. -/
theorem mem_farArrowhead_of_mem_interior_farKite {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u w x : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hπ : angle (u-v) (w-v) < Real.pi) (hc : ConsecutiveIncident A v u w)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx : x ∈ extendedBody A.realization r \ offset A.realization r)
    (hKite : x ∈ interior (farKite v u w r)) : x ∈ farArrowhead v u w r := by
  rw [farArrowhead, ite_eq_left hπ]
  refine ⟨hKite, ?_⟩
  intro hBall
  have hDist := Metric.mem_ball.mp hBall
  have hTip := arrowheadBisectorPoint_mem_realization_or_frontier hAK hu hw huw hπ hc hr hR
    (show (0 : ℝ) < 2 by norm_num) (by norm_num)
  rcases hTip with hA | hFront
  · exact hx.2 ((mem_offset_iff_exists_dist_le A.isClosed_realization).mpr ⟨_, hA, hDist.le⟩)
  · exact (not_lt_of_ge (le_dist_of_mem_frontier_offset_of_mem_extendedBody hx.1 hFront)) hDist

/-- Every point added by the extended body lies in a far arrowhead of a
consecutive pair of edges. -/
theorem exists_consecutive_farArrowhead_of_mem_extendedBody_sdiff_offset
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) {x : PLPoint}
    (hx : x ∈ extendedBody A.realization r \ offset A.realization r) :
    ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) ∈ A.edges ∧
      ({v,w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
      angle (u-v) (w-v) < Real.pi ∧ x ∈ farArrowhead v u w r := by
  obtain ⟨p, e, he, hp, hmin⟩ := exists_nearest_open_edge_of_mem_extendedBody_sdiff_offset hAK hr hR hx
  obtain ⟨v₀,v₁,_,rfl⟩ := Finset.card_eq_two.mp ((A.mem_edges_iff e).mp he).2
  obtain ⟨v,u,w,hvu,hw,huw,hcon,hθ,hπ,hn,hen,hdir,hrepr,h₀,h₁,h₂,h₃⟩ :=
    exists_consecutive_incident_satisfying_kite_bounds hAK he hp hmin hr hR hx
  have hu : ({v,u} : Finset PLPoint) ∈ A.edges := hvu.symm ▸ he
  have hKite := mem_interior_farKite_of_coordinate_bounds (FinitePlanarComplex.edge_endpoints_ne hu)
    (FinitePlanarComplex.edge_endpoints_ne hw) hr hθ hπ hn hen hdir hrepr h₀ h₁ h₂ h₃
  exact ⟨v,u,w,hu,hw,huw,hcon,hπ,
    mem_farArrowhead_of_mem_interior_farKite hAK hu hw huw hπ hcon hr hR hx hKite⟩

/-- The consecutive-arrowhead characterization of the extended body. -/
theorem extendedBody_eq_offset_union_consecutive_farArrowheads
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    extendedBody A.realization r = offset A.realization r ∪
      {x | ∃ v u w : PLPoint, ({v,u} : Finset PLPoint) ∈ A.edges ∧
        ({v,w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
        angle (u-v) (w-v) < Real.pi ∧ x ∈ farArrowhead v u w r} := by
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ offset A.realization r
    · exact Or.inl h
    · exact Or.inr (exists_consecutive_farArrowhead_of_mem_extendedBody_sdiff_offset hAK hr hR ⟨hx,h⟩)
  · rintro (hx | ⟨v,u,w,hu,hw,huw,_,hπ,hx⟩)
    · exact offset_subset_extendedBody _ _ hx
    · exact farArrowhead_subset_extendedBody hAK hu hw huw hπ hr hR hx

end SteinerProof
