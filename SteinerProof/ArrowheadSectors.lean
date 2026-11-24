import SteinerProof.ArrowheadLocalization

/-! Positive combinations of edge directions in a planar sector. -/

open Set InnerProductGeometry

noncomputable section

namespace SteinerProof

theorem sector_coordinate_of_combination (B : Module.Basis (Fin 2) ℝ PLPoint)
    (g h : PLPoint) (a b : ℝ) (i : Fin 2) :
    B.repr (a • g + b • h) i = a * B.repr g i + b * B.repr h i := by
  rw [map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply]
  rfl

theorem sector_coordinates_pos_iff (B : Module.Basis (Fin 2) ℝ PLPoint) (x : PLPoint) :
    (0 < B.repr x 0 ∧ 0 < B.repr x 1) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = a • B 0 + b • B 1 := by
  constructor
  · rintro ⟨h₀, h₁⟩
    have h := B.sum_repr x
    rw [Fin.sum_univ_two] at h
    exact ⟨_, _, h₀, h₁, h.symm⟩
  · rintro ⟨a, b, ha, hb, h⟩
    rw [h, sector_coordinate_of_combination, sector_coordinate_of_combination]
    simpa [Module.Basis.repr_self] using And.intro ha hb

/-- If a nonnegative combination crosses into the open sector while both of
its directions are outside, one of them supplies each positive coordinate. -/
theorem sector_order_of_positive_combination (B : Module.Basis (Fin 2) ℝ PLPoint)
    {g h x : PLPoint} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hG : min (B.repr g 0) (B.repr g 1) ≤ 0) (hH : min (B.repr h 0) (B.repr h 1) ≤ 0)
    (hrep : x = a • g + b • h) (hx₀ : 0 < B.repr x 0) (hx₁ : 0 < B.repr x 1) :
    (0 < B.repr g 0 ∧ B.repr g 1 ≤ 0 ∧ B.repr h 0 ≤ 0 ∧ 0 < B.repr h 1) ∨
      (0 < B.repr h 0 ∧ B.repr h 1 ≤ 0 ∧ B.repr g 0 ≤ 0 ∧ 0 < B.repr g 1) := by
  have hpos (i : Fin 2) (hi : 0 < B.repr x i) : 0 < B.repr g i ∨ 0 < B.repr h i := by
    by_contra! hh
    rw [hrep, sector_coordinate_of_combination] at hi
    exact (not_lt_of_ge (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hh.1)
      (mul_nonpos_of_nonneg_of_nonpos hb hh.2))) hi
  rcases hpos 0 hx₀ with hg₀ | hh₀
  · have hg₁ := (min_le_iff.mp hG).resolve_left (not_le_of_gt hg₀)
    have hh₁ := (hpos 1 hx₁).resolve_left (not_lt_of_ge hg₁)
    exact Or.inl ⟨hg₀, hg₁, (min_le_iff.mp hH).resolve_right (not_le_of_gt hh₁), hh₁⟩
  · have hh₁ := (min_le_iff.mp hH).resolve_left (not_le_of_gt hh₀)
    have hg₁ := (hpos 1 hx₁).resolve_right (not_lt_of_ge hh₁)
    exact Or.inr ⟨hh₀, hh₁, (min_le_iff.mp hG).resolve_right (not_le_of_gt hg₁), hg₁⟩

/-- If two outside directions have a combination in the open sector, each
boundary direction is a nonnegative combination of those directions. The
coefficient of the other direction is positive for a strict crossing. -/
theorem sector_axis_eq_nonneg_combination (B : Module.Basis (Fin 2) ℝ PLPoint)
    {i j : Fin 2} (hij : i ≠ j) {g h x : PLPoint} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgi : 0 < B.repr g i) (hgj : B.repr g j ≤ 0)
    (hhi : B.repr h i ≤ 0) (hhj : 0 < B.repr h j)
    (hrep : x = a • g + b • h) (hxi : 0 < B.repr x i) (hxj : 0 < B.repr x j) :
    ∃ c d : ℝ, 0 < c ∧ 0 ≤ d ∧ (B.repr g j < 0 → 0 < d) ∧ B i = c • g + d • h := by
  let t := -(B.repr g j) / B.repr h j
  let L := B.repr g i + t * B.repr h i
  have ht : 0 ≤ t := div_nonneg (neg_nonneg.mpr hgj) hhj.le
  have hj : t * B.repr h j = -(B.repr g j) := div_mul_cancel₀ _ hhj.ne'
  have hdot (k : Fin 2) : B.repr x k = a * B.repr g k + b * B.repr h k := by
    rw [hrep, sector_coordinate_of_combination]
  have htab : a * t < b := by
    apply (mul_lt_mul_iff_left₀ hhj).mp
    rw [mul_assoc, hj]
    linarith only [hdot j, hxj]
  have hL : 0 < L := by
    have hh := mul_le_mul_of_nonpos_right htab.le hhi
    have h : B.repr x i ≤ a * L := by
      dsimp only [L]
      nlinarith only [hdot i, hh]
    exact pos_of_mul_pos_right (hxi.trans_le h) ha
  refine ⟨L⁻¹, t / L, inv_pos.mpr hL, div_nonneg ht hL.le,
    fun h => div_pos (div_pos (neg_pos.mpr h) hhj) hL, ?_⟩
  apply B.repr.injective
  ext k
  rw [Module.Basis.repr_self, sector_coordinate_of_combination]
  have hk : k = i ∨ k = j := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  rcases hk with hki | hkj
  · rw [hki, Finsupp.single_eq_same]
    have h := inv_mul_cancel₀ hL.ne'
    dsimp only [L] at h
    rw [mul_add] at h
    rw [div_eq_mul_inv]
    nlinarith only [h]
  · rw [hkj, Finsupp.single_eq_of_ne hij.symm, div_eq_mul_inv]
    calc
      (0 : ℝ) = L⁻¹ * (B.repr g j + t * B.repr h j) := by rw [hj, add_neg_cancel, mul_zero]
      _ = _ := by ring

/-- An incident edge on a positive ray inside the cone of a face is an edge
of that face, by the simplicial-complex intersection property. -/
theorem vertex_mem_face_of_ray_mem_convexHull {A : FinitePlanarComplex}
    {s : Finset PLPoint} {v u p : PLPoint} (hs : s ∈ A.simplices.faces) (hv : v ∈ s)
    (he : ({v, u} : Finset PLPoint) ∈ A.edges) (hp : p ∈ convexHull ℝ (s : Set PLPoint))
    {t : ℝ} (ht : 0 < t) (hrep : p = v + t • (u - v)) : u ∈ s := by
  have hu := FinitePlanarComplex.edge_endpoints_ne he
  have heF := ((A.mem_edges_iff _).mp he).1
  let a := min t 1
  have ha : 0 < a := lt_min ht zero_lt_one
  have hat : a ≤ t := min_le_left _ _
  have ha₁ : a ≤ 1 := min_le_right _ _
  let q := v + a • (u - v)
  have hqS : q ∈ convexHull ℝ (s : Set PLPoint) := by
    have h : q = v + (a/t) • (p-v) := by
      rw [hrep, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ht.ne']
    rw [h]
    exact (convex_convexHull ℝ (s : Set PLPoint)).add_smul_sub_mem
      (subset_convexHull ℝ _ hv) hp ⟨div_nonneg ha.le ht.le, (div_le_one ht).mpr hat⟩
  have hqE : q ∈ convexHull ℝ (({v, u} : Finset PLPoint) : Set PLPoint) := by
    rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_image_lineMap]
    refine ⟨a, ⟨ha.le, ha₁⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  by_contra h
  have hInt : ({v, u} : Finset PLPoint) ∩ s = {v} := by
    ext z
    simp
    grind
  have hq : q ∈ convexHull ℝ (({v, u} : Finset PLPoint) : Set PLPoint) ∩
      convexHull ℝ (s : Set PLPoint) := ⟨hqE, hqS⟩
  rw [A.simplices.convexHull_inter_convexHull heF hs, ← Finset.coe_inter, hInt,
    Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hq
  have heq : a • (u-v) = 0 := by
    have hq' : v + a • (u-v) = v + 0 := hq.trans (add_zero v).symm
    exact add_left_cancel hq'
  exact (smul_ne_zero ha.ne' (sub_ne_zero.mpr hu)) heq

theorem sector_coordinates_nonpos_of_consecutive {A : FinitePlanarComplex}
    {v u w y : PLPoint} (hc : ConsecutiveIncident A v u w)
    (he : ({v,y} : Finset PLPoint) ∈ A.edges)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v) :
    min (B.repr (y-v) 0) (B.repr (y-v) 1) ≤ 0 := by
  by_contra! hyPos
  have hcoords := lt_min_iff.mp hyPos
  have hyu : y ≠ u := by
    intro h
    rw [h, ← hB₀, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at hcoords
    exact hcoords.2.false
  have hyw : y ≠ w := by
    intro h
    rw [h, ← hB₁, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at hcoords
    exact hcoords.1.false
  apply hc y he hyu hyw
  obtain ⟨a,b,ha,hb,hrep⟩ := (sector_coordinates_pos_iff B (y-v)).mp hcoords
  exact ⟨a,b,ha,hb,by rwa [← hB₀, ← hB₁]⟩

/-- Positive collinearity of two incident edges identifies their other endpoints. -/
theorem edge_endpoint_eq_of_pos_smul {A : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    {t : ℝ} (ht : 0 < t) (hrep : w-v = t • (u-v)) : u = w := by
  have h := vertex_mem_face_of_ray_mem_convexHull ((A.mem_edges_iff _).mp hw).1
    (Finset.mem_insert_self v {w}) hu (subset_convexHull ℝ _ (by simp : w ∈ ({v,w} : Finset PLPoint))) ht
    ((sub_eq_iff_eq_add.mp hrep).trans (add_comm _ _))
  exact Finset.mem_singleton.mp ((Finset.mem_insert.mp h).resolve_left (FinitePlanarComplex.edge_endpoints_ne hu))

/-- Two consecutive pairs at the same vertex have a common open-sector
point only when they define the same unordered pair of edges. -/
theorem incident_pairs_eq_of_common_open_sector {A : FinitePlanarComplex} {v u w g h x : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (hg : ({v,g} : Finset PLPoint) ∈ A.edges) (hh : ({v,h} : Finset PLPoint) ∈ A.edges)
    (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A v g h)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    (hx₀ : 0 < B.repr (x-v) 0) (hx₁ : 0 < B.repr (x-v) 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hrep : x-v = a • (g-v) + b • (h-v)) :
    ({u,w} : Finset PLPoint) = {g,h} := by
  have hout {y : PLPoint} (hy : ({v,y} : Finset PLPoint) ∈ A.edges) :=
    sector_coordinates_nonpos_of_consecutive hc₁ hy B hB₀ hB₁
  have hsolve {g h : PLPoint} {a b : ℝ}
      (hg : ({v,g} : Finset PLPoint) ∈ A.edges) (hh : ({v,h} : Finset PLPoint) ∈ A.edges)
      (hc : ConsecutiveIncident A v g h) (ha : 0 < a) (hb : 0 < b)
      (hrep : x-v = a • (g-v) + b • (h-v))
      (horder : 0 < B.repr (g-v) 0 ∧ B.repr (g-v) 1 ≤ 0 ∧
        B.repr (h-v) 0 ≤ 0 ∧ 0 < B.repr (h-v) 1) : u = g ∧ w = h := by
    obtain ⟨c,d,hcp,_,hdp,hU⟩ := sector_axis_eq_nonneg_combination B
      (by decide : (0 : Fin 2) ≠ 1) ha.le hb.le horder.1 horder.2.1 horder.2.2.1 horder.2.2.2 hrep hx₀ hx₁
    obtain ⟨e,f,hep,_,hfp,hW⟩ := sector_axis_eq_nonneg_combination B
      (by decide : (1 : Fin 2) ≠ 0) hb.le ha.le horder.2.2.2 horder.2.2.1 horder.2.1 horder.1
      (hrep.trans (add_comm _ _)) hx₁ hx₀
    have hu₁ : B.repr (u-v) 1 = 0 := by
      rw [← hB₀, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    have hw₀ : B.repr (w-v) 0 = 0 := by
      rw [← hB₁, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    have hg₁ : B.repr (g-v) 1 = 0 := by
      refine le_antisymm horder.2.1 (le_of_not_gt fun hg₁ => ?_)
      have hug : u ≠ g := fun heq => hg₁.ne (by rwa [← heq])
      have huh : u ≠ h := fun heq => horder.2.2.2.ne' (by rwa [← heq])
      exact hc u hu hug huh ⟨c,d,hcp,hdp hg₁,hB₀.symm.trans hU⟩
    have hh₀ : B.repr (h-v) 0 = 0 := by
      refine le_antisymm horder.2.2.1 (le_of_not_gt fun hh₀ => ?_)
      have hwg : w ≠ g := fun heq => horder.1.ne' (by rwa [← heq])
      have hwh : w ≠ h := fun heq => hh₀.ne (by rwa [← heq])
      exact hc w hw hwg hwh ⟨f,e,hfp hh₀,hep,(hB₁.symm.trans hW).trans (add_comm _ _)⟩
    have hG := B.sum_repr (g-v)
    rw [Fin.sum_univ_two, hg₁, zero_smul, add_zero, hB₀] at hG
    have hH := B.sum_repr (h-v)
    rw [Fin.sum_univ_two, hh₀, zero_smul, zero_add, hB₁] at hH
    exact ⟨edge_endpoint_eq_of_pos_smul hu hg horder.1 hG.symm,
      edge_endpoint_eq_of_pos_smul hw hh horder.2.2.2 hH.symm⟩
  rcases sector_order_of_positive_combination B ha.le hb.le (hout hg) (hout hh) hrep hx₀ hx₁ with hr | hr
  · obtain ⟨h₁,h₂⟩ := hsolve hg hh hc₂ ha hb hrep hr
    rw [h₁,h₂]
  · have hc₂' : ConsecutiveIncident A v h g := by
      intro y hy hyh hyg
      rintro ⟨a,b,ha,hb,hrep⟩
      exact hc₂ y hy hyg hyh ⟨b,a,hb,ha,hrep.trans (add_comm _ _)⟩
    obtain ⟨h₁,h₂⟩ := hsolve hh hg hc₂' hb ha (hrep.trans (add_comm _ _)) hr
    rw [h₁,h₂,Finset.pair_comm h g]

private theorem incident_face_point_eq_combination {A : FinitePlanarComplex}
    {s : Finset PLPoint} {v q : PLPoint} (hs : s ∈ A.simplices.faces) (hv : v ∈ s)
    (hq : q ∈ convexHull ℝ (s : Set PLPoint)) :
    ∃ g ∈ s, ∃ h ∈ s, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ q-v = a • (g-v) + b • (h-v) := by
  classical
  obtain ⟨w, hw, htotal, hqSum⟩ := Finset.mem_convexHull'.mp hq
  have hsum : ∑ z ∈ s.erase v, w z • (z-v) = q-v := by
    have ht := Finset.sum_erase_add (f := fun z => w z • (z-v)) _ hv
    simp only [sub_self, smul_zero, add_zero, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      htotal, one_smul, hqSum] at ht
    simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] using ht
  have hdim : s.card ≤ 3 := by
    have h := (A.simplices.indep hs).card_le_finrank_succ
    have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : s → PLPoint)))
    simp only [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at hle
    omega
  have hcard : (s.erase v).card ≤ 2 := by rw [Finset.card_erase_of_mem hv]; omega
  have hcases : (s.erase v).card = 0 ∨ (s.erase v).card = 1 ∨ (s.erase v).card = 2 := by omega
  rcases hcases with h | h | h
  · refine ⟨v, hv, v, hv, 0, 0, le_rfl, le_rfl, ?_⟩
    simpa [Finset.card_eq_zero.mp h] using hsum.symm
  · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h
    have hg' : g ∈ s := Finset.mem_of_mem_erase (by rw [hg]; simp)
    refine ⟨g, hg', v, hv, w g, 0, hw g hg', le_rfl, ?_⟩
    simpa [hg] using hsum.symm
  · obtain ⟨g, h, hgh, hpair⟩ := Finset.card_eq_two.mp h
    have hg : g ∈ s := Finset.mem_of_mem_erase (by rw [hpair]; simp)
    have hh : h ∈ s := Finset.mem_of_mem_erase (by rw [hpair]; simp)
    refine ⟨g, hg, h, hh, w g, w h, hw g hg, hw h hh, ?_⟩
    simpa [hpair, Finset.sum_pair hgh] using hsum.symm

theorem vertex_mem_face_of_nonneg_edge_combination {A : FinitePlanarComplex}
    {s : Finset PLPoint} {v u g h : PLPoint} (hs : s ∈ A.simplices.faces) (hv : v ∈ s)
    (he : ({v,u} : Finset PLPoint) ∈ A.edges) (hg : g ∈ s) (hh : h ∈ s)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hrep : u-v = a • (g-v) + b • (h-v)) : u ∈ s := by
  let d := a+b
  have hd : 0 < d := add_pos_of_pos_of_nonneg ha hb
  let q := (a/d) • g + (b/d) • h
  have ht : a/d+b/d = 1 := by rw [← add_div, div_self hd.ne']
  have hq : q ∈ convexHull ℝ (s : Set PLPoint) :=
    convex_convexHull ℝ _ (subset_convexHull ℝ _ hg) (subset_convexHull ℝ _ hh)
      (div_nonneg ha.le hd.le) (div_nonneg hb hd.le) ht
  have hvec : q - v = (a/d) • (g-v) + (b/d) • (h-v) := calc
    _ = q - ((a/d) • v + (b/d) • v) := by rw [← add_smul, ht, one_smul]
    _ = _ := by dsimp [q]; rw [smul_sub, smul_sub]; abel
  have hscaled : q-v = d⁻¹ • (u-v) := by
    rw [hrep, hvec, smul_add, smul_smul, smul_smul, div_eq_mul_inv, div_eq_mul_inv,
      mul_comm d⁻¹ a, mul_comm d⁻¹ b]
  exact vertex_mem_face_of_ray_mem_convexHull hs hv he hq (inv_pos.mpr hd)
    ((sub_eq_iff_eq_add.mp hscaled).trans (add_comm _ _))

/-- If an incident face enters the open sector of a consecutive pair,
both of the defining edges belong to that face. -/
theorem sector_endpoints_mem_face_of_pos_coordinates {A : FinitePlanarComplex}
    {s : Finset PLPoint} {v u w q : PLPoint} (hs : s ∈ A.simplices.faces) (hv : v ∈ s)
    (hu : ({v,u} : Finset PLPoint) ∈ A.edges) (hw : ({v,w} : Finset PLPoint) ∈ A.edges)
    (hc : ConsecutiveIncident A v u w) (hq : q ∈ convexHull ℝ (s : Set PLPoint))
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    (hq₀ : 0 < B.repr (q-v) 0) (hq₁ : 0 < B.repr (q-v) 1) : u ∈ s ∧ w ∈ s := by
  obtain ⟨g, hg, h, hh, a, b, ha, hb, hrep⟩ := incident_face_point_eq_combination hs hv hq
  have hOutside (y : PLPoint) (hy : y ∈ s) : min (B.repr (y-v) 0) (B.repr (y-v) 1) ≤ 0 := by
    by_cases hyv : y = v
    · simp [hyv]
    have heF : ({v,y} : Finset PLPoint) ∈ A.simplices.faces :=
      A.simplices.down_closed hs (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hy⟩)
        ⟨v, Finset.mem_insert_self _ _⟩
    have he : ({v,y} : Finset PLPoint) ∈ A.edges :=
      (A.mem_edges_iff _).mpr ⟨heF, Finset.card_pair (fun h => hyv h.symm)⟩
    exact sector_coordinates_nonpos_of_consecutive hc he B hB₀ hB₁
  have hboth {g h : PLPoint} {a b : ℝ} (hg : g ∈ s) (hh : h ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hrepr : q-v = a • (g-v) + b • (h-v))
      (h₀ : 0 < B.repr (g-v) 0 ∧ B.repr (g-v) 1 ≤ 0 ∧ B.repr (h-v) 0 ≤ 0 ∧ 0 < B.repr (h-v) 1) :
      u ∈ s ∧ w ∈ s := by
    obtain ⟨c, d, hcp, hdp, _, hAxis₀⟩ := sector_axis_eq_nonneg_combination B
      (by decide : (0 : Fin 2) ≠ 1) ha hb h₀.1 h₀.2.1 h₀.2.2.1 h₀.2.2.2 hrepr hq₀ hq₁
    obtain ⟨e, f, hep, hfp, _, hAxis₁⟩ := sector_axis_eq_nonneg_combination B
      (by decide : (1 : Fin 2) ≠ 0) hb ha h₀.2.2.2 h₀.2.2.1 h₀.2.1 h₀.1
      (hrepr.trans (add_comm _ _)) hq₁ hq₀
    rw [hB₀] at hAxis₀
    rw [hB₁] at hAxis₁
    exact ⟨vertex_mem_face_of_nonneg_edge_combination hs hv hu hg hh hcp hdp hAxis₀,
      vertex_mem_face_of_nonneg_edge_combination hs hv hw hh hg hep hfp hAxis₁⟩
  rcases sector_order_of_positive_combination B ha hb (hOutside g hg) (hOutside h hh) hrep hq₀ hq₁ with hc | hc
  · exact hboth hg hh ha hb hrep hc
  · exact hboth hh hg hb ha (hrep.trans (add_comm _ _)) hc

end SteinerProof
