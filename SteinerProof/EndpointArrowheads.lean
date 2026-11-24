import SteinerProof.EdgeOverlap

/-! The consecutive neighbors of an edge at an endpoint and their pieces. -/

open Set InnerProductGeometry MeasureTheory

noncomputable section

namespace SteinerProof

private theorem direction_eq_basis_coordinates (B : Module.Basis (Fin 2) ℝ PLPoint)
    (x : PLPoint) : x = B.repr x 0 • B 0 + B.repr x 1 • B 1 := by
  have h := B.sum_repr x
  rw [Fin.sum_univ_two] at h
  exact h.symm

private theorem direction_eq_of_eq_add {U W Z : PLPoint} {a b : ℝ} (hb : b ≠ 0)
    (hZ : Z = a • U + b • W) : W = (-a / b) • U + (1 / b) • Z := by
  rw [hZ, smul_add, smul_smul, smul_smul, one_div_mul_cancel hb, one_smul]
  have h : 1 / b * a = -(-a / b) := by ring
  rw [h, neg_smul]
  abel

private theorem consecutiveNeighbor_other_coordinate_neg {A : FinitePlanarComplex} {v u w z : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hw : w ∈ consecutiveNeighbors A v u) (hz : z ∈ consecutiveNeighbors A v u) (hzw : z ≠ w)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u - v) (hB₁ : B 1 = w - v) :
    B.repr (z - v) 1 < 0 := by
  obtain ⟨hw, huw, hcw, _⟩ := hw
  obtain ⟨hz, huz, hcz, hpiz⟩ := hz
  let a := B.repr (z - v) 0
  let b := B.repr (z - v) 1
  have hRep : z - v = a • (u - v) + b • (w - v) := by
    rw [← hB₀, ← hB₁]
    exact direction_eq_basis_coordinates B (z - v)
  change b < 0
  by_contra! hb
  rcases hb.lt_or_eq with hb | hb
  · rcases lt_trichotomy a 0 with ha | ha | ha
    · exact hcz w hw huw.symm hzw.symm ⟨-a / b, 1 / b, div_pos (neg_pos.mpr ha) hb,
        div_pos zero_lt_one hb, direction_eq_of_eq_add hb.ne' hRep⟩
    · rw [ha, zero_smul, zero_add] at hRep
      exact hzw (edge_endpoint_eq_of_pos_smul hw hz hb hRep).symm
    · exact hcw z hz huz.symm hzw ⟨a, b, ha, hb, hRep⟩
  · rw [← hb, zero_smul, add_zero] at hRep
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exact hpiz.ne (angle_eq_pi_iff.mpr ⟨sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hu), a, ha, hRep⟩)
    · rw [ha, zero_smul] at hRep
      exact (sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hz)) hRep
    · exact huz (edge_endpoint_eq_of_pos_smul hu hz ha hRep)

/-- A directed edge has at most one consecutive neighbor on each side. -/
theorem consecutiveNeighbors_eq_empty_singleton_or_pair {A : FinitePlanarComplex} {v u : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) :
    consecutiveNeighbors A v u = ∅ ∨ (∃ w, consecutiveNeighbors A v u = {w}) ∨
      ∃ w z : PLPoint, w ≠ z ∧ consecutiveNeighbors A v u = {w, z} := by
  classical
  by_cases h : (consecutiveNeighbors A v u).Nonempty
  · obtain ⟨w, hw⟩ := h
    by_cases h' : ∃ z ∈ consecutiveNeighbors A v u, z ≠ w
    · obtain ⟨z, hz, hzw⟩ := h'
      have huv := FinitePlanarComplex.edge_endpoints_ne hu
      obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis huv (FinitePlanarComplex.edge_endpoints_ne hw.1)
        (A.incident_angle_pos hu hw.1 hw.2.1) hw.2.2.2
      obtain ⟨C, hC₀, hC₁⟩ := exists_incident_basis huv (FinitePlanarComplex.edge_endpoints_ne hz.1)
        (A.incident_angle_pos hu hz.1 hz.2.1) hz.2.2.2
      have hu₁ : B.repr (u - v) 1 = 0 := by
        rw [← hB₀, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hzB := consecutiveNeighbor_other_coordinate_neg hu hw hz hzw B hB₀ hB₁
      refine Or.inr (Or.inr ⟨w, z, hzw.symm, ?_⟩)
      ext y
      constructor
      · intro hy
        by_cases hyw : y = w
        · exact Or.inl hyw
        by_cases hyz : y = z
        · exact Or.inr (Set.mem_singleton_iff.mpr hyz)
        have hyB := consecutiveNeighbor_other_coordinate_neg hu hw hy hyw B hB₀ hB₁
        have hyC := consecutiveNeighbor_other_coordinate_neg hu hz hy hyz C hC₀ hC₁
        have hRep := direction_eq_basis_coordinates C (y - v)
        rw [hC₀, hC₁] at hRep
        have hEq : B.repr (y - v) 1 = C.repr (y - v) 1 * B.repr (z - v) 1 := by
          nth_rw 1 [hRep]
          rw [sector_coordinate_of_combination, hu₁, mul_zero, zero_add]
        exact ((hEq ▸ hyB).not_gt (mul_pos_of_neg_of_neg hyC hzB)).elim
      · rintro (rfl | hy)
        · exact hw
        · obtain rfl := Set.mem_singleton_iff.mp hy
          exact hz
    · refine Or.inr (Or.inl ⟨w, ?_⟩)
      ext y
      constructor
      · intro hy
        exact Set.mem_singleton_iff.mpr (not_not.mp fun hn => h' ⟨y, hy, hn⟩)
      · rintro rfl
        exact hw
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)

/-- When both neighbors exist, their angle is straight, or the deleted
direction or its opposite lies in their open sector. -/
theorem consecutiveNeighbors_direction_cases {A : FinitePlanarComplex} {v u w z : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hw : w ∈ consecutiveNeighbors A v u) (hz : z ∈ consecutiveNeighbors A v u) (hzw : z ≠ w) :
    angle (w - v) (z - v) = Real.pi ∨
      (angle (w - v) (z - v) < Real.pi ∧
        ((∃ a b : ℝ, 0 < a ∧ 0 < b ∧ u - v = a • (w - v) + b • (z - v)) ∨
          (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ -(u - v) = a • (w - v) + b • (z - v)))) := by
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw.1
  obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis (FinitePlanarComplex.edge_endpoints_ne hu) hwv
    (A.incident_angle_pos hu hw.1 hw.2.1) hw.2.2.2
  let a := B.repr (z - v) 0
  let b := B.repr (z - v) 1
  have hb : b < 0 := consecutiveNeighbor_other_coordinate_neg hu hw hz hzw B hB₀ hB₁
  have hRep : z - v = a • (u - v) + b • (w - v) := by
    rw [← hB₀, ← hB₁]
    exact direction_eq_basis_coordinates B (z - v)
  by_cases ha : a = 0
  · exact Or.inl (angle_eq_pi_iff.mpr ⟨sub_ne_zero.mpr hwv, b, hb, by simpa [ha] using hRep⟩)
  have hp : angle (w - v) (z - v) < Real.pi := by
    refine lt_of_le_of_ne (angle_le_pi _ _) fun hp => ?_
    obtain ⟨_, t, _, ht⟩ := angle_eq_pi_iff.mp hp
    apply ha
    change B.repr (z - v) 0 = 0
    rw [ht, ← hB₁, map_smul, Module.Basis.repr_self]
    simp
  have hU := direction_eq_of_eq_add ha (hRep.trans (add_comm _ _))
  refine Or.inr ⟨hp, ?_⟩
  rcases lt_or_gt_of_ne ha with h | h
  · refine Or.inr ⟨b / a, -1 / a, div_pos_of_neg_of_neg hb h,
      div_pos_of_neg_of_neg (by norm_num) h, ?_⟩
    calc
      -(u - v) = -((-b / a) • (w - v) + (1 / a) • (z - v)) := congrArg Neg.neg hU
      _ = _ := by rw [neg_add, ← neg_smul, ← neg_smul]; congr 2 <;> ring
  · exact Or.inl ⟨-b / a, 1 / a, div_pos (neg_pos.mpr hb) h, div_pos zero_lt_one h, hU⟩

theorem farArrowhead_comm (v u w : PLPoint) (r : ℝ) : farArrowhead v u w r = farArrowhead v w u r := by
  unfold farArrowhead
  rw [angle_comm (u - v) (w - v), farKite_comm v u w r, arrowheadBisectorPoint_comm v u w r 2]

def endpointRemovedFarArrowheads (A : FinitePlanarComplex) (v u : PLPoint) (r : ℝ) : Set PLPoint :=
  ⋃ w ∈ consecutiveNeighbors A v u, farArrowhead v u w r

def endpointCreatedFarArrowheads (A : FinitePlanarComplex) (v u : PLPoint) (r : ℝ) : Set PLPoint :=
  {x | ∃ w ∈ consecutiveNeighbors A v u, ∃ z ∈ consecutiveNeighbors A v u,
    w ≠ z ∧ angle (w - v) (z - v) < Real.pi ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ u - v = a • (w - v) + b • (z - v)) ∧ x ∈ farArrowhead v w z r}

private theorem same_base_edge_ne {v u w : PLPoint} (hwv : w ≠ v) (hwu : w ≠ u) :
    ({v, w} : Finset PLPoint) ≠ {v, u} := by
  intro heq
  have hmem : w ∈ ({v, u} : Finset PLPoint) := heq ▸ (by simp : w ∈ ({v, w} : Finset PLPoint))
  exact hwu (Finset.mem_singleton.mp ((Finset.mem_insert.mp hmem).resolve_left hwv))

private theorem facet_triangle_not_face {A : FinitePlanarComplex} {v u w : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) (hwv : w ≠ v) (hwu : w ≠ u) :
    ({v, u, w} : Finset PLPoint) ∉ A.simplices.faces := by
  intro h
  have hs : ({v, u} : Finset PLPoint) ⊆ {v, u, w} := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨by simp, Finset.singleton_subset_iff.mpr (by simp)⟩
  have hEq := (Geometry.SimplicialComplex.mem_facets.mp he).2 _ h hs
  have hm : w ∈ ({v, u} : Finset PLPoint) := hEq.symm ▸ (by simp : w ∈ ({v, u, w} : Finset PLPoint))
  exact hwu (Finset.mem_singleton.mp ((Finset.mem_insert.mp hm).resolve_left hwv))

theorem removedFarArrowheads_eq_endpoint_union {A : FinitePlanarComplex} {v u : PLPoint}
    (hvu : v ≠ u) (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) (r : ℝ) :
    removedFarArrowheads A {v, u} r = endpointRemovedFarArrowheads A v u r ∪ endpointRemovedFarArrowheads A u v r := by
  have hFirst {p q w x : PLPoint} (hEq : ({p, q} : Finset PLPoint) = {v, u})
      (hw : w ∈ consecutiveNeighbors A p q) (hx : x ∈ farArrowhead p q w r) :
      x ∈ endpointRemovedFarArrowheads A v u r ∪ endpointRemovedFarArrowheads A u v r := by
    rcases pair_eq_or_swap hvu hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨w, hw, hx⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, hw, hx⟩)
  have hCover {p q : PLPoint} (hEq : ({p, q} : Finset PLPoint) = {v, u}) (hpq : p ≠ q) :
      endpointRemovedFarArrowheads A p q r ⊆ removedFarArrowheads A {v, u} r := by
    intro x hx
    obtain ⟨w, ⟨hw, hqw, hc, hπ⟩, hx⟩ := Set.mem_iUnion₂.mp hx
    have he' : ({p, q} : Finset PLPoint) ∈ A.simplices.facets := hEq.symm ▸ he
    have hE : ({p, q} : Finset PLPoint) ∈ A.edges :=
      (A.mem_edges_iff _).mpr ⟨(Geometry.SimplicialComplex.mem_facets.mp he').1, Finset.card_pair hpq⟩
    exact ⟨p, q, w, hE, hw, hqw, hc, hπ,
      facet_triangle_not_face he' (FinitePlanarComplex.edge_endpoints_ne hw) hqw.symm, Or.inl hEq, hx⟩
  refine Subset.antisymm ?_ (union_subset (hCover rfl hvu) (hCover (Finset.pair_comm u v) hvu.symm))
  rintro x ⟨p, q, w, hq, hw, hqw, hc, hπ, _, hEq | hEq, hx⟩
  · exact hFirst hEq ⟨hw, hqw, hc, hπ⟩ hx
  · exact hFirst hEq ⟨hq, hqw.symm, consecutiveIncident_swap hc, by rwa [angle_comm]⟩
      (farArrowhead_comm p q w r ▸ hx)

private theorem consecutiveIncident_neighbor_of_created {A : FinitePlanarComplex} {v u w z : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets)
    (hw : ({v, w} : Finset PLPoint) ∈ (A.eraseFacet {v, u} he).edges)
    (hz : ({v, z} : Finset PLPoint) ∈ (A.eraseFacet {v, u} he).edges)
    (hwz : w ≠ z) (hc : ConsecutiveIncident (A.eraseFacet {v, u} he) v w z)
    (hπ : angle (w - v) (z - v) < Real.pi)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hInter : u - v = a • (w - v) + b • (z - v)) :
    ConsecutiveIncident A v u w := by
  let B := A.eraseFacet {v, u} he
  obtain ⟨C, hC₀, hC₁⟩ := exists_incident_basis (FinitePlanarComplex.edge_endpoints_ne hw)
    (FinitePlanarComplex.edge_endpoints_ne hz) (B.incident_angle_pos hw hz hwz) hπ
  intro y hy hyu _
  rintro ⟨c, d, hc', hd, hrep⟩
  have hyB : ({v, y} : Finset PLPoint) ∈ B.edges :=
    (mem_edges_eraseFacet_iff he).mpr ⟨hy, same_base_edge_ne (FinitePlanarComplex.edge_endpoints_ne hy) hyu⟩
  have hneg := sector_coordinates_nonpos_of_consecutive hc hyB C hC₀ hC₁
  have hyRep : y - v = (c * a + d) • C 0 + (c * b) • C 1 := by
    rw [hrep, hInter, hC₀, hC₁, smul_add, smul_smul, smul_smul, add_smul]
    abel
  exact (not_lt_of_ge hneg) (lt_min_iff.mpr ((sector_coordinates_pos_iff C (y - v)).mpr
    ⟨_, _, add_pos (mul_pos hc' ha) hd, mul_pos hc' hb, hyRep⟩))

private theorem consecutiveIncident_created_of_neighbors {A : FinitePlanarComplex} {v u w z : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) (heA : ({v, u} : Finset PLPoint) ∈ A.edges)
    (hw : w ∈ consecutiveNeighbors A v u) (hz : z ∈ consecutiveNeighbors A v u)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hInter : u - v = a • (w - v) + b • (z - v)) :
    ConsecutiveIncident (A.eraseFacet {v, u} he) v w z := by
  intro y hy hyw hyz
  obtain ⟨hyA, hyNot⟩ := (mem_edges_eraseFacet_iff he).mp hy
  have hyu : y ≠ u := fun h => hyNot (by rw [h])
  rintro ⟨c, d, hc, hd, hrep⟩
  have hL : 0 < c / a := div_pos hc ha
  have hR : 0 < d / b := div_pos hd hb
  have hLc : c / a * a = c := div_mul_cancel₀ _ ha.ne'
  have hRd : d / b * b = d := div_mul_cancel₀ _ hb.ne'
  rcases lt_trichotomy (c / a) (d / b) with hh | hh | hh
  · have hs : 0 < d - (c / a) * b := sub_pos.mpr ((lt_div_iff₀ hb).mp hh)
    apply hz.2.2.1 y hyA hyu hyz
    refine ⟨c / a, d - (c / a) * b, hL, hs, ?_⟩
    rw [hInter, hrep, smul_add, smul_smul, smul_smul, hLc, sub_smul]
    abel
  · have hEq : (c / a) * b = d := hh ▸ hRd
    have hDir : y - v = (c / a) • (u - v) := by
      rw [hrep, hInter, smul_add, smul_smul, smul_smul, hLc, hEq]
    exact hyu (edge_endpoint_eq_of_pos_smul heA hyA hL hDir).symm
  · have hs : 0 < c - (d / b) * a := sub_pos.mpr ((lt_div_iff₀ ha).mp hh)
    apply hw.2.2.1 y hyA hyu hyw
    refine ⟨d / b, c - (d / b) * a, hR, hs, ?_⟩
    rw [hInter, hrep, smul_add, smul_smul, smul_smul, hRd, sub_smul]
    abel

private theorem created_piece_of_endpoint {A : FinitePlanarComplex} {v u : PLPoint}
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) (hvu : v ≠ u) {r : ℝ} :
    endpointCreatedFarArrowheads A v u r ⊆ createdFarArrowheads A {v, u} he r := by
  rintro x ⟨w, hw, z, hz, hwz, hπ, ⟨a, b, ha, hb, hInter⟩, hx⟩
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges :=
    (A.mem_edges_iff _).mpr ⟨(Geometry.SimplicialComplex.mem_facets.mp he).1, Finset.card_pair hvu⟩
  have hwB := (mem_edges_eraseFacet_iff he).mpr ⟨hw.1,
    same_base_edge_ne (FinitePlanarComplex.edge_endpoints_ne hw.1) hw.2.1.symm⟩
  have hzB := (mem_edges_eraseFacet_iff he).mpr ⟨hz.1,
    same_base_edge_ne (FinitePlanarComplex.edge_endpoints_ne hz.1) hz.2.1.symm⟩
  have hc := consecutiveIncident_created_of_neighbors he heA hw hz ha hb hInter
  have hext : ({v, w, z} : Finset PLPoint) ∉ (A.eraseFacet {v, u} he).simplices.faces := by
    intro h
    have huF := vertex_mem_face_of_nonneg_edge_combination h.1 (by simp) heA (by simp) (by simp) ha hb.le hInter
    simp [hvu.symm, hw.2.1, hz.2.1] at huF
  exact ⟨v, w, z, hwB, hzB, hwz, hc, hπ, hext,
    (not_consecutiveIncident_iff_erased_edge_inside he hwB hzB (Finset.card_pair hvu) hc).mpr
      ⟨u, rfl, a, b, ha, hb, hInter⟩, hx⟩

private theorem eraseFacet_congr {A : FinitePlanarComplex} {s t : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) (ht : t ∈ A.simplices.facets) (h : s = t) :
    A.eraseFacet s hs = A.eraseFacet t ht := by
  subst t
  rfl

private theorem createdFarArrowheads_congr {A : FinitePlanarComplex} {s t : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) (ht : t ∈ A.simplices.facets) (h : s = t) (r : ℝ) :
    createdFarArrowheads A s hs r = createdFarArrowheads A t ht r := by
  subst t
  rfl

theorem createdFarArrowheads_eq_endpoint_union {A : FinitePlanarComplex} {v u : PLPoint}
    (hvu : v ≠ u) (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) (r : ℝ) :
    createdFarArrowheads A {v, u} he r = endpointCreatedFarArrowheads A v u r ∪ endpointCreatedFarArrowheads A u v r := by
  have he' : ({u, v} : Finset PLPoint) ∈ A.simplices.facets := by rwa [Finset.pair_comm]
  have hSwap := eraseFacet_congr he' he (Finset.pair_comm u v)
  have hCover : endpointCreatedFarArrowheads A u v r ⊆ createdFarArrowheads A {v, u} he r := by
    rw [← createdFarArrowheads_congr he' he (Finset.pair_comm u v) r]
    exact created_piece_of_endpoint he' hvu.symm
  refine Subset.antisymm ?_ (union_subset (created_piece_of_endpoint he hvu) hCover)
  rintro x ⟨p, w, z, hw, hz, hwz, hc, hπ, _, hOld, hx⟩
  obtain ⟨q, hEq, a, b, ha, hb, hInter⟩ :=
    (not_consecutiveIncident_iff_erased_edge_inside he hw hz (Finset.card_pair hvu) hc).mp hOld
  have hLocal (heP : ({p, q} : Finset PLPoint) ∈ A.simplices.facets)
      (hwP : ({p, w} : Finset PLPoint) ∈ (A.eraseFacet {p, q} heP).edges)
      (hzP : ({p, z} : Finset PLPoint) ∈ (A.eraseFacet {p, q} heP).edges)
      (hcP : ConsecutiveIncident (A.eraseFacet {p, q} heP) p w z) : x ∈ endpointCreatedFarArrowheads A p q r := by
    have hW := (mem_edges_eraseFacet_iff heP).mp hwP
    have hZ := (mem_edges_eraseFacet_iff heP).mp hzP
    have hqw : q ≠ w := fun h => hW.2 (by rw [h])
    have hqz : q ≠ z := fun h => hZ.2 (by rw [h])
    have hcw := consecutiveIncident_neighbor_of_created heP hwP hzP hwz hcP hπ ha hb hInter
    have hcz := consecutiveIncident_neighbor_of_created heP hzP hwP hwz.symm (consecutiveIncident_swap hcP)
      (by rwa [angle_comm]) hb ha (hInter.trans (add_comm _ _))
    have hAngle {y : PLPoint} (hyW : y = w ∨ y = z) :
        angle (q - p) (y - p) < Real.pi := by
      obtain ⟨C, hC₀, hC₁⟩ := exists_incident_basis (FinitePlanarComplex.edge_endpoints_ne hW.1)
        (FinitePlanarComplex.edge_endpoints_ne hZ.1) (A.incident_angle_pos hW.1 hZ.1 hwz) hπ
      have hpos := (sector_coordinates_pos_iff C (q - p)).mpr
        ⟨a, b, ha, hb, by rwa [hC₀, hC₁]⟩
      refine lt_of_le_of_ne (angle_le_pi _ _) fun h => ?_
      obtain ⟨_, t, ht, hty⟩ := angle_eq_pi_iff.mp h
      rcases hyW with hy | hy
      · rw [hy] at hty
        have hZero : C.repr (w - p) 0 = 1 := by rw [← hC₀, Module.Basis.repr_self]; simp
        have hNeg : C.repr (w - p) 0 < 0 := by
          rw [hty, map_smul, Finsupp.smul_apply, smul_eq_mul]
          exact mul_neg_of_neg_of_pos ht hpos.1
        linarith
      · rw [hy] at hty
        have hZero : C.repr (z - p) 1 = 1 := by rw [← hC₁, Module.Basis.repr_self]; simp
        have hNeg : C.repr (z - p) 1 < 0 := by
          rw [hty, map_smul, Finsupp.smul_apply, smul_eq_mul]
          exact mul_neg_of_neg_of_pos ht hpos.2
        linarith
    exact ⟨w, ⟨hW.1, hqw, hcw, hAngle (Or.inl rfl)⟩,
      z, ⟨hZ.1, hqz, hcz, hAngle (Or.inr rfl)⟩, hwz, hπ, ⟨a, b, ha, hb, hInter⟩, hx⟩
  rcases pair_eq_or_swap hvu hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (hLocal he hw hz hc)
  · apply Or.inr
    apply hLocal he'
    · rwa [hSwap]
    · rwa [hSwap]
    · rwa [hSwap]

theorem endpointCreated_eq_empty_of_subsingleton {A : FinitePlanarComplex} {v u : PLPoint} {r : ℝ}
    (hN : (consecutiveNeighbors A v u).Subsingleton) : endpointCreatedFarArrowheads A v u r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨w, hw, z, hz, hwz, _, _, _⟩
  exact hwz (hN hw hz)

open scoped Classical in
theorem endpointCreated_eq_of_neighbor_pair {A : FinitePlanarComplex} {v u w z : PLPoint} {r : ℝ}
    (hwz : w ≠ z) (hN : consecutiveNeighbors A v u = {w, z}) :
    endpointCreatedFarArrowheads A v u r =
      if angle (w - v) (z - v) < Real.pi ∧
        (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ u - v = a • (w - v) + b • (z - v)) then farArrowhead v w z r else ∅ := by
  classical
  let P := angle (w - v) (z - v) < Real.pi ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ u - v = a • (w - v) + b • (z - v))
  change endpointCreatedFarArrowheads A v u r = if P then farArrowhead v w z r else ∅
  have hMem (x : PLPoint) : x ∈ endpointCreatedFarArrowheads A v u r ↔ P ∧ x ∈ farArrowhead v w z r := by
    constructor
    · rintro ⟨p, hp, q, hq, hpq, hπ, ⟨a, b, ha, hb, hRep⟩, hx⟩
      rw [hN] at hp hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · exact (hpq (hp.trans hq.symm)).elim
      · rw [hp, hq] at hπ hRep hx
        exact ⟨⟨hπ, a, b, ha, hb, hRep⟩, hx⟩
      · rw [hp, hq] at hπ hRep hx
        exact ⟨⟨by rwa [angle_comm], b, a, hb, ha, hRep.trans (add_comm _ _)⟩,
          farArrowhead_comm v z w r ▸ hx⟩
      · exact (hpq (hp.trans hq.symm)).elim
    · rintro ⟨⟨hπ, hInter⟩, hx⟩
      exact ⟨w, by rw [hN]; simp, z, by rw [hN]; simp, hwz, hπ, hInter, hx⟩
  ext x
  by_cases hP : P
  · rw [if_pos hP, hMem]
    exact and_iff_right hP
  · rw [if_neg hP, hMem]
    simp [hP]

theorem measurableSet_endpointRemovedFarArrowheads (A : FinitePlanarComplex) (v u : PLPoint) (r : ℝ) :
    MeasurableSet (endpointRemovedFarArrowheads A v u r) :=
  MeasurableSet.biUnion (countable_consecutiveNeighbors A v u) (fun w _ => measurableSet_farArrowhead v u w r)

theorem measurableSet_endpointCreatedFarArrowheads {A : FinitePlanarComplex} {v u : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) (r : ℝ) : MeasurableSet (endpointCreatedFarArrowheads A v u r) := by
  classical
  rcases consecutiveNeighbors_eq_empty_singleton_or_pair hu with hN | ⟨w, hN⟩ | ⟨w, z, hwz, hN⟩
  · rw [endpointCreated_eq_empty_of_subsingleton (by rw [hN]; exact Set.subsingleton_empty)]
    exact MeasurableSet.empty
  · rw [endpointCreated_eq_empty_of_subsingleton (by rw [hN]; exact Set.subsingleton_singleton)]
    exact MeasurableSet.empty
  · rw [endpointCreated_eq_of_neighbor_pair hwz hN]
    split
    · exact measurableSet_farArrowhead v w z r
    · exact MeasurableSet.empty

private theorem farArrowhead_subset_ball {K : FinitePlanarComplex} {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hπ : angle (u - v) (w - v) < Real.pi) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    farArrowhead v u w r ⊆ Metric.ball v (K.vertexFaceSeparation / 2) := by
  rw [farArrowhead, if_pos hπ]
  exact (sdiff_subset.trans interior_subset).trans (farKite_subset_separation_ball hu hw huw hπ hr hR)

/-- Both changes are additive over the two endpoints of the erased edge. -/
theorem volumes_changedFarArrowheads_eq_endpoint_sums {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u : PLPoint} (hvu : v ≠ u)
    (he : ({v, u} : Finset PLPoint) ∈ A.simplices.facets) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (removedFarArrowheads A {v, u} r) =
      volume (endpointRemovedFarArrowheads A v u r) + volume (endpointRemovedFarArrowheads A u v r) ∧
    volume (createdFarArrowheads A {v, u} he r) =
      volume (endpointCreatedFarArrowheads A v u r) + volume (endpointCreatedFarArrowheads A u v r) := by
  have hLift {t : Finset PLPoint} (ht : t ∈ A.edges) : t ∈ K.edges := by
    obtain ⟨hFace, hCard⟩ := (A.mem_edges_iff _).mp ht
    exact (K.mem_edges_iff _).mpr ⟨hAK hFace, hCard⟩
  have heA : ({v, u} : Finset PLPoint) ∈ A.edges :=
    (A.mem_edges_iff _).mpr ⟨(Geometry.SimplicialComplex.mem_facets.mp he).1, Finset.card_pair hvu⟩
  have heA' : ({u, v} : Finset PLPoint) ∈ A.edges := by rwa [Finset.pair_comm]
  have hsep := FinitePlanarComplex.vertexFaceSeparation_le_edge_dist (hLift heA)
  have hBalls : Disjoint (Metric.ball v (K.vertexFaceSeparation / 2)) (Metric.ball u (K.vertexFaceSeparation / 2)) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have h₁ := Metric.mem_ball.mp hx
    have h₂ := Metric.mem_ball.mp hx'
    linarith [dist_triangle_left v u x]
  have hRemoved {p q : PLPoint} (hePQ : ({p, q} : Finset PLPoint) ∈ A.edges) :
      endpointRemovedFarArrowheads A p q r ⊆ Metric.ball p (K.vertexFaceSeparation / 2) := by
    intro x hx
    obtain ⟨w, ⟨hw, hqw, _, hπ⟩, hx⟩ := Set.mem_iUnion₂.mp hx
    exact farArrowhead_subset_ball (hLift hePQ) (hLift hw) hqw hπ hr hR hx
  have hCreated (p q : PLPoint) : endpointCreatedFarArrowheads A p q r ⊆ Metric.ball p (K.vertexFaceSeparation / 2) := by
    rintro x ⟨w, hw, z, hz, hwz, hπ, _, hx⟩
    exact farArrowhead_subset_ball (hLift hw.1) (hLift hz.1) hwz hπ hr hR hx
  constructor
  · rw [removedFarArrowheads_eq_endpoint_union hvu he r,
      measure_union (hBalls.mono (hRemoved heA) (hRemoved heA')) (measurableSet_endpointRemovedFarArrowheads A u v r)]
  · rw [createdFarArrowheads_eq_endpoint_union hvu he r,
      measure_union (hBalls.mono (hCreated v u) (hCreated u v)) (measurableSet_endpointCreatedFarArrowheads heA' r)]

end SteinerProof
