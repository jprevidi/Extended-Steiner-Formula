import SteinerProof.ArrowheadExterior

/-! The exterior arrowhead pieces lost and created by erasing an open edge. -/

open Set InnerProductGeometry MeasureTheory

noncomputable section

namespace SteinerProof

private def exteriorFarArrowheadsWith (A : FinitePlanarComplex) (r : ℝ)
    (P : PLPoint → PLPoint → PLPoint → Prop) : Set PLPoint :=
  {x | ∃ v u w : PLPoint, ({v, u} : Finset PLPoint) ∈ A.edges ∧
    ({v, w} : Finset PLPoint) ∈ A.edges ∧ u ≠ w ∧ ConsecutiveIncident A v u w ∧
    angle (u - v) (w - v) < Real.pi ∧ ({v, u, w} : Finset PLPoint) ∉ A.simplices.faces ∧
    P v u w ∧ x ∈ farArrowhead v u w r}

/-- The exterior far arrowheads supplied by pairs containing the erased edge. -/
def removedFarArrowheads (A : FinitePlanarComplex) (s : Finset PLPoint) (r : ℝ) : Set PLPoint :=
  exteriorFarArrowheadsWith A r fun v u w => {v, u} = s ∨ {v, w} = s

/-- The exterior far arrowheads of pairs made consecutive by the deletion. -/
def createdFarArrowheads (A : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ A.simplices.facets) (r : ℝ) : Set PLPoint :=
  exteriorFarArrowheadsWith (A.eraseFacet s hs) r fun v u w => ¬ ConsecutiveIncident A v u w

theorem removedFarArrowheads_subset {A : FinitePlanarComplex} {s : Finset PLPoint} {r : ℝ} :
    removedFarArrowheads A s r ⊆ exteriorFarArrowheads A r := by
  rintro x ⟨v, u, w, hu, hw, huw, hc, hπ, hext, _, hx⟩
  exact ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩

theorem createdFarArrowheads_subset {A : FinitePlanarComplex} {s : Finset PLPoint}
    {hs : s ∈ A.simplices.facets} {r : ℝ} :
    createdFarArrowheads A s hs r ⊆ exteriorFarArrowheads (A.eraseFacet s hs) r := by
  rintro x ⟨v, u, w, hu, hw, huw, hc, hπ, hext, _, hx⟩
  exact ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩

theorem measurableSet_farArrowhead (v u w : PLPoint) (r : ℝ) : MeasurableSet (farArrowhead v u w r) := by
  unfold farArrowhead
  split
  · exact isOpen_interior.measurableSet.diff Metric.isOpen_ball.measurableSet
  · exact MeasurableSet.empty

private theorem measurableSet_exteriorFarArrowheadsWith (A : FinitePlanarComplex) (r : ℝ)
    (P : PLPoint → PLPoint → PLPoint → Prop) : MeasurableSet (exteriorFarArrowheadsWith A r P) := by
  classical
  let V : Set PLPoint := (A.faceFinset.biUnion id : Finset PLPoint)
  let T : Set (PLPoint × PLPoint × PLPoint) := {p |
    ({p.1, p.2.1} : Finset PLPoint) ∈ A.edges ∧ ({p.1, p.2.2} : Finset PLPoint) ∈ A.edges ∧
    p.2.1 ≠ p.2.2 ∧ ConsecutiveIncident A p.1 p.2.1 p.2.2 ∧
    angle (p.2.1 - p.1) (p.2.2 - p.1) < Real.pi ∧
    ({p.1, p.2.1, p.2.2} : Finset PLPoint) ∉ A.simplices.faces ∧ P p.1 p.2.1 p.2.2}
  have hV : V.Finite := Finset.finite_toSet _
  have hEndpoints {v u : PLPoint} (he : ({v, u} : Finset PLPoint) ∈ A.edges) : v ∈ V ∧ u ∈ V := by
    have hF := (A.mem_faceFinset_iff _).mpr ((A.mem_edges_iff _).mp he).1
    exact ⟨Finset.mem_biUnion.mpr ⟨{v, u}, hF, by simp⟩, Finset.mem_biUnion.mpr ⟨{v, u}, hF, by simp⟩⟩
  have hT : T.Finite := (hV.prod (hV.prod hV)).subset (by
    rintro ⟨v, u, w⟩ ⟨hu, hw, _, _, _, _, _⟩
    exact ⟨(hEndpoints hu).1, (hEndpoints hu).2, (hEndpoints hw).2⟩)
  have hEq : exteriorFarArrowheadsWith A r P = ⋃ p ∈ T, farArrowhead p.1 p.2.1 p.2.2 r := by
    ext x
    constructor
    · rintro ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hP, hx⟩
      exact Set.mem_iUnion₂.mpr ⟨(v, u, w), ⟨hu, hw, huw, hc, hπ, hext, hP⟩, hx⟩
    · intro hx
      obtain ⟨⟨v, u, w⟩, ⟨hu, hw, huw, hc, hπ, hext, hP⟩, hfar⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hP, hfar⟩
  rw [hEq]
  exact MeasurableSet.biUnion hT.countable (fun p _ => measurableSet_farArrowhead p.1 p.2.1 p.2.2 r)

theorem measurableSet_removedFarArrowheads (A : FinitePlanarComplex) (s : Finset PLPoint) (r : ℝ) :
    MeasurableSet (removedFarArrowheads A s r) := measurableSet_exteriorFarArrowheadsWith _ _ _

theorem measurableSet_createdFarArrowheads (A : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ A.simplices.facets) (r : ℝ) :
    MeasurableSet (createdFarArrowheads A s hs r) := measurableSet_exteriorFarArrowheadsWith _ _ _

theorem mem_edges_eraseFacet_iff {A : FinitePlanarComplex} {s e : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) : e ∈ (A.eraseFacet s hs).edges ↔ e ∈ A.edges ∧ e ≠ s := by
  rw [(A.eraseFacet s hs).mem_edges_iff, A.mem_edges_iff, A.faces_eraseFacet]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

private theorem consecutiveIncident_eraseFacet {A : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) {v u w : PLPoint} (hc : ConsecutiveIncident A v u w) :
    ConsecutiveIncident (A.eraseFacet s hs) v u w := by
  intro y hy hyu hyw
  exact hc y ((mem_edges_eraseFacet_iff hs).mp hy).1 hyu hyw

theorem consecutiveIncident_swap {A : FinitePlanarComplex} {v u w : PLPoint}
    (hc : ConsecutiveIncident A v u w) : ConsecutiveIncident A v w u := by
  intro y hy hyw hyu
  rintro ⟨a, b, ha, hb, hrep⟩
  exact hc y hy hyu hyw ⟨b, a, hb, ha, hrep.trans (add_comm _ _)⟩

theorem pair_eq_or_swap {u w g h : PLPoint} (hgh : g ≠ h)
    (hPair : ({u, w} : Finset PLPoint) = {g, h}) : (g = u ∧ h = w) ∨ (g = w ∧ h = u) := by
  have hg : g ∈ ({u, w} : Finset PLPoint) := hPair.symm ▸ (by simp : g ∈ ({g, h} : Finset PLPoint))
  have hh : h ∈ ({u, w} : Finset PLPoint) := hPair.symm ▸ (by simp : h ∈ ({g, h} : Finset PLPoint))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · exact (hgh (hg.trans hh.symm)).elim
  · exact Or.inl ⟨hg, hh⟩
  · exact Or.inr ⟨hg, hh⟩
  · exact (hgh (hg.trans hh.symm)).elim

private theorem consecutive_pairs_aligned_of_common_farArrowhead {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {v u w z g h x : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ A.edges) (hw : ({v, w} : Finset PLPoint) ∈ A.edges)
    (hg : ({z, g} : Finset PLPoint) ∈ A.edges) (hh : ({z, h} : Finset PLPoint) ∈ A.edges)
    (huw : u ≠ w) (hgh : g ≠ h) (hc₁ : ConsecutiveIncident A v u w) (hc₂ : ConsecutiveIncident A z g h)
    (hπ₁ : angle (u - v) (w - v) < Real.pi) (hπ₂ : angle (g - z) (h - z) < Real.pi)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (hx₁ : x ∈ farArrowhead v u w r) (hx₂ : x ∈ farArrowhead z g h r) :
    v = z ∧ ((g = u ∧ h = w) ∨ (g = w ∧ h = u)) := by
  have hnot (h : v ≠ z ∨ ({u, w} : Finset PLPoint) ≠ {g, h}) : False :=
    Set.disjoint_left.mp
      (disjoint_farArrowheads_of_distinct_consecutive_pairs hAK hu hw hg hh huw hgh hc₁ hc₂ hπ₁ hπ₂ h hr hR) hx₁ hx₂
  refine ⟨not_not.mp (fun hv => hnot (Or.inl hv)), pair_eq_or_swap hgh ?_⟩
  exact not_not.mp (fun hp => hnot (Or.inr hp))

private theorem exterior_of_exterior_eraseEdge {A : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges)
    (hw : ({v, w} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges)
    (huw : u ≠ w) (hs₂ : s.card = 2)
    (hext : ({v, u, w} : Finset PLPoint) ∉ (A.eraseFacet s hs).simplices.faces) :
    ({v, u, w} : Finset PLPoint) ∉ A.simplices.faces := by
  intro h
  apply hext
  refine ⟨h, ?_⟩
  intro heq
  have hcard : ({v, u, w} : Finset PLPoint).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [FinitePlanarComplex.edge_endpoints_ne hu |>.symm,
      FinitePlanarComplex.edge_endpoints_ne hw |>.symm]), Finset.card_pair huw]
  rw [Set.mem_singleton_iff] at heq
  rw [heq, hs₂] at hcard
  omega

/-- The surviving exterior far arrowheads, together with the newly
consecutive ones, give the exterior far arrowheads after erasing an edge. -/
theorem exteriorFarArrowheads_eraseEdge_eq {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {s : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) (hs₂ : s.card = 2) {r : ℝ}
    (hr : 0 < r) (hR : r < K.admissibleRadius) :
    exteriorFarArrowheads (A.eraseFacet s hs) r =
      (exteriorFarArrowheads A r \ removedFarArrowheads A s r) ∪ createdFarArrowheads A s hs r := by
  ext x
  constructor
  · rintro ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩
    by_cases hcA : ConsecutiveIncident A v u w
    · obtain ⟨huA, huNe⟩ := (mem_edges_eraseFacet_iff hs).mp hu
      obtain ⟨hwA, hwNe⟩ := (mem_edges_eraseFacet_iff hs).mp hw
      refine Or.inl ⟨⟨v, u, w, huA, hwA, huw, hcA, hπ,
        exterior_of_exterior_eraseEdge hs hu hw huw hs₂ hext, hx⟩, ?_⟩
      rintro ⟨z, g, h, hg, hh, hgh, hcGH, hπGH, _, hRemoved, hxGH⟩
      obtain ⟨rfl, hPair⟩ := consecutive_pairs_aligned_of_common_farArrowhead hAK huA hwA hg hh
        huw hgh hcA hcGH hπ hπGH hr hR hx hxGH
      rcases hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hRemoved.elim huNe hwNe
      · exact hRemoved.elim hwNe huNe
    · exact Or.inr ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hcA, hx⟩
  · rintro (⟨⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩, hn⟩ |
        ⟨v, u, w, hu, hw, huw, hc, hπ, hext, _, hx⟩)
    · have hne : ¬ ({v, u} : Finset PLPoint) = s ∧ ¬ ({v, w} : Finset PLPoint) = s := by
        push Not
        by_contra h
        apply hn
        refine ⟨v, u, w, hu, hw, huw, hc, hπ, hext, ?_, hx⟩
        tauto
      exact ⟨v, u, w, (mem_edges_eraseFacet_iff hs).mpr ⟨hu, hne.1⟩,
        (mem_edges_eraseFacet_iff hs).mpr ⟨hw, hne.2⟩, huw, consecutiveIncident_eraseFacet hs hc,
        hπ, fun h => hext h.1, hx⟩
    · exact ⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩

/-- Surviving and newly consecutive pairs give disjoint pieces after deletion. -/
theorem disjoint_surviving_createdFarArrowheads {K A : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces) {s : Finset PLPoint} (hs : s ∈ A.simplices.facets)
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    Disjoint (exteriorFarArrowheads A r \ removedFarArrowheads A s r) (createdFarArrowheads A s hs r) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨⟨v, u, w, hu, hw, huw, hc, hπ, hext, hx⟩, hn⟩
    ⟨z, g, h, hg, hh, hgh, hcGH, hπGH, _, hNew, hxGH⟩
  have huB : ({v, u} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges :=
    (mem_edges_eraseFacet_iff hs).mpr ⟨hu, fun heq => hn ⟨v, u, w, hu, hw, huw, hc, hπ, hext, Or.inl heq, hx⟩⟩
  have hwB : ({v, w} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges :=
    (mem_edges_eraseFacet_iff hs).mpr ⟨hw, fun heq => hn ⟨v, u, w, hu, hw, huw, hc, hπ, hext, Or.inr heq, hx⟩⟩
  have hBK : (A.eraseFacet s hs).simplices.faces ⊆ K.simplices.faces := fun _ h => hAK h.1
  obtain ⟨rfl, hPair⟩ := consecutive_pairs_aligned_of_common_farArrowhead hBK
    huB hwB hg hh huw hgh (consecutiveIncident_eraseFacet hs hc) hcGH hπ hπGH hr hR hx hxGH
  rcases hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hNew hc
  · exact hNew (consecutiveIncident_swap hc)

/-- A pair becomes consecutive precisely when the erased edge was the
sole interior edge in its sector, among pairs that survive the deletion. -/
theorem not_consecutiveIncident_iff_erased_edge_inside {A : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ A.simplices.facets) {v u w : PLPoint}
    (hu : ({v, u} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges)
    (hw : ({v, w} : Finset PLPoint) ∈ (A.eraseFacet s hs).edges)
    (hs₂ : s.card = 2) (hc : ConsecutiveIncident (A.eraseFacet s hs) v u w) :
    (¬ ConsecutiveIncident A v u w) ↔ ∃ y : PLPoint, ({v, y} : Finset PLPoint) = s ∧
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ y - v = a • (u - v) + b • (w - v) := by
  classical
  constructor
  · intro hOld
    unfold ConsecutiveIncident at hOld
    push Not at hOld
    obtain ⟨y, hy, hyu, hyw, hcomb⟩ := hOld
    have hyS : ({v, y} : Finset PLPoint) = s := by
      by_contra hn
      exact hc y ((mem_edges_eraseFacet_iff hs).mpr ⟨hy, hn⟩) hyu hyw hcomb
    exact ⟨y, hyS, hcomb⟩
  · rintro ⟨y, hy, hComb⟩ hOld
    have hsE : s ∈ A.edges := (A.mem_edges_iff _).mpr ⟨(Geometry.SimplicialComplex.mem_facets.mp hs).1, hs₂⟩
    have hyE : ({v, y} : Finset PLPoint) ∈ A.edges := hy.symm ▸ hsE
    have hyu : y ≠ u := fun h => ((mem_edges_eraseFacet_iff hs).mp hu).2 (h ▸ hy)
    have hyw : y ≠ w := fun h => ((mem_edges_eraseFacet_iff hs).mp hw).2 (h ▸ hy)
    exact hOld y hyE hyu hyw hComb

end SteinerProof
