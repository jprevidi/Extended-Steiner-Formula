import SteinerProof.PLComplex

/-! The vertex-to-face separation used for the global PL scale in Section 2.5. -/

noncomputable section

namespace FinitePlanarComplex

private def vertexFacePairs (K : FinitePlanarComplex) :
    Finset (PLPoint × Finset PLPoint) := by
  classical
  exact ((K.faceFinset.biUnion id) ×ˢ K.faceFinset).filter (fun p => p.1 ∉ p.2)

private theorem mem_vertexFacePairs (K : FinitePlanarComplex) (v : PLPoint)
    (s : Finset PLPoint) :
    (v, s) ∈ K.vertexFacePairs ↔
      v ∈ K.simplices.vertices ∧ s ∈ K.simplices.faces ∧ v ∉ s := by
  classical
  rw [K.simplices.vertices_eq]
  simp only [vertexFacePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
    mem_faceFinset_iff, id_eq, Set.mem_iUnion, Finset.mem_coe]
  grind

private def vertexFaceDistances (K : FinitePlanarComplex) : Finset ℝ := by
  classical
  exact K.vertexFacePairs.image (fun p => Metric.infDist p.1 (convexHull ℝ (p.2 : Set PLPoint)))

/-- The minimum distance over nonincident vertex-face pairs.
When the index is empty, any finite positive bound is valid. -/
def vertexFaceSeparation (K : FinitePlanarComplex) : ℝ :=
  if h : K.vertexFaceDistances.Nonempty then K.vertexFaceDistances.min' h else 1

theorem vertexFaceSeparation_pos (K : FinitePlanarComplex) : 0 < K.vertexFaceSeparation := by
  classical
  unfold vertexFaceSeparation
  split
  next h =>
    have hm := Finset.min'_mem K.vertexFaceDistances h
    obtain ⟨⟨v, s⟩, hp, heq⟩ := Finset.mem_image.mp hm
    obtain ⟨hv, hs, hvs⟩ := (K.mem_vertexFacePairs v s).mp hp
    have hclosed := s.finite_toSet.isClosed_convexHull ℝ
    have hnonempty : (convexHull ℝ (s : Set PLPoint)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr
        (K.simplices.nonempty_of_mem_faces hs))
    have hnot : v ∉ convexHull ℝ (s : Set PLPoint) :=
      fun hmem => hvs ((K.simplices.vertex_mem_convexHull_iff hv hs).mp hmem)
    exact heq ▸ (hclosed.notMem_iff_infDist_pos hnonempty).mp hnot
  next => exact zero_lt_one

theorem vertexFaceSeparation_le_dist (K : FinitePlanarComplex) {v x : PLPoint}
    {s : Finset PLPoint} (hv : v ∈ K.simplices.vertices) (hs : s ∈ K.simplices.faces)
    (hvs : v ∉ s) (hx : x ∈ convexHull ℝ (s : Set PLPoint)) :
    K.vertexFaceSeparation ≤ dist v x := by
  classical
  have hm : Metric.infDist v (convexHull ℝ (s : Set PLPoint)) ∈ K.vertexFaceDistances := by
    exact Finset.mem_image.mpr ⟨(v, s), (K.mem_vertexFacePairs v s).mpr ⟨hv, hs, hvs⟩, rfl⟩
  rw [vertexFaceSeparation, dif_pos ⟨_, hm⟩]
  exact (Finset.min'_le _ _ hm).trans (Metric.infDist_le_dist_of_mem hx)

end FinitePlanarComplex
