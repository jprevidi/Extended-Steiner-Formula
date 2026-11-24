import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import SteinerProof.FacetDeletion

/-! The contributions of relatively open simplices to the Steiner polynomial. -/

noncomputable section

namespace FinitePlanarComplex

/-- The open-simplex values in Section 2.1, expressed through the closed face. -/
def steinerFaceContribution (s : Finset PLPoint) (r : ℝ) : ℝ :=
  if s.card = 3 then triangleArea s - r * trianglePerimeter s + Real.pi * r ^ 2
  else if s.card = 2 then 2 * r * edgeLength s - Real.pi * r ^ 2
  else Real.pi * r ^ 2

private theorem sum_filter_sub_erase {F : Finset (Finset PLPoint)} {s : Finset PLPoint}
    [DecidableEq (Finset PLPoint)] (hs : s ∈ F)
    (p : Finset PLPoint → Prop) [DecidablePred p] (f : Finset PLPoint → ℝ) :
    (∑ t ∈ F.filter p, f t) - (∑ t ∈ (F.erase s).filter p, f t) =
      if p s then f s else 0 := by
  rw [Finset.filter_erase]
  by_cases h : p s
  · have hmem : s ∈ F.filter p := Finset.mem_filter.mpr ⟨hs, h⟩
    rw [ite_eq_left h]
    exact sub_eq_of_eq_add ((Finset.sum_erase_add (F.filter p) f hmem).symm.trans (add_comm _ _))
  · have hnot : s ∉ F.filter p := fun hx => h (Finset.mem_filter.mp hx).2
    rw [ite_eq_right h, Finset.erase_eq_of_notMem hnot, sub_self]

theorem steinerPolynomial_sub_eraseFacet (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.facets) (r : ℝ) :
    K.steinerPolynomial r - (K.eraseFacet s hs).steinerPolynomial r =
      steinerFaceContribution s r := by
  classical
  have hsFace := (Geometry.SimplicialComplex.mem_facets.mp hs).1
  have hsFin := (K.mem_faceFinset_iff s).mpr hsFace
  have hpos := Finset.card_pos.mpr (K.simplices.nonempty_of_mem_faces hsFace)
  have hdim : s.card ≤ 3 := by
    have h := (K.simplices.indep hsFace).card_le_finrank_succ
    have hle := Submodule.finrank_le (vectorSpan ℝ
      (Set.range ((↑) : s → PLPoint)))
    simp only [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at hle
    omega
  have hArea := sum_filter_sub_erase hsFin (fun t => t.card = 3) triangleArea
  have hEdge := sum_filter_sub_erase hsFin (fun t => t.card = 2) edgeLength
  have hPerim := sum_filter_sub_erase hsFin (fun t => t.card = 3) trianglePerimeter
  have hCard (n : ℕ) :
      ((K.faceFinset.filter (fun t => t.card = n)).card : ℝ) -
        (((K.faceFinset.erase s).filter (fun t => t.card = n)).card : ℝ) =
          if s.card = n then 1 else 0 := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      sum_filter_sub_erase hsFin (fun t => t.card = n) (fun _ => 1)
  have h1 := hCard 1
  have h2 := hCard 2
  have h3 := hCard 3
  simp only [steinerPolynomial, totalArea, twiceV1, totalEdgeLength, totalTrianglePerimeter,
    eulerChar, vertices, edges, triangles, faceFinset_eraseFacet, Int.cast_sub, Int.cast_add,
    Int.cast_natCast]
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hcard | hcard | hcard <;>
    simp [steinerFaceContribution, hcard] at hArea hEdge hPerim h1 h2 h3 ⊢ <;>
    linear_combination hArea + 2 * r * hEdge - r * hPerim +
      Real.pi * r ^ 2 * (h1 - h2 + h3)

end FinitePlanarComplex
