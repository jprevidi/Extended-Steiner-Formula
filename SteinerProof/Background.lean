import SteinerProof.ExtendedBody
import SteinerProof.SimplicialArea

/-! Background inputs used by the paper's planar deletion proof.

The ordinary offset formulas in Section 6 are collected in
`OrdinaryPlanarSteiner`. The refinement data records the compatibility and
polynomial invariance used to transport the deletion induction. The construction
of compatible refinements is proved in `HullFilling`.
-/

noncomputable section

namespace FinitePlanarComplex

/-- The ordinary offset area formula for the closed triangle of a face. -/
def TriangleOffsetFormula (s : Finset PLPoint) : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    (MeasureTheory.volume (offset (convexHull ℝ (s : Set PLPoint)) r)).toReal =
      triangleArea s + r * trianglePerimeter s + Real.pi * r ^ 2

/-- The ordinary offset area formula at the convex seed, expressed in the
simplicial coefficients. This includes their normalization on the seed. -/
def ConvexOffsetFormulaAt (C : FinitePlanarComplex) (r : ℝ) : Prop :=
  (MeasureTheory.volume (offset C.realization r)).toReal = C.steinerPolynomial r

/-- The ordinary planar Steiner formula in the two forms used in Section 6.
On a convex triangulated set the formula uses the simplicial coefficients. -/
structure OrdinaryPlanarSteiner : Prop where
  convexOffset (C : FinitePlanarComplex) : C.realization.Nonempty → Convex ℝ C.realization →
    ∀ r : ℝ, 0 ≤ r → ConvexOffsetFormulaAt C r
  triangleOffset (C : FinitePlanarComplex) : ∀ s ∈ C.triangles, TriangleOffsetFormula s

/-- A triangulation of the convex hull together with a subcomplex that
represents the original realization and preserves its Steiner coefficients. -/
structure CompatibleHullRefinement (A : FinitePlanarComplex) where
  hull : FinitePlanarComplex
  target : FinitePlanarComplex
  target_faces_subset : target.simplices.faces ⊆ hull.simplices.faces
  hull_realization : hull.realization = convexHull ℝ A.realization
  target_realization : target.realization = A.realization
  target_twiceV1 : target.twiceV1 = A.twiceV1
  target_eulerChar : target.eulerChar = A.eulerChar

/-- The constant coefficient follows from equality of realizations.
Only the other two coefficients need to be supplied by the refinement. -/
theorem CompatibleHullRefinement.target_polynomial {A : FinitePlanarComplex}
    (H : CompatibleHullRefinement A) (r : ℝ) :
    H.target.steinerPolynomial r = A.steinerPolynomial r := by
  simp only [steinerPolynomial, totalArea_eq_volume_realization, H.target_realization,
    H.target_twiceV1, H.target_eulerChar]

end FinitePlanarComplex
