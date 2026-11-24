import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option linter.all false

noncomputable section

abbrev PLPoint := EuclideanSpace ℝ (Fin 2)

structure FinitePlanarComplex where
  simplices : Geometry.SimplicialComplex ℝ PLPoint
  finite_faces : simplices.faces.Finite

namespace FinitePlanarComplex

def faceFinset (K : FinitePlanarComplex) :
    Finset (Finset PLPoint) := by
  classical
  exact K.finite_faces.toFinset

theorem mem_faceFinset_iff
    (K : FinitePlanarComplex) (s : Finset PLPoint) :
    s ∈ K.faceFinset ↔ s ∈ K.simplices.faces := by
  classical
  simp [faceFinset]

def vertices (K : FinitePlanarComplex) :
    Finset (Finset PLPoint) :=
  K.faceFinset.filter (fun s => s.card = 1)

def edges (K : FinitePlanarComplex) :
    Finset (Finset PLPoint) :=
  K.faceFinset.filter (fun s => s.card = 2)

def triangles (K : FinitePlanarComplex) :
    Finset (Finset PLPoint) :=
  K.faceFinset.filter (fun s => s.card = 3)

def eulerChar (K : FinitePlanarComplex) : ℤ :=
  (K.vertices.card : ℤ) -
  (K.edges.card : ℤ) +
  (K.triangles.card : ℤ)

theorem mem_edges_iff
    (K : FinitePlanarComplex) (s : Finset PLPoint) :
    s ∈ K.edges ↔
      s ∈ K.simplices.faces ∧ s.card = 2 := by
  classical
  simp [edges, faceFinset]

end FinitePlanarComplex


namespace FinitePlanarComplex

-- For two vertices, this gives the edge length.
-- For three vertices, it gives the triangle perimeter.
def boundaryLength (s : Finset PLPoint) : ℝ :=
  (∑ p ∈ s, ∑ q ∈ s, dist p q) / 2

def edgeLength (s : Finset PLPoint) : ℝ :=
  boundaryLength s

def trianglePerimeter (s : Finset PLPoint) : ℝ :=
  boundaryLength s

-- The ordinary two-dimensional area of a triangle.
def triangleArea (s : Finset PLPoint) : ℝ :=
  (MeasureTheory.volume
    (convexHull ℝ (s : Set PLPoint))).toReal

-- Check that our edge-length formula gives the usual distance.
theorem edgeLength_pair (p q : PLPoint) (hpq : p ≠ q) :
    edgeLength ({p, q} : Finset PLPoint) = dist p q := by
  classical
  simp [edgeLength, boundaryLength, hpq, dist_comm] <;> ring

end FinitePlanarComplex


namespace FinitePlanarComplex

-- Sum of the areas of all triangles.
def totalArea (K : FinitePlanarComplex) : ℝ :=
  ∑ t ∈ K.triangles, triangleArea t

-- Sum of the lengths of all edges.
def totalEdgeLength (K : FinitePlanarComplex) : ℝ :=
  ∑ e ∈ K.edges, edgeLength e

-- Sum of the perimeters of all triangles.
def totalTrianglePerimeter (K : FinitePlanarComplex) : ℝ :=
  ∑ t ∈ K.triangles, trianglePerimeter t

-- Twice the first intrinsic-volume coefficient.
def twiceV1 (K : FinitePlanarComplex) : ℝ :=
  2 * K.totalEdgeLength - K.totalTrianglePerimeter

-- The simplicial Steiner polynomial.
def steinerPolynomial (K : FinitePlanarComplex) (r : ℝ) : ℝ :=
  K.totalArea + r * K.twiceV1
    + Real.pi * r ^ 2 * (K.eulerChar : ℝ)

-- At radius zero, only the area term remains.
theorem steinerPolynomial_zero (K : FinitePlanarComplex) :
    K.steinerPolynomial 0 = K.totalArea := by
  simp [steinerPolynomial]

-- Expand the polynomial into explicit finite sums.
theorem steinerPolynomial_expanded
    (K : FinitePlanarComplex) (r : ℝ) :
    K.steinerPolynomial r =
      (∑ t ∈ K.triangles, triangleArea t)
      + r * (2 * (∑ e ∈ K.edges, edgeLength e)
        - (∑ t ∈ K.triangles, trianglePerimeter t))
      + Real.pi * r ^ 2 * (K.eulerChar : ℝ) := by
  rfl

end FinitePlanarComplex


namespace FinitePlanarComplex

-- The actual subset of the plane represented by K.
def realization (K : FinitePlanarComplex) : Set PLPoint :=
  K.simplices.space

-- A point belongs to the realization precisely when
-- it lies in one of the complex's geometric simplices.
theorem mem_realization_iff
    (K : FinitePlanarComplex) (x : PLPoint) :
    x ∈ K.realization ↔
      ∃ s ∈ K.simplices.faces,
        x ∈ convexHull ℝ (s : Set PLPoint) := by
  exact Geometry.SimplicialComplex.mem_space_iff

-- Every face is contained in the realization.
theorem convexHull_face_subset_realization
    (K : FinitePlanarComplex) (s : Finset PLPoint)
    (hs : s ∈ K.simplices.faces) :
    convexHull ℝ (s : Set PLPoint) ⊆ K.realization := by
  exact Geometry.SimplicialComplex.convexHull_subset_space hs

end FinitePlanarComplex


namespace FinitePlanarComplex

theorem isClosed_realization (K : FinitePlanarComplex) :
    IsClosed K.realization := by
  change IsClosed
    (⋃ s ∈ K.simplices.faces,
      convexHull ℝ (s : Set PLPoint))
  apply K.finite_faces.isClosed_biUnion
  intro s hs
  exact (s.finite_toSet).isClosed_convexHull ℝ

end FinitePlanarComplex


namespace FinitePlanarComplex

-- A finite planar simplicial complex has compact realization.
theorem isCompact_realization (K : FinitePlanarComplex) :
    IsCompact K.realization := by
  change IsCompact
    (⋃ s ∈ K.simplices.faces,
      convexHull ℝ (s : Set PLPoint))
  apply K.finite_faces.isCompact_biUnion
  intro s hs
  exact (s.finite_toSet).isCompact_convexHull ℝ

-- Every compact subset of the plane is bounded.
theorem isBounded_realization (K : FinitePlanarComplex) :
    Bornology.IsBounded K.realization := by
  exact K.isCompact_realization.isBounded

-- The realization has finite Lebesgue area.
theorem volume_realization_lt_top (K : FinitePlanarComplex) :
    MeasureTheory.volume K.realization < ⊤ := by
  exact K.isCompact_realization.measure_lt_top

end FinitePlanarComplex


namespace FinitePlanarComplex
