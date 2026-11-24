import SteinerProof.ExtendedBody
import SteinerProof.PLComplex

set_option linter.all false

noncomputable section

namespace FinitePlanarComplex

theorem extendedBody_realization_eq_erosion
    (K : FinitePlanarComplex) (r : ℝ) (hr : 0 ≤ r) :
    extendedBody K.realization r =
      {x | Metric.closedBall x r ⊆
        offset K.realization (2 * r)} := by
  exact extendedBody_eq_erosion
    K.realization r K.isClosed_realization hr

theorem measurableSet_realization
    (K : FinitePlanarComplex) :
    MeasurableSet K.realization := by
  exact K.isClosed_realization.measurableSet

def extendedArea (K : FinitePlanarComplex) (r : ℝ) : ℝ :=
  (MeasureTheory.volume
    (extendedBody K.realization r)).toReal

end FinitePlanarComplex


namespace FinitePlanarComplex

-- A finite-radius offset of the realization is bounded.
theorem isBounded_offset_realization
    (K : FinitePlanarComplex) (r : ℝ) :
    Bornology.IsBounded (offset K.realization r) := by
  have hbounded : Bornology.IsBounded K.realization :=
    K.isBounded_realization
  have hexists :
      ∃ R : ℝ, K.realization ⊆ Metric.closedBall (0 : PLPoint) R :=
    (Metric.isBounded_iff_subset_closedBall (0 : PLPoint)).mp hbounded
  obtain ⟨R, hR⟩ := hexists
  apply (Metric.isBounded_iff_subset_closedBall (0 : PLPoint)).2
  refine ⟨R + max r 0, ?_⟩
  intro x hx
  change K.realization.Nonempty ∧
    Metric.infDist x K.realization ≤ r at hx
  obtain ⟨a, ha, hdist⟩ :=
    K.isCompact_realization.exists_infDist_eq_dist hx.1 x
  have hxa : dist x a ≤ r := by
    calc
      dist x a = Metric.infDist x K.realization := hdist.symm
      _ ≤ r := hx.2
  have ha0 : dist a (0 : PLPoint) ≤ R :=
    Metric.mem_closedBall.mp (hR ha)
  have htri :
      dist x (0 : PLPoint) ≤
        dist x a + dist a (0 : PLPoint) :=
    dist_triangle x a 0
  change dist x (0 : PLPoint) ≤ R + max r 0
  have hrmax : r ≤ max r 0 := le_max_left r 0
  linarith

-- The extended body is bounded.
theorem isBounded_extendedBody_realization
    (K : FinitePlanarComplex) (r : ℝ) (hr : 0 ≤ r) :
    Bornology.IsBounded (extendedBody K.realization r) := by
  exact (K.isBounded_offset_realization (2 * r)).subset
    (extendedBody_subset_offset_twice K.realization r hr)

-- A closed and bounded planar set is compact.
theorem isCompact_extendedBody_realization
    (K : FinitePlanarComplex) (r : ℝ) (hr : 0 ≤ r) :
    IsCompact (extendedBody K.realization r) := by
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_extendedBody K.realization r
      K.isClosed_realization hr)
    (K.isBounded_extendedBody_realization r hr)

-- Hence the extended body has finite area.
theorem volume_extendedBody_lt_top
    (K : FinitePlanarComplex) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume (extendedBody K.realization r) < ⊤ := by
  exact (K.isCompact_extendedBody_realization r hr).measure_lt_top

theorem extendedArea_zero (K : FinitePlanarComplex) :
    K.extendedArea 0 =
      (MeasureTheory.volume K.realization).toReal := by
  unfold extendedArea
  rw [extendedBody_zero_eq_of_isClosed
    K.realization K.isClosed_realization]

end FinitePlanarComplex

namespace FinitePlanarComplex

/-- The area decrement under deletion is the area of the lost region. -/
theorem extendedArea_sub_of_realization_subset
    {A B : FinitePlanarComplex} (hBA : B.realization ⊆ A.realization)
    (r : ℝ) (hr : 0 ≤ r) :
    A.extendedArea r - B.extendedArea r =
      (MeasureTheory.volume
        (extendedBody A.realization r \ extendedBody B.realization r)).toReal := by
  have hsubset := extendedBody_mono hBA r
  have hmeas := (B.isCompact_extendedBody_realization r hr).isClosed.measurableSet
  have hfinite := (B.volume_extendedBody_lt_top r hr).ne
  unfold extendedArea
  rw [MeasureTheory.measure_sdiff hsubset hmeas.nullMeasurableSet hfinite,
    ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hsubset)
      (A.volume_extendedBody_lt_top r hr).ne]

end FinitePlanarComplex
