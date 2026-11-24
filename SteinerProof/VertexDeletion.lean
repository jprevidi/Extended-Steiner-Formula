import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import SteinerProof.ExtendedBody

/-! The isolated vertex deletion of Section 6.2. -/

open Set

noncomputable section

/-- The radius-`r` ball about a point of the erosion cannot switch between
two sufficiently separated components of the radius-`2r` offset. -/
private theorem extendedBody_union_of_separated {A B : Set Point2}
    (hA : IsClosed A) (hB : IsClosed B) {r : ℝ} (hr : 0 ≤ r)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, 5 * r < dist a b) :
    extendedBody (A ∪ B) r = extendedBody A r ∪ extendedBody B r := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have hball := extendedBody_subset_erosion (A ∪ B) r hx
    obtain ⟨z, hz, hxz⟩ :=
      (mem_offset_iff_exists_dist_le (hA.union hB)).mp
        (hball (Metric.mem_closedBall_self hr))
    rcases hz with hzA | hzB
    · apply Or.inl
      apply erosion_subset_extendedBody A r hA hr
      intro y hy
      obtain ⟨w, hw, hyw⟩ := (mem_offset_iff_exists_dist_le (hA.union hB)).mp (hball hy)
      rcases hw with hwA | hwB
      · exact (mem_offset_iff_exists_dist_le hA).mpr ⟨w, hwA, hyw⟩
      · have hzy := dist_triangle z x y
        have hzw := dist_triangle z y w
        rw [dist_comm z x, dist_comm x y] at hzy
        linarith [Metric.mem_closedBall.mp hy, hsep z hzA w hwB]
    · apply Or.inr
      apply erosion_subset_extendedBody B r hB hr
      intro y hy
      obtain ⟨w, hw, hyw⟩ := (mem_offset_iff_exists_dist_le (hA.union hB)).mp (hball hy)
      rcases hw with hwA | hwB
      · have hwx := dist_triangle w y x
        have hwz := dist_triangle w x z
        rw [dist_comm w y] at hwx
        linarith [Metric.mem_closedBall.mp hy, hsep w hwA z hzB]
      · exact (mem_offset_iff_exists_dist_le hB).mpr ⟨w, hwB, hyw⟩
  · rintro x (hx | hx)
    · exact extendedBody_mono subset_union_left r hx
    · exact extendedBody_mono subset_union_right r hx

/-- Deleting a separated vertex removes exactly its closed radius-`r` disk. -/
theorem extendedBody_sdiff_isolated_vertex {B : Set Point2} (hB : IsClosed B)
    {z : Point2} {r : ℝ} (hr : 0 ≤ r)
    (hsep : ∀ b ∈ B, 5 * r < dist b z) :
    extendedBody (B ∪ {z}) r \ extendedBody B r = Metric.closedBall z r := by
  have hsingle : extendedBody ({z} : Set Point2) r = Metric.closedBall z r := by
    rw [extendedBody_eq_offset_of_convex isClosed_singleton (convex_singleton z) hr]
    ext x
    simp [offset, Metric.mem_closedBall]
  rw [extendedBody_union_of_separated hB isClosed_singleton hr
    (fun b hb a ha => by simpa only [Set.mem_singleton_iff.mp ha] using hsep b hb),
    hsingle]
  ext x
  constructor
  · rintro ⟨hx | hx, hnot⟩
    · exact (hnot hx).elim
    · exact hx
  · intro hx
    refine ⟨Or.inr hx, fun hxB => ?_⟩
    obtain ⟨b, hb, hxb⟩ := (mem_offset_iff_exists_dist_le hB).mp
      (extendedBody_subset_offset_twice B r hr hxB)
    have htri := dist_triangle b x z
    rw [dist_comm b x] at htri
    linarith [Metric.mem_closedBall.mp hx, hsep b hb]

theorem volume_extendedBody_sdiff_isolated_vertex {B : Set Point2} (hB : IsClosed B)
    {z : Point2} {r : ℝ} (hr : 0 ≤ r)
    (hsep : ∀ b ∈ B, 5 * r < dist b z) :
    (MeasureTheory.volume (extendedBody (B ∪ {z}) r \ extendedBody B r)).toReal =
      Real.pi * r ^ 2 := by
  rw [extendedBody_sdiff_isolated_vertex hB hr hsep, EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_pos.le, mul_comm]
