import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

set_option linter.all false

open Set

noncomputable section

abbrev Point2 := EuclideanSpace ℝ (Fin 2)

def offset (A : Set Point2) (r : ℝ) : Set Point2 :=
  {x | A.Nonempty ∧ Metric.infDist x A ≤ r}

def extendedBody (A : Set Point2) (r : ℝ) : Set Point2 :=
  {x | ∀ c : Point2, dist x c ≤ r →
    (Metric.closedBall c r ∩ offset A r).Nonempty}

theorem offset_subset_extendedBody (A : Set Point2) (r : ℝ) :
    offset A r ⊆ extendedBody A r := by
  intro x hx
  change ∀ c : Point2, dist x c ≤ r →
    (Metric.closedBall c r ∩ offset A r).Nonempty
  intro c hxc
  refine ⟨x, ?_⟩
  exact ⟨(Metric.mem_closedBall).2 hxc, hx⟩


theorem extendedBody_subset_erosion (A : Set Point2) (r : ℝ) :
    extendedBody A r ⊆
      {x | Metric.closedBall x r ⊆ offset A (2 * r)} := by
  intro x hx
  intro c hc

  have hxc : dist x c ≤ r := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hc)

  obtain ⟨y, hyball, hyoffset⟩ := hx c hxc

  have hcy : dist c y ≤ r := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hyball)

  change A.Nonempty ∧ Metric.infDist y A ≤ r at hyoffset
  rcases hyoffset with ⟨hA, hyA⟩

  have htri :
      Metric.infDist c A ≤ Metric.infDist y A + dist c y :=
    Metric.infDist_le_infDist_add_dist

  change A.Nonempty ∧ Metric.infDist c A ≤ 2 * r
  constructor
  · exact hA
  · linarith


theorem erosion_subset_extendedBody
    (A : Set Point2) (r : ℝ)
    (hclosed : IsClosed A) (hr : 0 ≤ r) :
    {x | Metric.closedBall x r ⊆ offset A (2 * r)}
      ⊆ extendedBody A r := by
  intro x hx
  change ∀ c : Point2, dist x c ≤ r →
    (Metric.closedBall c r ∩ offset A r).Nonempty
  intro c hxc
  have hcball : c ∈ Metric.closedBall x r := by
    apply Metric.mem_closedBall.mpr
    simpa [dist_comm] using hxc
  have hcoffset := hx hcball
  change A.Nonempty ∧ Metric.infDist c A ≤ 2 * r at hcoffset
  obtain ⟨a, ha, hnear⟩ :=
    hclosed.exists_infDist_eq_dist hcoffset.1 c
  have hca : dist c a ≤ 2 * r := by
    rw [← hnear]
    exact hcoffset.2
  let m : Point2 := midpoint ℝ c a
  have hcm : dist c m = dist c a / 2 := by
    dsimp [m]
    rw [dist_left_midpoint]
    norm_num <;> ring
  have hma : dist m a = dist c a / 2 := by
    dsimp [m]
    rw [dist_midpoint_right]
    norm_num <;> ring
  have hmA : Metric.infDist m A ≤ r := by
    have hbound : Metric.infDist m A ≤ dist m a :=
      Metric.infDist_le_dist_of_mem ha
    linarith [hr]
  refine ⟨m, ?_⟩
  change m ∈ Metric.closedBall c r ∩ offset A r
  constructor
  · apply Metric.mem_closedBall.mpr
    rw [dist_comm m c, hcm]
    linarith
  · change A.Nonempty ∧ Metric.infDist m A ≤ r
    exact ⟨hcoffset.1, hmA⟩


theorem extendedBody_eq_erosion
    (A : Set Point2) (r : ℝ)
    (hclosed : IsClosed A) (hr : 0 ≤ r) :
    extendedBody A r =
      {x | Metric.closedBall x r ⊆ offset A (2 * r)} := by
  apply Set.Subset.antisymm
  · exact extendedBody_subset_erosion A r
  · exact erosion_subset_extendedBody A r hclosed hr


theorem extendedBody_subset_offset_twice
    (A : Set Point2) (r : ℝ) (hr : 0 ≤ r) :
    extendedBody A r ⊆ offset A (2 * r) := by
  intro x hx
  have hball :
      Metric.closedBall x r ⊆ offset A (2 * r) :=
    extendedBody_subset_erosion A r hx
  apply hball
  change dist x x ≤ r
  simpa using hr


-- The closed r-neighborhood of any set is closed.
theorem isClosed_offset (A : Set Point2) (r : ℝ) :
    IsClosed (offset A r) := by
  by_cases hA : A.Nonempty
  · have h :
        IsClosed {x : Point2 | Metric.infDist x A ≤ r} :=
      isClosed_le (Metric.continuous_infDist_pt A) continuous_const
    simpa [offset, hA] using h
  · have h : offset A r = (∅ : Set Point2) := by
      ext x
      simp [offset, hA]
    rw [h]
    exact isClosed_empty

-- Therefore its closed neighborhood is measurable.
theorem measurableSet_offset (A : Set Point2) (r : ℝ) :
    MeasurableSet (offset A r) := by
  exact (isClosed_offset A r).measurableSet


-- The erosion of a closed set by a ball is closed.
theorem isClosed_erosion
    (S : Set Point2) (r : ℝ) (hS : IsClosed S) :
    IsClosed {x : Point2 | Metric.closedBall x r ⊆ S} := by
  have hEq :
      {x : Point2 | Metric.closedBall x r ⊆ S} =
        ⋂ v : Point2, {x : Point2 |
          dist (0 : Point2) v ≤ r → x + v ∈ S} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx v hv
      apply hx
      apply Metric.mem_closedBall.mpr
      have hdist :
          dist (x + v) x = dist (0 : Point2) v := by
        have h : x + v - x = v := by abel
        simp [dist_eq_norm, h]
      rw [hdist]
      exact hv
    · intro hx y hy
      have hdist :
          dist (0 : Point2) (y - x) = dist y x := by
        simpa [dist_eq_norm] using (norm_sub_rev x y)
      have hv : dist (0 : Point2) (y - x) ≤ r := by
        rw [hdist]
        exact Metric.mem_closedBall.mp hy
      have hxy : x + (y - x) = y := by abel
      simpa [hxy] using hx (y - x) hv
  rw [hEq]
  apply isClosed_iInter
  intro v

  by_cases hv : ‖v‖ ≤ r
  · have hf : Continuous (fun x : Point2 => x + v) :=
      continuous_id.add continuous_const
    have hh : IsClosed {x : Point2 | x + v ∈ S} :=
      hS.preimage hf
    simpa [hv, dist_eq_norm] using hh
  · simpa [hv, dist_eq_norm] using
      (isClosed_univ : IsClosed (Set.univ : Set Point2))


-- The extended body of a closed set is closed.
theorem isClosed_extendedBody
    (A : Set Point2) (r : ℝ)
    (hclosed : IsClosed A) (hr : 0 ≤ r) :
    IsClosed (extendedBody A r) := by
  rw [extendedBody_eq_erosion A r hclosed hr]
  exact isClosed_erosion
    (offset A (2 * r)) r (isClosed_offset A (2 * r))

-- Consequently, the extended body is measurable.
theorem measurableSet_extendedBody
    (A : Set Point2) (r : ℝ)
    (hclosed : IsClosed A) (hr : 0 ≤ r) :
    MeasurableSet (extendedBody A r) := by
  exact (isClosed_extendedBody A r hclosed hr).measurableSet


-- At radius zero, the offset of a closed set is the set itself.
theorem offset_zero_eq_of_isClosed
    (A : Set Point2) (hclosed : IsClosed A) :
    offset A 0 = A := by
  ext x
  change (A.Nonempty ∧ Metric.infDist x A ≤ 0) ↔ x ∈ A
  constructor
  · rintro ⟨hA, hdist⟩
    apply (hclosed.mem_iff_infDist_zero hA).2
    exact le_antisymm hdist Metric.infDist_nonneg
  · intro hx
    constructor
    · exact ⟨x, hx⟩
    · rw [Metric.infDist_zero_of_mem hx]

-- At radius zero, the extended body is the original closed set.
theorem extendedBody_zero_eq_of_isClosed
    (A : Set Point2) (hclosed : IsClosed A) :
    extendedBody A 0 = A := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx0 : x ∈ offset A (2 * 0) :=
      extendedBody_subset_offset_twice A 0 (by norm_num) hx
    simpa [offset_zero_eq_of_isClosed A hclosed] using hx0
  · intro x hx
    have hx0 : x ∈ offset A 0 := by
      simpa [offset_zero_eq_of_isClosed A hclosed] using hx
    exact offset_subset_extendedBody A 0 hx0

theorem offset_mono {A B : Set Point2} (hAB : A ⊆ B) (r : ℝ) :
    offset A r ⊆ offset B r := by
  intro x hx
  change A.Nonempty ∧ Metric.infDist x A ≤ r at hx
  exact ⟨hx.1.mono hAB, (Metric.infDist_le_infDist_of_subset hAB hx.1).trans hx.2⟩

theorem extendedBody_mono {A B : Set Point2} (hAB : A ⊆ B) (r : ℝ) :
    extendedBody A r ⊆ extendedBody B r := by
  intro x hx c hxc
  obtain ⟨y, hyBall, hyOffset⟩ := hx c hxc
  exact ⟨y, hyBall, offset_mono hAB r hyOffset⟩

/-- A point is lost precisely when its radius-`r` ball meets the lost
part of the radius-`2 * r` offset. -/
theorem mem_extendedBody_sdiff_iff {A B : Set Point2} (hB : IsClosed B)
    {r : ℝ} (hr : 0 ≤ r) {x : Point2} :
    x ∈ extendedBody A r \ extendedBody B r ↔
      x ∈ extendedBody A r ∧
        (Metric.closedBall x r ∩ (offset A (2 * r) \ offset B (2 * r))).Nonempty := by
  constructor
  · rintro ⟨hxA, hxB⟩
    rw [extendedBody_eq_erosion B r hB hr] at hxB
    change ¬ (Metric.closedBall x r ⊆ offset B (2 * r)) at hxB
    have hw : ∃ y, y ∈ Metric.closedBall x r ∧ y ∉ offset B (2 * r) := by
      by_contra! hn
      exact hxB (fun y hy => hn y hy)
    obtain ⟨y, hyBall, hyB⟩ := hw
    exact ⟨hxA, y, hyBall, extendedBody_subset_erosion A r hxA hyBall, hyB⟩
  · rintro ⟨hxA, y, hyBall, _, hyB⟩
    exact ⟨hxA, fun hxB => hyB (extendedBody_subset_erosion B r hxB hyBall)⟩

/-- Agreement with the ordinary offset for closed convex sets. -/
theorem extendedBody_eq_offset_of_convex {A : Set Point2}
    (hclosed : IsClosed A) (hconvex : Convex ℝ A) {r : ℝ} (hr : 0 ≤ r) :
    extendedBody A r = offset A r := by
  refine Subset.antisymm ?_ (offset_subset_extendedBody A r)
  intro x hx
  have hx₂ := extendedBody_subset_offset_twice A r hr hx
  change A.Nonempty ∧ Metric.infDist x A ≤ 2 * r at hx₂
  refine ⟨hx₂.1, ?_⟩
  by_contra! hfar
  obtain ⟨a, ha, hnear⟩ := hclosed.exists_infDist_eq_dist hx₂.1 x
  let d := ‖x - a‖
  have hd : d = Metric.infDist x A := by
    simpa [d, dist_eq_norm] using hnear.symm
  have hdpos : 0 < d := by linarith
  have hmin : ‖x - a‖ = ⨅ w : A, ‖x - w‖ := by
    simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hd
  have hsupport := (norm_eq_iInf_iff_real_inner_le_zero hconvex ha).mp hmin
  let c : Point2 := (r / d) • (x - a) + x
  have hc : c ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm, show c - x = (r / d) • (x - a) by simp [c],
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hdpos.le)]
    change r / d * d ≤ r
    rw [div_mul_cancel₀ _ hdpos.ne']
  have hc₂ := extendedBody_subset_erosion A r hx hc
  change A.Nonempty ∧ Metric.infDist c A ≤ 2 * r at hc₂
  have hca : c - a = (1 + r / d) • (x - a) := by
    rw [add_smul, one_smul]
    dsimp [c]
    abel
  have hcoef : 0 ≤ 1 + r / d := by positivity
  have hcd : ‖c - a‖ = d + r := by
    rw [hca, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
    change (1 + r / d) * d = d + r
    rw [add_mul, one_mul, div_mul_cancel₀ _ hdpos.ne']
  have hcmin := (norm_eq_iInf_iff_real_inner_le_zero hconvex (u := c) ha).mpr
    (fun w hw => by
      rw [hca, real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos hcoef (hsupport w hw))
  rw [← show ‖c - a‖ = Metric.infDist c A by
    simpa only [Metric.infDist_eq_iInf, dist_eq_norm] using hcmin, hcd] at hc₂
  linarith [hc₂.2]

theorem mem_offset_iff_exists_dist_le {A : Set Point2} (hA : IsClosed A)
    {r : ℝ} {x : Point2} :
    x ∈ offset A r ↔ ∃ a ∈ A, dist x a ≤ r := by
  constructor
  · intro hx
    change A.Nonempty ∧ Metric.infDist x A ≤ r at hx
    obtain ⟨a, ha, hnear⟩ := hA.exists_infDist_eq_dist hx.1 x
    exact ⟨a, ha, hnear ▸ hx.2⟩
  · rintro ⟨a, ha, hxa⟩
    exact ⟨⟨a, ha⟩, (Metric.infDist_le_dist_of_mem ha).trans hxa⟩
