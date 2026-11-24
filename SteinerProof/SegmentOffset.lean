import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Convex.Segment
import SteinerProof.ExtendedBody
import SteinerProof.PLComplex

/-! The ordinary planar offset of a segment. -/

open Set MeasureTheory WithLp NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

private def xy (x y : ℝ) : PLPoint := WithLp.toLp 2 ![x, y]

@[simp] private theorem xy_zero (x y : ℝ) : xy x y 0 = x := rfl
@[simp] private theorem xy_one (x y : ℝ) : xy x y 1 = y := rfl

private theorem dist_sq_xy (x y : PLPoint) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private theorem mem_axis_segment {p : PLPoint} {l : ℝ} (hl : 0 < l) :
    p ∈ segment ℝ 0 (xy l 0) ↔ 0 ≤ p 0 ∧ p 0 ≤ l ∧ p 1 = 0 := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ⟨ht, ht₁⟩, rfl⟩
    simp only [AffineMap.lineMap_apply_module', sub_zero, add_zero, PiLp.smul_apply, xy_zero, xy_one,
      smul_eq_mul, mul_zero]
    exact ⟨mul_nonneg ht hl.le, mul_le_of_le_one_left hl.le ht₁, trivial⟩
  · rintro ⟨hp₀, hp₁, hp₂⟩
    refine ⟨p 0 / l, ⟨div_nonneg hp₀ hl.le, (div_le_one hl).mpr hp₁⟩, ?_⟩
    ext i
    fin_cases i
    · rw [AffineMap.lineMap_apply_module', sub_zero, add_zero]
      change (p 0 / l) * l = p 0
      exact div_mul_cancel₀ (p 0) hl.ne'
    · rw [AffineMap.lineMap_apply_module', sub_zero, add_zero]
      change (p 0 / l) * 0 = p 1
      rw [mul_zero, hp₂]

private def axisRectangle (l r : ℝ) : Set PLPoint := {x | 0 ≤ x 0 ∧ x 0 ≤ l ∧ |x 1| ≤ r}
private def axisLeftCap (r : ℝ) : Set PLPoint := Metric.closedBall 0 r ∩ {x | x 0 < 0}
private def axisRightCap (l r : ℝ) : Set PLPoint := Metric.closedBall (xy l 0) r ∩ {x | l < x 0}

/-- The offset of a horizontal segment is its rectangular strip and two
semicircular caps. The straight cuts belong to the rectangle. -/
private theorem axis_offset_eq_rectangle_union_caps {l r : ℝ} (hl : 0 < l) (hr : 0 ≤ r) :
    offset (segment ℝ 0 (xy l 0)) r = axisRectangle l r ∪ (axisLeftCap r ∪ axisRightCap l r) := by
  have hClosed : IsClosed (segment ℝ 0 (xy l 0)) := by
    rw [← convexHull_pair]
    exact ((finite_singleton (xy l 0)).insert 0).isClosed_convexHull ℝ
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le hClosed).mp hx
    obtain ⟨hp₀, hp₁, hp₂⟩ := (mem_axis_segment hl).mp hp
    have hsq := pow_le_pow_left₀ dist_nonneg hxp 2
    rw [dist_sq_xy, hp₂, sub_zero] at hsq
    by_cases hx₀ : x 0 < 0
    · refine Or.inr (Or.inl ⟨?_, hx₀⟩)
      apply Metric.mem_closedBall.mpr
      apply (sq_le_sq₀ dist_nonneg hr).mp
      rw [dist_sq_xy, PiLp.zero_apply, PiLp.zero_apply, sub_zero, sub_zero]
      have hh := mul_nonneg hp₀ (show 0 ≤ p 0 - 2 * x 0 by linarith)
      nlinarith only [hsq, hh]
    by_cases hx₁ : l < x 0
    · refine Or.inr (Or.inr ⟨?_, hx₁⟩)
      apply Metric.mem_closedBall.mpr
      apply (sq_le_sq₀ dist_nonneg hr).mp
      rw [dist_sq_xy, xy_zero, xy_one, sub_zero]
      have hh := mul_nonneg (sub_nonneg.mpr hp₁) (show 0 ≤ 2 * x 0 - l - p 0 by linarith)
      nlinarith only [hsq, hh]
    apply Or.inl
    refine ⟨le_of_not_gt hx₀, le_of_not_gt hx₁, ?_⟩
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    linarith only [hsq, sq_nonneg (x 0 - p 0)]
  · intro hx
    apply (mem_offset_iff_exists_dist_le hClosed).mpr
    rcases hx with ⟨hx₀, hx₁, hx₂⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
    · let p := xy (x 0) 0
      refine ⟨p, (mem_axis_segment hl).mpr (by simpa [p] using And.intro hx₀ hx₁), ?_⟩
      apply (sq_le_sq₀ dist_nonneg hr).mp
      rw [dist_sq_xy]
      simp only [p, xy_zero, xy_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, sub_zero]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx₂ 2
    · exact ⟨0, left_mem_segment ℝ _ _, Metric.mem_closedBall.mp hb⟩
    · exact ⟨xy l 0, right_mem_segment ℝ _ _, Metric.mem_closedBall.mp hb⟩

private theorem volume_axisRectangle {l r : ℝ} (hl : 0 ≤ l) :
    volume (axisRectangle l r) = ENNReal.ofReal (2 * r * l) := by
  let a : Fin 2 → ℝ := ![0, -r]
  let b : Fin 2 → ℝ := ![l, r]
  have hRect : axisRectangle l r = (@ofLp 2 (Fin 2 → ℝ)) ⁻¹' Icc a b := by
    ext x
    simp only [axisRectangle, Set.mem_ofPred_eq, abs_le, Set.mem_preimage, Set.mem_Icc, Pi.le_def,
      Fin.forall_fin_two, a, b, Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  rw [hRect, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
      (measurableSet_Icc (a := a) (b := b)).nullMeasurableSet,
    Real.volume_Icc_pi, Fin.prod_univ_two]
  simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul hl]
  congr 1
  ring

private theorem volume_axis_cut_zero : volume {x : PLPoint | x 0 = 0} = 0 := by
  let f : Fin 2 → Set ℝ := ![{0}, Set.univ]
  have hEq : ({x : PLPoint | x 0 = 0} : Set PLPoint) = (@ofLp 2 (Fin 2 → ℝ)) ⁻¹' Set.pi Set.univ f := by
    ext x
    simp [f, Set.mem_pi, Fin.forall_fin_two]
  have hm : MeasurableSet (Set.pi Set.univ f) := by
    apply MeasurableSet.pi Set.countable_univ
    intro i _
    fin_cases i <;> simp [f]
  rw [hEq, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, Fin.prod_univ_two]
  simp [f]

private theorem measurableSet_axisLeftCap (r : ℝ) : MeasurableSet (axisLeftCap r) :=
  Metric.isClosed_closedBall.measurableSet.inter ((isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const).measurableSet)

private theorem measurableSet_axisRightCap (l r : ℝ) : MeasurableSet (axisRightCap l r) :=
  Metric.isClosed_closedBall.measurableSet.inter ((isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)).measurableSet)

private theorem volume_axis_caps (l r : ℝ) :
    volume (axisLeftCap r) + volume (axisRightCap l r) = volume (Metric.closedBall (0 : PLPoint) r) := by
  let P := axisRightCap 0 r
  have hZero : xy 0 0 = 0 := by ext i; fin_cases i <;> rfl
  have hp₀ : P = Metric.closedBall (0 : PLPoint) r ∩ {x | 0 < x 0} := by
    dsimp only [P, axisRightCap]
    rw [hZero]
  have hShift : axisRightCap l r = (fun x : PLPoint => x - xy l 0) ⁻¹' P := by
    rw [hp₀]
    ext x
    simp only [axisRightCap, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall,
      dist_eq_norm, sub_zero, PiLp.sub_apply, xy_zero, sub_pos]
  have hm : MeasurePreserving (fun x : PLPoint => x - xy l 0) := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure PLPoint) (-xy l 0)
  have hArea : volume (axisRightCap l r) = volume P := by
    rw [hShift, hm.measure_preimage (measurableSet_axisRightCap 0 r).nullMeasurableSet]
  have hDisjoint : Disjoint (axisLeftCap r) P := by
    rw [hp₀]
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ : x 0 < 0 := hx.2
    have h₂ : 0 < x 0 := hy.2
    linarith
  have hCover : axisLeftCap r ∪ P = Metric.closedBall (0 : PLPoint) r \ {x | x 0 = 0} := by
    rw [hp₀]
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.ne⟩
      · exact ⟨hx.1, hx.2.ne'⟩
    · rintro ⟨hx, hn⟩
      exact (lt_or_gt_of_ne hn).imp (fun h => ⟨hx, h⟩) (fun h => ⟨hx, h⟩)
  rw [hArea, ← measure_union hDisjoint (measurableSet_axisRightCap 0 r), hCover, measure_sdiff_null volume_axis_cut_zero]

private theorem volume_axis_offset {l r : ℝ} (hl : 0 < l) (hr : 0 ≤ r) :
    volume (offset (segment ℝ 0 (xy l 0)) r) = ENNReal.ofReal (2 * r * l) +
      volume (Metric.closedBall (0 : PLPoint) r) := by
  have hDisCap : Disjoint (axisLeftCap r) (axisRightCap l r) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have h₀ : x 0 < 0 := hx.2
    have h₁ : l < x 0 := hx'.2
    linarith
  have hDisRect : Disjoint (axisRectangle l r) (axisLeftCap r ∪ axisRightCap l r) := by
    apply Set.disjoint_left.mpr
    rintro x hx (h | h)
    · exact (not_lt_of_ge hx.1) h.2
    · exact (not_lt_of_ge hx.2.1) h.2
  rw [axis_offset_eq_rectangle_union_caps hl hr,
    measure_union hDisRect ((measurableSet_axisLeftCap r).union (measurableSet_axisRightCap l r)),
    measure_union hDisCap (measurableSet_axisRightCap l r), volume_axis_caps, volume_axisRectangle hl.le]

private theorem exists_axis_isometry {d : PLPoint} (hd : d ≠ 0) :
    ∃ F : PLPoint ≃ₗᵢ[ℝ] PLPoint, F d = xy ‖d‖ 0 := by
  let e := normalize d
  let n := xy (-(e 1)) (e 0)
  have he : ‖e‖ = 1 := norm_normalize hd
  have hn : ‖n‖ = 1 := by
    have h : ‖n‖ ^ 2 = ‖e‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [n, xy_zero, xy_one, neg_sq]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (he ▸ h)
  have hen : ⟪e, n⟫ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    change -(e 1) * e 0 + e 0 * e 1 = 0
    ring
  have hne : ⟪n, e⟫ = 0 := (real_inner_comm _ _).trans hen
  have hon : Orthonormal ℝ (![e, n] : Fin 2 → PLPoint) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, hn, hen, hne]
  let B := basisOfOrthonormalOfCardEqFinrank hon (by simp)
  have hB : (B : Fin 2 → PLPoint) = ![e, n] := coe_basisOfOrthonormalOfCardEqFinrank _ _
  let O := B.toOrthonormalBasis (hB.symm ▸ hon)
  have hO : (O : Fin 2 → PLPoint) = ![e, n] := (B.coe_toOrthonormalBasis _).trans hB
  have heO : O 0 = e := congrFun hO 0
  have hnO : O 1 = n := congrFun hO 1
  have hScale : d = ‖d‖ • e := (norm_smul_normalize _).symm
  have h₀ : ⟪e, d⟫ = ‖d‖ := by
    calc
      _ = ⟪e, ‖d‖ • e⟫ := congrArg (fun t : PLPoint => ⟪e, t⟫) hScale
      _ = _ := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  have h₁ : ⟪n, d⟫ = 0 := by
    calc
      _ = ⟪n, ‖d‖ • e⟫ := congrArg (fun t : PLPoint => ⟪n, t⟫) hScale
      _ = _ := by rw [real_inner_smul_right, hne, mul_zero]
  refine ⟨O.repr, ?_⟩
  ext i
  fin_cases i
  · change O.repr d 0 = ‖d‖
    rw [O.repr_apply_apply, heO, h₀]
  · change O.repr d 1 = 0
    rw [O.repr_apply_apply, hnO, h₁]

/-- A closed segment offset has the area of the rectangle of width `2r`
and a disk of radius `r`. This is the ordinary Steiner formula for a segment. -/
theorem volume_offset_segment_toReal {v u : PLPoint} (hvu : v ≠ u) {r : ℝ} (hr : 0 ≤ r) :
    (volume (offset (segment ℝ v u) r)).toReal = 2 * r * dist v u + Real.pi * r ^ 2 := by
  have hd : u - v ≠ 0 := sub_ne_zero.mpr hvu.symm
  let l := ‖u - v‖
  have hl : 0 < l := norm_pos_iff.mpr hd
  obtain ⟨F, hF⟩ := exists_axis_isometry hd
  let G : PLPoint →ᵃ[ℝ] PLPoint := F.toLinearMap.toAffineMap.comp
    ((AffineMap.id ℝ PLPoint) - AffineMap.const ℝ PLPoint v)
  have hG (x : PLPoint) : G x = F (x - v) := rfl
  have hGv : G v = 0 := by rw [hG, sub_self, map_zero]
  have hGu : G u = xy l 0 := hF
  have hImg : G '' segment ℝ v u = segment ℝ 0 (xy l 0) := by
    rw [image_segment, hGv, hGu]
  have hDist (x y : PLPoint) : dist (G x) (G y) = dist x y := by
    rw [hG, hG, F.dist_map]
    simp only [dist_eq_norm, sub_sub_sub_cancel_right]
  have hCarry : offset (segment ℝ v u) r = G ⁻¹' offset (segment ℝ 0 (xy l 0)) r := by
    have hClosed (a b : PLPoint) : IsClosed (segment ℝ a b) := by
      rw [← convexHull_pair]
      exact ((finite_singleton b).insert a).isClosed_convexHull ℝ
    ext x
    change x ∈ offset (segment ℝ v u) r ↔ G x ∈ offset (segment ℝ 0 (xy l 0)) r
    rw [mem_offset_iff_exists_dist_le (hClosed v u), mem_offset_iff_exists_dist_le (hClosed 0 _), ← hImg]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨G y, ⟨y, hy, rfl⟩, by rwa [hDist]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      exact ⟨y, hy, by rwa [hDist] at hxy⟩
  have hMP : MeasurePreserving G := by
    have hT : MeasurePreserving (fun x : PLPoint => x - v) := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure PLPoint) (-v)
    exact F.measurePreserving.comp hT
  rw [hCarry, hMP.measure_preimage (measurableSet_offset (segment ℝ 0 (xy l 0)) r).nullMeasurableSet,
    volume_axis_offset hl hr,
    ENNReal.toReal_add ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne,
    EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r * l)]
  rw [dist_comm v u, dist_eq_norm]
  change 2 * r * l + r ^ 2 * Real.pi = 2 * r * l + Real.pi * r ^ 2
  ring

end SteinerProof
