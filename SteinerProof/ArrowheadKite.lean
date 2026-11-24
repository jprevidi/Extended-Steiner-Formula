import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import SteinerProof.ArrowheadGeometry

/-! The near and far right kites and their central reflection in Section 3. -/

open Set InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

/-- The inward normal component of the bisector displacement, based at the common vertex. -/
def nearKiteShoulder (v u w : PLPoint) (r : ℝ) : PLPoint :=
  let X := normalize (u - v)
  let D := arrowheadBisectorPoint v u w r 1 - v
  v + (D - ⟪D, X⟫ • X)

theorem nearKiteShoulder_sub_vertex_eq {v u w : PLPoint} {r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) :
    nearKiteShoulder v u w r - v =
      (r / Real.sin (angle (u - v) (w - v))) •
        (normalize (w - v) - Real.cos (angle (u - v) (w - v)) • normalize (u - v)) := by
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let θ := angle (u - v) (w - v)
  let d := r / Real.sin θ
  let c := Real.cos θ
  let D := arrowheadBisectorPoint v u w r 1 - v
  have hD : D = d • (X + Y) := by simp [D, arrowheadBisectorPoint, d, θ, X, Y]
  have hX : ‖X‖ = 1 := norm_normalize (sub_ne_zero.mpr hu)
  have hYX : ⟪Y, X⟫ = c := (real_inner_comm _ _).trans
    (inner_normalize_eq_cos_angle (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw))
  have hDX : ⟪D, X⟫ = d * (1 + c) := by
    rw [hD, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hX, hYX, one_pow]
  change v + (D - ⟪D, X⟫ • X) - v = d • (Y - c • X)
  rw [add_sub_cancel_left, hDX, hD, smul_add, smul_sub, mul_add, mul_one, add_smul, mul_smul]
  abel

/-- Dot products of the two unit edge directions with the inward normal
displacement of the first shoulder. -/
theorem inner_nearKiteShoulder_directions {v u w : PLPoint} {r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi) :
    let N := nearKiteShoulder v u w r - v
    ⟪normalize (u - v), N⟫ = 0 ∧
      ⟪normalize (w - v), N⟫ = r * Real.sin (angle (u - v) (w - v)) := by
  dsimp only
  rw [nearKiteShoulder_sub_vertex_eq hu hw]
  let θ := angle (u - v) (w - v)
  let X := normalize (u - v)
  let Y := normalize (w - v)
  have hX : ‖X‖ = 1 := norm_normalize (sub_ne_zero.mpr hu)
  have hY : ‖Y‖ = 1 := norm_normalize (sub_ne_zero.mpr hw)
  have hXY : ⟪X, Y⟫ = Real.cos θ :=
    inner_normalize_eq_cos_angle (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw)
  have hYX : ⟪Y, X⟫ = Real.cos θ := (real_inner_comm _ _).trans hXY
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  change ⟪X, (r / Real.sin θ) • (Y - Real.cos θ • X)⟫ = 0 ∧
    ⟪Y, (r / Real.sin θ) • (Y - Real.cos θ • X)⟫ = r * Real.sin θ
  constructor
  · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, hXY,
      real_inner_self_eq_norm_sq, hX]
    ring
  · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hY, hYX]
    have heq : 1 ^ 2 - Real.cos θ * Real.cos θ = Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [heq, pow_two, ← mul_assoc, div_mul_cancel₀ _ hsin.ne']

/-- The shoulder has a leg of length `r) from `p₀` and a right angle
between the legs to `p₀` and `p₁`. -/
theorem nearKiteShoulder_right_angle {v u w : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi) :
    let S := nearKiteShoulder v u w r
    let Q := arrowheadBisectorPoint v u w r 1
    dist S v = r ∧ ⟪v - S, Q - S⟫ = 0 := by
  dsimp only
  let S := nearKiteShoulder v u w r
  let Q := arrowheadBisectorPoint v u w r 1
  let θ := angle (u - v) (w - v)
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let D := Q - v
  let N := D - ⟪D, X⟫ • X
  let d := r / Real.sin θ
  let c := Real.cos θ
  have hu' := sub_ne_zero.mpr hu
  have hw' := sub_ne_zero.mpr hw
  have hX : ‖X‖ = 1 := norm_normalize hu'
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hN : N = d • (Y - c • X) := by
    simpa only [show N = S - v from (add_sub_cancel_left v N).symm] using
      (nearKiteShoulder_sub_vertex_eq (r := r) hu hw)
  change dist S v = r ∧ ⟪v - S, Q - S⟫ = 0
  have hSv : S - v = N := add_sub_cancel_left v N
  constructor
  · rw [dist_eq_norm, hSv, hN, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr hsin.le)]
    have hn : ‖Y - c • X‖ = Real.sin θ := norm_normalize_sub_cos_smul hu' hw'
    rw [hn]
    exact div_mul_cancel₀ _ hsin.ne'
  · have hNX : ⟪N, X⟫ = 0 := by
      change ⟪D - ⟪D, X⟫ • X, X⟫ = 0
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hX]
      ring
    have hVS : v - S = -N := by rw [← hSv, neg_sub]
    have hQS : Q - S = ⟪D, X⟫ • X := by
      change Q - (v + (Q - v - ⟪D, X⟫ • X)) = _
      abel
    rw [hVS, hQS, real_inner_smul_right, inner_neg_left, hNX, neg_zero, mul_zero]

/-- The closed kite with distinguished vertex `p₀ = v` and opposite vertex `p₁`. -/
def nearKite (v u w : PLPoint) (r : ℝ) : Set PLPoint :=
  convexHull ℝ {v, arrowheadBisectorPoint v u w r 1,
    nearKiteShoulder v u w r, nearKiteShoulder v w u r}

/-- The closed kite with distinguished vertex `p₂`, obtained by reflection about `p₁`. -/
def farKite (v u w : PLPoint) (r : ℝ) : Set PLPoint :=
  AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1) ''
    nearKite v u w r

/-- Remove the open disk at the distinguished vertex from the interior of the kite. -/
def nearArrowhead (v u w : PLPoint) (r : ℝ) : Set PLPoint :=
  if angle (u - v) (w - v) < Real.pi then interior (nearKite v u w r) \ Metric.ball v r
  else ∅

def farArrowhead (v u w : PLPoint) (r : ℝ) : Set PLPoint :=
  if angle (u - v) (w - v) < Real.pi then
    interior (farKite v u w r) \ Metric.ball (arrowheadBisectorPoint v u w r 2) r
  else ∅

theorem pointReflection_bisectorPoint (v u w : PLPoint) (r : ℝ) :
    AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1) v =
      arrowheadBisectorPoint v u w r 2 := by
  rw [AffineIsometryEquiv.pointReflection_apply]
  change arrowheadBisectorPoint v u w r 1 - v + arrowheadBisectorPoint v u w r 1 = _
  unfold arrowheadBisectorPoint
  simp only [one_mul, add_sub_cancel_left]
  rw [show 2 * r / Real.sin (angle (u - v) (w - v)) =
      r / Real.sin (angle (u - v) (w - v)) + r / Real.sin (angle (u - v) (w - v)) by ring,
    add_smul]
  abel

/-- The far shoulder corresponding to the first incident edge. -/
def farKiteShoulder (v u w : PLPoint) (r : ℝ) : PLPoint :=
  AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1)
    (nearKiteShoulder v u w r)

/-- The reflected kite has the four vertices used in the paper. -/
theorem farKite_eq_convexHull (v u w : PLPoint) (r : ℝ) :
    farKite v u w r = convexHull ℝ {arrowheadBisectorPoint v u w r 2,
      arrowheadBisectorPoint v u w r 1, farKiteShoulder v u w r, farKiteShoulder v w u r} := by
  let e := AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1)
  unfold farKite nearKite
  change e.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
  rw [AffineMap.image_convexHull]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change convexHull ℝ {e v, e (arrowheadBisectorPoint v u w r 1),
    farKiteShoulder v u w r, e (nearKiteShoulder v w u r)} = _
  dsimp [e]
  rw [pointReflection_bisectorPoint, AffineIsometryEquiv.pointReflection_self]
  unfold farKiteShoulder
  rw [arrowheadBisectorPoint_comm v w u r 1]

/-- The squared distance of the far shoulder from the common vertex. -/
theorem dist_farKiteShoulder_sq {v u w : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi) :
    dist (farKiteShoulder v u w r) v ^ 2 =
      dist (arrowheadBisectorPoint v u w r 2) v ^ 2 - 3 * r ^ 2 := by
  let S := nearKiteShoulder v u w r
  let Q := arrowheadBisectorPoint v u w r 1
  let P := arrowheadBisectorPoint v u w r 2
  let D := Q - v
  let N := S - v
  obtain ⟨hleg, horth⟩ := nearKiteShoulder_right_angle hr hu hw hθ hπ
  have hN : ‖N‖ = r := by simpa only [dist_eq_norm] using hleg
  have hNC : ⟪N, D⟫ = r ^ 2 := by
    have h : ⟪-N, D - N⟫ = 0 := by
      rw [neg_sub, show D - N = Q - S by dsimp [D, N]; abel]
      exact horth
    rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, hN] at h
    linarith
  have hDN : ⟪D, N⟫ = r ^ 2 := (real_inner_comm _ _).trans hNC
  have hS : farKiteShoulder v u w r - v = (2 : ℝ) • D - N := by
    rw [farKiteShoulder, AffineIsometryEquiv.pointReflection_apply, two_smul]
    change Q - S + Q - v = _
    dsimp [D, N]
    abel
  have hP : dist P v = 2 * ‖D‖ := by
    rw [show P = _ from (pointReflection_bisectorPoint v u w r).symm,
      AffineIsometryEquiv.dist_pointReflection_self_real, dist_eq_norm]
  change dist (farKiteShoulder v u w r) v ^ 2 = dist P v ^ 2 - 3 * r ^ 2
  rw [hP, dist_eq_norm, hS, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    real_inner_smul_left, hDN, hN]
  ring

/-- Every point of the far kite is within the distance of its distinguished vertex. -/
theorem farKite_subset_closedBall {v u w : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi) :
    farKite v u w r ⊆ Metric.closedBall v (dist (arrowheadBisectorPoint v u w r 2) v) := by
  rw [farKite_eq_convexHull]
  apply convexHull_min _ (convex_closedBall _ _)
  have h₁ := dist_farKiteShoulder_sq hr hu hw hθ hπ
  have h₂ := dist_farKiteShoulder_sq hr hw hu
    (by rwa [angle_comm]) (by rwa [angle_comm])
  rw [arrowheadBisectorPoint_comm v w u r 2] at h₂
  have hdist : dist (arrowheadBisectorPoint v u w r 2) v =
      2 * dist (arrowheadBisectorPoint v u w r 1) v := by
    rw [← pointReflection_bisectorPoint, AffineIsometryEquiv.dist_pointReflection_self_real]
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rw [Metric.mem_closedBall]
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_rfl
  · rw [hdist]
    linarith [dist_nonneg (x := arrowheadBisectorPoint v u w r 1) (y := v)]
  · exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp (by nlinarith [sq_nonneg r])
  · exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp (by nlinarith [sq_nonneg r])

/-- With the paper's radius, the far kite stays within half the separation scale. -/
theorem farKite_subset_separation_ball {K : FinitePlanarComplex} {v u w : PLPoint} {r : ℝ}
    (hu : ({v, u} : Finset PLPoint) ∈ K.edges) (hw : ({v, w} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (hπ : angle (u - v) (w - v) < Real.pi)
    (hr : 0 < r) (hrK : r < K.admissibleRadius) :
    farKite v u w r ⊆ Metric.ball v (K.vertexFaceSeparation / 2) := by
  have hθ := K.incident_angle_pos hu hw huw
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  intro x hx
  have h := Metric.mem_closedBall.mp (farKite_subset_closedBall hr.le huv hwv hθ hπ hx)
  have hM := K.four_mul_csc_lt_separation hu hw huw hθ hr hrK
  rw [dist_arrowheadBisectorPoint v u w hr.le (by norm_num) huv hwv hθ hπ] at h
  exact Metric.mem_ball.mpr (by linarith)

/-- The near shoulder's normal displacement pairs with the bisector
displacement to give the squared radius. -/
private theorem inner_bisector_nearShoulder {v u w : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi) :
    ⟪arrowheadBisectorPoint v u w r 1 - v, nearKiteShoulder v u w r - v⟫ = r ^ 2 := by
  let S := nearKiteShoulder v u w r
  let Q := arrowheadBisectorPoint v u w r 1
  let N := S - v
  obtain ⟨hleg, horth⟩ := nearKiteShoulder_right_angle hr hu hw hθ hπ
  have hN : ‖N‖ = r := by simpa only [dist_eq_norm] using hleg
  have h : ⟪-N, (Q - v) - N⟫ = 0 := by
    rw [show -N = v - S by simp [N], show (Q - v) - N = Q - S by dsimp [N]; abel]
    exact horth
  rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, hN, neg_eq_zero,
    sub_eq_zero] at h
  rw [real_inner_comm]
  exact h

private theorem le_inner_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ farKite v u w r) :
    r ^ 2 ≤ ⟪x - v, nearKiteShoulder v u w r - v⟫ := by
  let N := nearKiteShoulder v u w r - v
  let Q := arrowheadBisectorPoint v u w r 1
  have hN : ‖N‖ = r := by
    simpa only [dist_eq_norm] using (nearKiteShoulder_right_angle hr hu hw hθ hπ).1
  have hQ := inner_bisector_nearShoulder hr hu hw hθ hπ
  let f : PLPoint →ᵃ[ℝ] ℝ :=
    (innerSL ℝ N).toLinearMap.toAffineMap.comp
      ((AffineMap.id ℝ PLPoint) - AffineMap.const ℝ PLPoint v)
  have hF (y : PLPoint) : f y = ⟪y - v, N⟫ := by
    change ⟪N, y - v⟫ = ⟪y - v, N⟫
    exact real_inner_comm _ _
  have hnear : nearKite v u w r ⊆ f ⁻¹' Iic (r ^ 2) := by
    unfold nearKite
    apply convexHull_min _ ((convex_Iic _).affine_preimage _)
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rw [mem_preimage, mem_Iic, hF]
    rcases hy with rfl | rfl | rfl | rfl
    · simp [sq_nonneg r]
    · exact hQ.le
    · change ⟪N, N⟫ ≤ r ^ 2
      rw [real_inner_self_eq_norm_sq, hN]
    · have hN' : ‖nearKiteShoulder v w u r - v‖ = r := by
        simpa only [dist_eq_norm] using
          (nearKiteShoulder_right_angle hr hw hu
            (by rwa [angle_comm]) (by rwa [angle_comm])).1
      have h := real_inner_le_norm (nearKiteShoulder v w u r - v) N
      rwa [hN', hN, ← pow_two] at h
  obtain ⟨y, hy, rfl⟩ := hx
  have hle : f y ≤ r ^ 2 := hnear hy
  rw [hF] at hle
  rw [AffineIsometryEquiv.pointReflection_apply]
  change r ^ 2 ≤ ⟪Q - y + Q - v, N⟫
  rw [show Q - y + Q - v = (2 : ℝ) • (Q - v) - (y - v) by rw [two_smul]; abel,
    inner_sub_left, real_inner_smul_left, hQ]
  linarith

private theorem lt_inner_of_mem_interior_of_bound {C : Set PLPoint} {v x N : PLPoint}
    {a : ℝ} (hN : 0 < ‖N‖) (hbound : ∀ y ∈ C, a ≤ ⟪y - v, N⟫)
    (hx : x ∈ interior C) : a < ⟪x - v, N⟫ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let t := ε / (2 * ‖N‖)
  have ht : 0 < t := by dsimp [t]; positivity
  have hy : x - t • N ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, show x - t • N - x = -(t • N) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have htr : t * ‖N‖ = ε / 2 := by dsimp [t]; field_simp [hN.ne']
    linarith
  have hlo := hbound _ (interior_subset (hball hy))
  rw [show x - t • N - v = (x - v) - t • N by abel, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hlo
  linarith [mul_pos ht (pow_pos hN 2)]

/-- The far kite interior lies strictly beyond the radius-`r` supporting
line parallel to the first edge. This is the first transverse kite inequality. -/
theorem lt_inner_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    r ^ 2 < ⟪x - v, nearKiteShoulder v u w r - v⟫ := by
  let N := nearKiteShoulder v u w r - v
  have hN : ‖N‖ = r := by
    simpa only [dist_eq_norm] using (nearKiteShoulder_right_angle hr.le hu hw hθ hπ).1
  exact lt_inner_of_mem_interior_of_bound (hN.symm ▸ hr)
    (fun _ hy => le_inner_farKite hr.le hu hw hθ hπ hy) hx

theorem nearKite_comm (v u w : PLPoint) (r : ℝ) : nearKite v u w r = nearKite v w u r := by
  have hvertices :
      ({v, arrowheadBisectorPoint v u w r 1, nearKiteShoulder v u w r,
        nearKiteShoulder v w u r} : Set PLPoint) =
      {v, arrowheadBisectorPoint v u w r 1, nearKiteShoulder v w u r,
        nearKiteShoulder v u w r} := by
    exact congrArg (fun tail : Set PLPoint =>
      insert v (insert (arrowheadBisectorPoint v u w r 1) tail))
      (Set.pair_comm (nearKiteShoulder v u w r) (nearKiteShoulder v w u r))
  unfold nearKite
  rw [arrowheadBisectorPoint_comm v w u r 1, hvertices]

theorem farKite_comm (v u w : PLPoint) (r : ℝ) : farKite v u w r = farKite v w u r := by
  unfold farKite
  rw [arrowheadBisectorPoint_comm v u w r 1, nearKite_comm v u w r]

/-- The scalar projection along a defining edge is nonnegative throughout the near kite. -/
theorem inner_nonneg_of_mem_nearKite {v u w x : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ nearKite v u w r) : 0 ≤ ⟪x - v, normalize (u - v)⟫ := by
  let X := normalize (u - v)
  let Y := normalize (w - v)
  let Q := arrowheadBisectorPoint v u w r 1
  let D := Q - v
  let θ := angle (u - v) (w - v)
  let c := Real.cos θ
  let d := r / Real.sin θ
  have hX : ‖X‖ = 1 := norm_normalize (sub_ne_zero.mpr hu)
  have hY : ‖Y‖ = 1 := norm_normalize (sub_ne_zero.mpr hw)
  have hXY : ⟪X, Y⟫ = c := inner_normalize_eq_cos_angle (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw)
  have hYX : ⟪Y, X⟫ = c := (real_inner_comm _ _).trans hXY
  have hD : D = d • (X + Y) := by simp [D, Q, arrowheadBisectorPoint, d, θ, X, Y]
  have hDX : ⟪D, X⟫ = d * (1 + c) := by
    rw [hD, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hX, hYX, one_pow]
  have hDY : ⟪D, Y⟫ = d * (1 + c) := by
    rw [hD, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hY, hXY, one_pow]
    rw [add_comm c 1]
  have hnonneg : 0 ≤ ⟪D, X⟫ := by
    rw [hDX]
    exact mul_nonneg (div_nonneg hr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).le)
      (by linarith [Real.neg_one_le_cos θ])
  let f : PLPoint →ᵃ[ℝ] ℝ :=
    (innerSL ℝ X).toLinearMap.toAffineMap.comp
      ((AffineMap.id ℝ PLPoint) - AffineMap.const ℝ PLPoint v)
  have hF (y : PLPoint) : f y = ⟪y - v, X⟫ := by
    change ⟪X, y - v⟫ = ⟪y - v, X⟫
    exact real_inner_comm _ _
  have hnear : nearKite v u w r ⊆ f ⁻¹' Ici 0 := by
    unfold nearKite
    apply convexHull_min _ ((convex_Ici _).affine_preimage _)
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rw [mem_preimage, mem_Ici, hF]
    rcases hy with rfl | rfl | rfl | rfl
    · simp
    · exact hnonneg
    · have heq : nearKiteShoulder v u w r - v = D - ⟪D, X⟫ • X := by
        simp [nearKiteShoulder, D, Q, X]
      rw [heq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hX]
      simp
    · have heq : nearKiteShoulder v w u r - v = D - ⟪D, Y⟫ • Y := by
        simp [nearKiteShoulder, D, Q, Y, arrowheadBisectorPoint_comm v w u r 1]
      rw [heq, inner_sub_left, real_inner_smul_left, hYX, hDY, ← hDX, ← mul_one_sub]
      exact mul_nonneg hnonneg (by dsimp [c]; linarith [Real.cos_le_one θ])
  rw [← hF]
  exact hnear hx

private theorem inner_le_farKite_projection {v u w x : PLPoint} {r : ℝ} (hr : 0 ≤ r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ farKite v u w r) :
    ⟪x - v, normalize (u - v)⟫ ≤
      2 * ⟪arrowheadBisectorPoint v u w r 1 - v, normalize (u - v)⟫ := by
  let X := normalize (u - v)
  let Q := arrowheadBisectorPoint v u w r 1
  let D := Q - v
  obtain ⟨y, hy, rfl⟩ := hx
  have hle := inner_nonneg_of_mem_nearKite hr hu hw hθ hπ hy
  rw [AffineIsometryEquiv.pointReflection_apply]
  change ⟪Q - y + Q - v, X⟫ ≤ 2 * ⟪D, X⟫
  rw [show Q - y + Q - v = (2 : ℝ) • D - (y - v) by rw [two_smul]; dsimp [D]; abel,
    inner_sub_left, real_inner_smul_left]
  linarith

/-- The strict longitudinal bound for the first edge of the far kite. -/
theorem inner_lt_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    ⟪x - v, normalize (u - v)⟫ <
      2 * ⟪arrowheadBisectorPoint v u w r 1 - v, normalize (u - v)⟫ := by
  let X := normalize (u - v)
  have hX : 0 < ‖-X‖ := by rw [norm_neg, norm_normalize (sub_ne_zero.mpr hu)]; norm_num
  have hlo := lt_inner_of_mem_interior_of_bound hX
    (a := -(2 * ⟪arrowheadBisectorPoint v u w r 1 - v, X⟫))
    (v := v) (fun _ hy => by
      rw [inner_neg_right]
      exact neg_le_neg (inner_le_farKite_projection hr.le hu hw hθ hπ hy)) hx
  rw [inner_neg_right] at hlo
  exact neg_lt_neg_iff.mp hlo

/-- The strict longitudinal bound for the second edge of the far kite. -/
theorem inner_other_lt_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    ⟪x - v, normalize (w - v)⟫ <
      2 * ⟪arrowheadBisectorPoint v u w r 1 - v, normalize (w - v)⟫ := by
  rw [farKite_comm] at hx
  rw [arrowheadBisectorPoint_comm v u w]
  exact inner_lt_of_mem_interior_farKite hr hw hu
    (by rwa [angle_comm]) (by rwa [angle_comm]) hx

private theorem bisectorPoint_two_sub_vertex (v u w : PLPoint) (r : ℝ) :
    arrowheadBisectorPoint v u w r 2 - v =
      (2 : ℝ) • (arrowheadBisectorPoint v u w r 1 - v) := by
  rw [← pointReflection_bisectorPoint, AffineIsometryEquiv.pointReflection_apply, two_smul]
  change arrowheadBisectorPoint v u w r 1 - v + arrowheadBisectorPoint v u w r 1 - v = _
  abel

/-- A radius-`r` ball containing a far-kite interior point has its center
on the inward side of the supporting line of the first edge. -/
theorem inner_pos_of_dist_le_of_mem_interior_farKite {v u w x c : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) (hc : dist c x ≤ r) :
    0 < ⟪c - v, nearKiteShoulder v u w r - v⟫ := by
  let N := nearKiteShoulder v u w r - v
  have hN : ‖N‖ = r := by
    simpa only [dist_eq_norm] using (nearKiteShoulder_right_angle hr.le hu hw hθ hπ).1
  have hstrict := lt_inner_of_mem_interior_farKite hr hu hw hθ hπ hx
  change r ^ 2 < ⟪x - v, N⟫ at hstrict
  have hdist : ‖x - c‖ ≤ r := by simpa only [dist_eq_norm, norm_sub_rev] using hc
  have hin := (real_inner_le_norm (x - c) N).trans
    (mul_le_mul_of_nonneg_right hdist (norm_nonneg N))
  rw [hN, show x - c = (x - v) - (c - v) by abel, inner_sub_left] at hin
  linarith

/-- A center strictly beyond the tip in the positive edge sector cannot
cover a far-arrowhead point with a radius-`r` ball. -/
theorem lt_dist_of_mem_farArrowhead_of_beyond_tip {v u w x c : PLPoint} {r a b : ℝ}
    (hr : 0 < r) (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ farArrowhead v u w r) (ha : 0 < a) (hb : 0 < b)
    (hc : c - arrowheadBisectorPoint v u w r 2 =
      a • normalize (u - v) + b • normalize (w - v)) :
    r < dist c x := by
  let P := arrowheadBisectorPoint v u w r 2
  let Q := arrowheadBisectorPoint v u w r 1
  let X := normalize (u - v)
  let Y := normalize (w - v)
  rw [farArrowhead, ite_eq_left hπ] at hx
  have hPX : ⟪x - P, X⟫ < 0 := by
    rw [show x - P = (x - v) - (P - v) by abel, inner_sub_left,
      bisectorPoint_two_sub_vertex, real_inner_smul_left]
    exact sub_neg.mpr (inner_lt_of_mem_interior_farKite hr hu hw hθ hπ hx.1)
  have hPY : ⟪x - P, Y⟫ < 0 := by
    rw [show x - P = (x - v) - (P - v) by abel, inner_sub_left,
      bisectorPoint_two_sub_vertex, real_inner_smul_left]
    exact sub_neg.mpr (inner_other_lt_of_mem_interior_farKite hr hu hw hθ hπ hx.1)
  have hinner : ⟪c - P, x - P⟫ < 0 := by
    change c - P = a • X + b • Y at hc
    rw [hc, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (x - P) X, real_inner_comm (x - P) Y]
    exact add_neg (mul_neg_of_pos_of_neg ha hPX) (mul_neg_of_pos_of_neg hb hPY)
  have hball : r ≤ ‖x - P‖ := by
    have h := hx.2
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at h
    exact h
  apply (sq_lt_sq₀ hr.le dist_nonneg).mp
  rw [dist_eq_norm, show c - x = (c - P) - (x - P) by abel, norm_sub_sq_real]
  nlinarith [sq_nonneg ‖c - P‖, (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hball]

/-- Every point in the far kite interior is at distance strictly greater
than `r` from its first defining edge. -/
theorem lt_infDist_edge_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    r < Metric.infDist x (segment ℝ v u) := by
  let X := normalize (u - v)
  let D := arrowheadBisectorPoint v u w r 1 - v
  let N := nearKiteShoulder v u w r - v
  have hX : ‖X‖ = 1 := norm_normalize (sub_ne_zero.mpr hu)
  have hN : ‖N‖ = r := by
    simpa only [dist_eq_norm] using (nearKiteShoulder_right_angle hr.le hu hw hθ hπ).1
  have hNX : ⟪N, X⟫ = 0 := by
    have h : N = D - ⟪D, X⟫ • X := by simp [N, nearKiteShoulder, D, X]
    rw [h, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hX]
    ring
  have hdir : u - v = ‖u - v‖ • X := by
    dsimp [X, NormedSpace.normalize]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu)), one_smul]
  have hcompact : IsCompact (segment ℝ v u) := by
    rw [← convexHull_pair]
    exact ((finite_singleton u).insert v).isCompact_convexHull ℝ
  obtain ⟨z, hz, heq⟩ := hcompact.exists_infDist_eq_dist ⟨v, left_mem_segment ℝ v u⟩ x
  have hzero : ⟪z - v, N⟫ = 0 := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, _, rfl⟩ := hz
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, hdir,
      real_inner_smul_left, real_inner_smul_left,
      show ⟪X, N⟫ = 0 from (real_inner_comm _ _).trans hNX, mul_zero, mul_zero]
  have hstrict := lt_inner_of_mem_interior_farKite hr hu hw hθ hπ hx
  change r ^ 2 < ⟪x - v, N⟫ at hstrict
  have hle := real_inner_le_norm (x - z) N
  rw [show x - z = (x - v) - (z - v) by abel, inner_sub_left, hzero, sub_zero, hN] at hle
  rw [show (x - v) - (z - v) = x - z by abel] at hle
  rw [heq, dist_eq_norm]
  exact (mul_lt_mul_iff_left₀ hr).mp (by rw [← pow_two]; exact hstrict.trans_le hle)

/-- The corresponding separation from the second defining edge. -/
theorem lt_infDist_other_edge_of_mem_interior_farKite {v u w x : PLPoint} {r : ℝ} (hr : 0 < r)
    (hu : u ≠ v) (hw : w ≠ v)
    (hθ : 0 < angle (u - v) (w - v)) (hπ : angle (u - v) (w - v) < Real.pi)
    (hx : x ∈ interior (farKite v u w r)) :
    r < Metric.infDist x (segment ℝ v w) := by
  rw [farKite_comm] at hx
  exact lt_infDist_edge_of_mem_interior_farKite hr hw hu
    (by rwa [angle_comm]) (by rwa [angle_comm]) hx

/-- Central reflection at `p₁` carries the entire near arrowhead to the far arrowhead. -/
theorem image_nearArrowhead_eq_farArrowhead (v u w : PLPoint) (r : ℝ) :
    AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1) ''
      nearArrowhead v u w r = farArrowhead v u w r := by
  by_cases h : angle (u - v) (w - v) < Real.pi
  · let e := AffineIsometryEquiv.pointReflection ℝ (arrowheadBisectorPoint v u w r 1)
    rw [nearArrowhead, farArrowhead, ite_eq_left h, ite_eq_left h, Set.image_sdiff e.injective]
    have hi := e.toHomeomorph.image_interior (nearKite v u w r)
    change e '' interior (nearKite v u w r) = interior (farKite v u w r) at hi
    have hb : e '' Metric.ball v r = Metric.ball (arrowheadBisectorPoint v u w r 2) r := by
      rw [← pointReflection_bisectorPoint v u w r]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Metric.mem_ball.mpr ((e.isometry.dist_eq y v).trans_lt (Metric.mem_ball.mp hy))
      · intro hx
        obtain ⟨y, rfl⟩ := e.surjective x
        refine ⟨y, Metric.mem_ball.mpr ?_, rfl⟩
        exact (e.isometry.dist_eq y v).symm.trans_lt (Metric.mem_ball.mp hx)
    change e '' interior (nearKite v u w r) \ e '' Metric.ball v r = _
    rw [hi, hb]
  · simp [nearArrowhead, farArrowhead, h]

/-- The near and far arrowheads have equal area, as required for cancellation. -/
theorem volume_nearArrowhead_eq_farArrowhead (v u w : PLPoint) (r : ℝ) :
    MeasureTheory.volume (nearArrowhead v u w r) =
      MeasureTheory.volume (farArrowhead v u w r) := by
  rw [← image_nearArrowhead_eq_farArrowhead]
  have he : (AffineIsometryEquiv.pointReflection ℝ
      (arrowheadBisectorPoint v u w r 1) : PLPoint → PLPoint) =
      AffineMap.homothety (arrowheadBisectorPoint v u w r 1) (-1 : ℝ) := by
    funext x
    rw [AffineIsometryEquiv.pointReflection_apply, AffineMap.homothety_apply]
    change arrowheadBisectorPoint v u w r 1 - x + arrowheadBisectorPoint v u w r 1 =
      (-1 : ℝ) • (x - arrowheadBisectorPoint v u w r 1) + arrowheadBisectorPoint v u w r 1
    simp [sub_eq_add_neg, add_comm]
  rw [he, MeasureTheory.Measure.addHaar_image_homothety]
  simp

end SteinerProof
