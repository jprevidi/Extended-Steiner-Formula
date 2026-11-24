import Mathlib.Analysis.Convex.Measure
import SteinerProof.ArrowheadRecognition
import SteinerProof.ArrowheadSectors

/-! Ordinary offsets of two incident edges and their near arrowhead. -/

open Set MeasureTheory InnerProductGeometry NormedSpace
open scoped RealInnerProductSpace

noncomputable section

namespace SteinerProof

theorem measurableSet_nearArrowhead (v u w : PLPoint) (r : ℝ) :
    MeasurableSet (nearArrowhead v u w r) := by
  unfold nearArrowhead
  split
  · exact isOpen_interior.measurableSet.diff Metric.isOpen_ball.measurableSet
  · exact MeasurableSet.empty

private theorem isClosed_planar_segment (v u : PLPoint) : IsClosed (segment ℝ v u) := by
  rw [← convexHull_pair]
  exact ((finite_singleton u).insert v).isClosed_convexHull ℝ

private theorem convex_offset_of_isClosed {A : Set PLPoint} (hA : IsClosed A)
    (hconv : Convex ℝ A) (r : ℝ) : Convex ℝ (offset A r) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le hA).mp hx
  obtain ⟨q, hq, hyq⟩ := (mem_offset_iff_exists_dist_le hA).mp hy
  apply (mem_offset_iff_exists_dist_le hA).mpr
  refine ⟨a • p + b • q, hconv hp hq ha hb hab, ?_⟩
  have hvec : (a • x + b • y) - (a • p + b • q) = a • (x-p) + b • (y-q) := by
    rw [smul_sub, smul_sub]
    abel
  rw [dist_eq_norm, hvec]
  calc
    _ ≤ ‖a • (x-p)‖ + ‖b • (y-q)‖ := norm_add_le _ _
    _ = a * dist x p + b * dist y q := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb, ← dist_eq_norm, ← dist_eq_norm]
    _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left hxp ha) (mul_le_mul_of_nonneg_left hyq hb)
    _ = r := by rw [← add_mul, hab, one_mul]

private theorem offset_pos_projection_of_outside_disk {v u x p : PLPoint}
    (hp : p ∈ segment ℝ v u) {r : ℝ} (hxp : dist x p ≤ r) (hx : r < dist x v) :
    0 < ⟪x-v, normalize (u-v)⟫ := by
  obtain ⟨t, ht, htp⟩ := (segment_eq_image_lineMap ℝ v u) ▸ hp
  have hp' : p-v = (t * ‖u-v‖) • normalize (u-v) := by
    rw [← htp, AffineMap.lineMap_apply_module', add_sub_cancel_right, mul_smul, norm_smul_normalize]
  by_contra! hn
  have hin : ⟪x-v, p-v⟫ ≤ 0 := by
    rw [hp', real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.1 (norm_nonneg _)) hn
  have h := norm_sub_sq_real (x-v) (p-v)
  rw [show (x-v)-(p-v) = x-p by abel, ← dist_eq_norm, ← dist_eq_norm] at h
  have hh : dist x p ^ 2 < dist x v ^ 2 := pow_lt_pow_left₀ (hxp.trans_lt hx) dist_nonneg (by decide)
  linarith only [h, hh, hin, sq_nonneg ‖p-v‖]

private theorem offset_bounds_in_edge_directions {v u w x : PLPoint} {a b r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hr : 0 < r) (hθ : 0 < angle (u-v) (w-v))
    (hπ : angle (u-v) (w-v) < Real.pi)
    (hrep : x-v = a • normalize (u-v) + b • normalize (w-v))
    (hx : x ∈ offset (segment ℝ v u) r) (hDisc : r < dist x v) :
    0 ≤ a + Real.cos (angle (u-v) (w-v))*b ∧ b ≤ r/Real.sin (angle (u-v) (w-v)) := by
  let X := normalize (u-v)
  let Y := normalize (w-v)
  let N := nearKiteShoulder v u w r - v
  let θ := angle (u-v) (w-v)
  let c := Real.cos θ
  let s := Real.sin θ
  obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le (isClosed_planar_segment v u)).mp hx
  have hPos : 0 ≤ ⟪x-v, X⟫ := (offset_pos_projection_of_outside_disk hp hxp hDisc).le
  have hYX : ⟪Y,X⟫ = c := (real_inner_comm _ _).trans
    (inner_normalize_eq_cos_angle (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hw))
  rw [hrep, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_normalize (sub_ne_zero.mpr hu), one_pow, mul_one, hYX, mul_comm b c] at hPos
  refine ⟨hPos, ?_⟩
  obtain ⟨hXN, hYN⟩ := inner_nearKiteShoulder_directions (r := r) hu hw hθ hπ
  have hN : ‖N‖ = r := by
    simpa only [N, ← dist_eq_norm] using (nearKiteShoulder_right_angle hr.le hu hw hθ hπ).1
  obtain ⟨t, _, htp⟩ := (segment_eq_image_lineMap ℝ v u) ▸ hp
  have hp' : p-v = (t * ‖u-v‖) • X := by
    rw [← htp, AffineMap.lineMap_apply_module', add_sub_cancel_right, mul_smul, norm_smul_normalize]
  have hinner : ⟪x-p,N⟫ = b*(r*s) := by
    rw [show x-p = (x-v)-(p-v) by abel, hrep, hp', inner_sub_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hXN, hYN]
    ring
  have hlim := real_inner_le_norm (x-p) N
  rw [hinner, hN, ← dist_eq_norm] at hlim
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  apply (le_div_iff₀ hs).mpr
  apply (mul_le_mul_iff_right₀ hr).mp
  have hh := hlim.trans (mul_le_mul_of_nonneg_right hxp hr.le)
  linarith only [hh]

/-- The weak longitudinal and transverse bounds suffice for membership of the
closed near kite. Split the kite along the segment joining `v` to `p₁`. -/
private theorem mem_nearKite_of_edge_direction_bounds {v u w x : PLPoint} {a b r : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hr : 0 < r) (hθ : 0 < angle (u-v) (w-v))
    (hπ : angle (u-v) (w-v) < Real.pi)
    (hrep : x-v = a • normalize (u-v) + b • normalize (w-v))
    (h₀ : 0 ≤ a + Real.cos (angle (u-v) (w-v))*b)
    (h₁ : 0 ≤ b + Real.cos (angle (u-v) (w-v))*a)
    (ha : a ≤ r/Real.sin (angle (u-v) (w-v))) (hb : b ≤ r/Real.sin (angle (u-v) (w-v))) :
    x ∈ nearKite v u w r := by
  let θ := angle (u-v) (w-v)
  let c := Real.cos θ
  let s := Real.sin θ
  let k := r/s
  let L := k*(1+c)
  let Q := arrowheadBisectorPoint v u w r 1
  let C := nearKite v u w r
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hk : 0 < k := div_pos hr hs
  have hL : 0 < L := mul_pos hk (by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le (le_refl Real.pi) hπ
    rw [Real.cos_pi] at h
    change -1 < c at h
    linarith)
  have hC : Convex ℝ C := convex_convexHull ℝ _
  have hv : v ∈ C := subset_convexHull ℝ _ (by simp)
  have hQ : Q ∈ C := subset_convexHull ℝ _ (by simp [Q])
  have hSide {X Y S : PLPoint} {a b : ℝ} (hS : S ∈ C)
      (hQvec : Q-v = k • X + k • Y) (hSvec : S-v = (-k*c) • X + k • Y)
      (hx : x-v = a • X + b • Y) (hba : a ≤ b) (hPos : 0 ≤ a+c*b) (hb : b ≤ k) : x ∈ C := by
    let β := (b-a)/L
    let α := (a+c*b)/L
    have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hba) hL.le
    have hα : 0 ≤ α := div_nonneg hPos hL.le
    have hβL : β*L = b-a := div_mul_cancel₀ _ hL.ne'
    have hαL : α*L = a+c*b := div_mul_cancel₀ _ hL.ne'
    have hkc : 0 < 1+c := pos_of_mul_pos_right hL hk.le
    have hsum : (α+β)*k = b := by
      apply (mul_left_inj' hkc.ne').mp
      rw [mul_assoc, show k*(1+c)=L from rfl, add_mul, hαL, hβL]
      ring
    have hab : α+β ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hk).mp
      simpa only [hsum, one_mul] using hb
    have hαβ : α*k - β*k*c = a := by
      have hh : α*k + β*k = b := by rwa [add_mul] at hsum
      dsimp only [L] at hαL
      nlinarith only [hαL, congrArg (fun t : ℝ => c*t) hh]
    have hcombo := convex_three_point_mem hC hv hQ hS hα hβ hab
    have hvec : (1-α-β) • v + α • Q + β • S = x := by
      have hQ' : Q = v + (k • X + k • Y) := by rw [← hQvec]; abel
      have hS' : S = v + ((-k*c) • X + k • Y) := by rw [← hSvec]; abel
      rw [hQ', hS']
      have hh : α*k + β*k = b := by rwa [add_mul] at hsum
      have hCoeff : α*k + β*(-k*c) = a := by linarith only [hαβ]
      have hx' : x = v + (a • X + b • Y) := by rw [← hx]; abel
      rw [hx']
      simp only [smul_add, smul_smul, sub_smul, one_smul, ← hCoeff, ← hh, add_smul]
      abel
    exact hvec ▸ hcombo
  have hQvec : Q-v = k • normalize (u-v) + k • normalize (w-v) := by
    simp only [Q, arrowheadBisectorPoint, one_mul, add_sub_cancel_left, smul_add, k, s, θ]
  have hSVec {u' w' : PLPoint} (hu' : u' ≠ v) (hw' : w' ≠ v)
      (hθ' : angle (u'-v) (w'-v) = θ) : nearKiteShoulder v u' w' r-v =
        (-k*c) • normalize (u'-v) + k • normalize (w'-v) := by
    rw [nearKiteShoulder_sub_vertex_eq hu' hw', hθ']
    change k • (normalize (w'-v) - c • normalize (u'-v)) = _
    rw [smul_sub, smul_smul, neg_mul, neg_smul]
    abel
  rcases le_total a b with hab | hab
  · have hS : nearKiteShoulder v u w r ∈ C := subset_convexHull ℝ _ (by simp)
    exact hSide hS hQvec (hSVec hu hw rfl) hrep hab h₀ hb
  · have hS : nearKiteShoulder v w u r ∈ C := subset_convexHull ℝ _ (by simp)
    exact hSide hS (hQvec.trans (add_comm _ _)) (hSVec hw hu (angle_comm _ _))
      (hrep.trans (add_comm _ _)) hab h₁ ha

/-- At the paper's admissible radius, two incident edge offsets meet in the
endpoint disk together with the closed near kite. -/
theorem inter_edge_offsets_eq_closedBall_union_nearKite {K : FinitePlanarComplex}
    {v u w : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hπ : angle (u-v) (w-v) < Real.pi) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r =
      Metric.closedBall v r ∪ nearKite v u w r := by
  let Q := arrowheadBisectorPoint v u w r 1
  let U := offset (segment ℝ v u) r
  let W := offset (segment ℝ v w) r
  have huv := FinitePlanarComplex.edge_endpoints_ne hu
  have hwv := FinitePlanarComplex.edge_endpoints_ne hw
  have hθ := K.incident_angle_pos hu hw huw
  have hDisk : Metric.closedBall v r ⊆ U ∩ W := by
    intro x hx
    have hx' := Metric.mem_closedBall.mp hx
    exact ⟨(mem_offset_iff_exists_dist_le (isClosed_planar_segment v u)).mpr
      ⟨v, left_mem_segment ℝ v u, hx'⟩, (mem_offset_iff_exists_dist_le (isClosed_planar_segment v w)).mpr
      ⟨v, left_mem_segment ℝ v w, hx'⟩⟩
  have hQ : Q ∈ U ∩ W := by
    have hU := infDist_arrowheadBisectorPoint_edge hu hw huw hπ hr hR
      (show (0 : ℝ) ≤ 1 by norm_num) (by norm_num)
    have hW := infDist_arrowheadBisectorPoint_other_edge hu hw huw hπ hr hR
      (show (0 : ℝ) ≤ 1 by norm_num) (by norm_num)
    exact ⟨⟨⟨v, left_mem_segment ℝ v u⟩, by simpa only [Q, hU, one_mul] using (le_rfl : r ≤ r)⟩,
      ⟨⟨v, left_mem_segment ℝ v w⟩, by simpa only [Q, hW, one_mul] using (le_rfl : r ≤ r)⟩⟩
  have hKite : nearKite v u w r ⊆ U ∩ W := by
    apply convexHull_min _ ((convex_offset_of_isClosed (isClosed_planar_segment v u) (convex_segment v u) r).inter
      (convex_offset_of_isClosed (isClosed_planar_segment v w) (convex_segment v w) r))
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hDisk (Metric.mem_closedBall_self hr.le)
    · exact hQ
    · exact hDisk (Metric.mem_closedBall.mpr (nearKiteShoulder_right_angle hr.le huv hwv hθ hπ).1.le)
    · exact hDisk (Metric.mem_closedBall.mpr (nearKiteShoulder_right_angle hr.le hwv huv
        (by rwa [angle_comm]) (by rwa [angle_comm])).1.le)
  refine Subset.antisymm ?_ (union_subset hDisk hKite)
  rintro x ⟨hxU, hxW⟩
  by_cases hx : x ∈ Metric.closedBall v r
  · exact Or.inl hx
  · apply Or.inr
    have hx' : r < dist x v := lt_of_not_ge fun h => hx (Metric.mem_closedBall.mpr h)
    obtain ⟨B,hB₀,hB₁⟩ := exists_incident_basis huv hwv hθ hπ
    let a := B.repr (x-v) 0 * ‖u-v‖
    let b := B.repr (x-v) 1 * ‖w-v‖
    have hrep : x-v = a • normalize (u-v) + b • normalize (w-v) := by
      dsimp only [a,b]
      rw [mul_smul, mul_smul, norm_smul_normalize, norm_smul_normalize, ← hB₀, ← hB₁]
      have h := B.sum_repr (x-v)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    obtain ⟨h₀,hb⟩ := offset_bounds_in_edge_directions huv hwv hr hθ hπ hrep hxU hx'
    obtain ⟨h₁,ha⟩ := offset_bounds_in_edge_directions hwv huv hr (by rwa [angle_comm]) (by rwa [angle_comm])
      (hrep.trans (add_comm _ _)) hxW hx'
    rw [angle_comm (w-v) (u-v)] at h₁ ha
    exact mem_nearKite_of_edge_direction_bounds huv hwv hr hθ hπ hrep h₀ h₁ ha hb

/-- The kite frontier and the circle can be omitted from the overlap
without changing it almost everywhere. -/
theorem inter_edge_offsets_ae_eq_ball_union_nearArrowhead {K : FinitePlanarComplex}
    {v u w : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hπ : angle (u-v) (w-v) < Real.pi) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r =ᵐ[volume]
      Metric.ball v r ∪ nearArrowhead v u w r := by
  rw [inter_edge_offsets_eq_closedBall_union_nearKite hu hw huw hπ hr hR]
  have hK : Convex ℝ (nearKite v u w r) := convex_convexHull ℝ _
  have hFront : ∀ᵐ x ∂(volume : Measure PLPoint), x ∉ frontier (nearKite v u w r) :=
    ae_iff.mpr (by simpa only [not_not, Set.setOf_mem_eq] using hK.addHaar_frontier volume)
  have hCircle : ∀ᵐ x ∂(volume : Measure PLPoint), x ∉ Metric.sphere v r :=
    ae_iff.mpr (by simpa only [not_not, Set.setOf_mem_eq] using Measure.addHaar_sphere volume v r)
  filter_upwards [hFront,hCircle] with x hx hc
  rw [nearArrowhead, ite_eq_left hπ]
  constructor
  · intro h
    by_cases hb : x ∈ Metric.ball v r
    · exact Or.inl hb
    · apply Or.inr
      have hk : x ∈ nearKite v u w r := by
        refine h.resolve_left (fun hd => hc (Metric.mem_sphere.mpr ?_))
        exact le_antisymm (Metric.mem_closedBall.mp hd) (le_of_not_gt (fun hlt => hb (Metric.mem_ball.mpr hlt)))
      refine ⟨?_, hb⟩
      by_contra h
      exact hx ⟨subset_closure hk, h⟩
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl (Metric.ball_subset_closedBall h)
    · exact Or.inr (interior_subset h)

/-- In area, the overlap of two incident edge offsets is the endpoint disk
plus the near arrowhead. -/
theorem volume_inter_edge_offsets_eq_ball_add_nearArrowhead {K : FinitePlanarComplex}
    {v u w : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hπ : angle (u-v) (w-v) < Real.pi) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    volume (offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r) =
      volume (Metric.ball v r) + volume (nearArrowhead v u w r) := by
  rw [measure_congr (inter_edge_offsets_ae_eq_ball_union_nearArrowhead hu hw huw hπ hr hR)]
  apply measure_union' _ Metric.isOpen_ball.measurableSet
  apply Set.disjoint_left.mpr
  intro x hx hA
  rw [nearArrowhead, ite_eq_left hπ] at hA
  exact hA.2 hx

/-- Offsets of two edges in opposite directions meet exactly in their
common endpoint disk, including the circle. -/
theorem inter_edge_offsets_of_angle_eq_pi {v u w : PLPoint} {r : ℝ}
    (hπ : angle (u-v) (w-v) = Real.pi) :
    offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r = Metric.closedBall v r := by
  obtain ⟨_,t,ht,hrep⟩ := angle_eq_pi_iff.mp hπ
  have hOpp : normalize (w-v) = -normalize (u-v) := by
    rw [hrep, normalize_smul_of_neg ht]
  ext x
  constructor
  · rintro ⟨hu,hw⟩
    by_contra hn
    have hDisc : r < dist x v := lt_of_not_ge (fun h => hn (Metric.mem_closedBall.mpr h))
    obtain ⟨p,hp,hxp⟩ := (mem_offset_iff_exists_dist_le (isClosed_planar_segment v u)).mp hu
    obtain ⟨q,hq,hxq⟩ := (mem_offset_iff_exists_dist_le (isClosed_planar_segment v w)).mp hw
    have hU := offset_pos_projection_of_outside_disk hp hxp hDisc
    have hW := offset_pos_projection_of_outside_disk hq hxq hDisc
    rw [hOpp, inner_neg_right] at hW
    linarith only [hU,hW]
  · intro hx
    have hx' := Metric.mem_closedBall.mp hx
    exact ⟨(mem_offset_iff_exists_dist_le (isClosed_planar_segment v u)).mpr
      ⟨v, left_mem_segment ℝ v u, hx'⟩, (mem_offset_iff_exists_dist_le (isClosed_planar_segment v w)).mpr
      ⟨v, left_mem_segment ℝ v w, hx'⟩⟩

private theorem ray_distance_ge_half_angle {u w : PLPoint} {a b : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b * Real.sin (angle u w / 2) ≤ ‖a • normalize u - b • normalize w‖ := by
  let θ := angle u w
  let c := Real.cos θ
  let d := ‖a • normalize u - b • normalize w‖
  have hsq : d^2 = a^2 - 2*a*b*c + b^2 := by
    dsimp only [d]
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb, norm_normalize hu, norm_normalize hw,
      real_inner_smul_left, real_inner_smul_right, inner_normalize_eq_cos_angle hu hw]
    change (a*1)^2 - 2*(a*(b*c)) + (b*1)^2 = _
    ring
  change b * Real.sin (θ/2) ≤ d
  have hd : 0 ≤ d := norm_nonneg _
  by_cases hc : 0 ≤ c
  · have hθ₂ : θ ≤ Real.pi/2 := by
      by_contra! h
      have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi/2) (angle_le_pi _ _) h
      rw [Real.cos_pi_div_two] at hcos
      exact (not_lt_of_ge hc) hcos
    have hs : Real.sin (θ/2) ≤ Real.sin θ := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos, angle_nonneg u w]) hθ₂ (by linarith [angle_nonneg u w])
    refine (mul_le_mul_of_nonneg_left hs hb).trans ?_
    apply (sq_le_sq₀ (mul_nonneg hb (sin_angle_nonneg _ _)) hd).mp
    have hh : d^2 - (b * Real.sin θ)^2 = (a-b*c)^2 := by
      rw [hsq]
      linear_combination -b^2 * Real.sin_sq_add_cos_sq θ
    linarith only [hh, sq_nonneg (a-b*c)]
  · refine (mul_le_of_le_one_right hb (Real.sin_le_one _)).trans ?_
    apply (sq_le_sq₀ hb hd).mp
    linarith only [hsq, sq_nonneg a, mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) (le_of_not_ge hc)]

/-- The intervening-edge inclusion. The coordinates in the two edge
directions say that the other set is on the intervening edge's side of
the first edge and lies beyond the intervening edge. -/
theorem inter_offset_subset_offset_of_intervening_edge {K : FinitePlanarComplex}
    {v u w : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hπ : angle (u-v) (w-v) < Real.pi) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    {S : Set PLPoint} (hS : IsClosed S)
    (hSide : ∀ y ∈ S, B.repr (y-v) 0 ≤ 0 ∧ 0 ≤ B.repr (y-v) 1) :
    offset (segment ℝ v u) r ∩ offset S r ⊆ offset (segment ℝ v w) r := by
  rintro x ⟨hxU,hxS⟩
  apply (mem_offset_iff_exists_dist_le (isClosed_planar_segment v w)).mpr
  by_cases hx : dist x v ≤ r
  · exact ⟨v, left_mem_segment ℝ v w, hx⟩
  obtain ⟨p, hp, hxp⟩ := (mem_offset_iff_exists_dist_le (isClosed_planar_segment v u)).mp hxU
  obtain ⟨y, hy, hxy⟩ := (mem_offset_iff_exists_dist_le hS).mp hxS
  obtain ⟨a, ha, hap⟩ := (segment_eq_image_lineMap ℝ v u) ▸ hp
  have ha₀ : 0 < a := by
    refine lt_of_le_of_ne ha.1 fun h => hx ?_
    have hh : p = v := by simpa [← h] using hap.symm
    simpa [hh] using hxp
  have hpDir : p-v = a • (u-v) := by
    rw [← hap, AffineMap.lineMap_apply_module', add_sub_cancel_right]
  have hp₀ : B.repr (p-v) 0 = a := by
    rw [hpDir, ← hB₀, map_smul, Module.Basis.repr_self]
    simp
  have hp₁ : B.repr (p-v) 1 = 0 := by
    rw [hpDir, ← hB₀, map_smul, Module.Basis.repr_self]
    simp
  obtain ⟨hy₀,hy₁⟩ := hSide y hy
  let c := B.repr (y-v) 0
  have hd : 0 < a-c := sub_pos.mpr (hy₀.trans_lt ha₀)
  let t := a/(a-c)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha₀.le hd.le, (div_le_one hd).mpr (by dsimp [c]; linarith)⟩
  let q := AffineMap.lineMap p y t
  have hqSeg : q ∈ segment ℝ p y := by
    rw [segment_eq_image_lineMap]
    exact ⟨t,ht,rfl⟩
  have hxq : dist x q ≤ r := by
    have hh := (convex_closedBall x r).segment_subset
      (Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hxp))
      (Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hxy)) hqSeg
    simpa only [Metric.mem_closedBall, dist_comm q x] using hh
  have hlin : q-v = (1-t) • (p-v) + t • (y-v) := by
    have hv : (1-t) • v + t • v = v := by rw [← add_smul, sub_add_cancel, one_smul]
    dsimp [q]
    rw [AffineMap.lineMap_apply_module, smul_sub, smul_sub, sub_add_sub_comm, hv]
  have hq₀ : B.repr (q-v) 0 = 0 := by
    rw [hlin, sector_coordinate_of_combination, hp₀]
    change (1-t)*a+t*c = 0
    have hmul : t*(a-c) = a := div_mul_cancel₀ _ hd.ne'
    linarith only [hmul]
  let b := B.repr (q-v) 1
  have hb : 0 ≤ b := by
    dsimp only [b]
    rw [hlin, sector_coordinate_of_combination, hp₁, mul_zero, zero_add]
    exact mul_nonneg ht.1 hy₁
  have hqDir : q-v = b • (w-v) := by
    have h := B.sum_repr (q-v)
    rw [Fin.sum_univ_two, hq₀, zero_smul, zero_add, hB₁] at h
    exact h.symm
  have hdist : dist q v = b * ‖w-v‖ := by
    rw [dist_eq_norm, hqDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have hhalf : dist q v * Real.sin (angle (u-v) (w-v) / 2) ≤ dist p q := by
    have h := ray_distance_ge_half_angle (sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hu))
      (sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hw))
      (mul_nonneg ha₀.le (norm_nonneg (u-v))) (mul_nonneg hb (norm_nonneg (w-v)))
    rw [mul_smul, mul_smul, norm_smul_normalize, norm_smul_normalize, ← hpDir, ← hqDir] at h
    rw [show (p-v)-(q-v) = p-q by abel, ← dist_eq_norm p q, ← hdist] at h
    exact h
  have hpq : dist p q ≤ 2*r := by linarith [dist_triangle_left p q x]
  have hθ := K.incident_angle_pos hu hw huw
  let θ := angle (u-v) (w-v)
  have hs : 0 < Real.sin (θ/2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [show 0 < θ from hθ]) (by linarith [show θ < Real.pi from hπ, Real.pi_pos])
  have hbound : dist q v ≤ 2*r*(Real.sin (θ/2))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hs).mpr (hhalf.trans hpq)
  have hSep := K.four_mul_csc_lt_separation hu hw huw hθ hr hR
  have hlen := FinitePlanarComplex.vertexFaceSeparation_le_edge_dist hw
  rw [dist_comm v w, dist_eq_norm] at hlen
  have hb₁ : b ≤ 1 := by
    have hnorm : 0 < ‖w-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (FinitePlanarComplex.edge_endpoints_ne hw))
    apply (mul_le_mul_iff_left₀ hnorm).mp
    rw [← hdist, one_mul]
    have hh : 2*r*(Real.sin (θ/2))⁻¹ < K.vertexFaceSeparation := by
      change 4*r*(Real.sin (θ/2))⁻¹ < K.vertexFaceSeparation at hSep
      linarith [K.vertexFaceSeparation_pos]
    exact (hbound.trans hh.le).trans hlen
  refine ⟨q, ?_, hxq⟩
  rw [segment_eq_image_lineMap]
  refine ⟨b, ⟨hb,hb₁⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module', ← hqDir]
  abel

theorem inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead {K : FinitePlanarComplex}
    {v u w : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hπ : angle (u-v) (w-v) < Real.pi) {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    (offset (segment ℝ v u) r ∩ offset (segment ℝ v w) r) \ Metric.ball v r =ᵐ[volume]
      nearArrowhead v u w r := by
  filter_upwards [inter_edge_offsets_ae_eq_ball_union_nearArrowhead hu hw huw hπ hr hR] with x hx
  constructor
  · rintro ⟨h,hnot⟩
    exact (hx.mp h).resolve_left hnot
  · intro h
    have hout : x ∉ Metric.ball v r := by
      rw [nearArrowhead, ite_eq_left hπ] at h
      exact h.2
    exact ⟨hx.mpr (Or.inr h),hout⟩

/-- The non-reflex overlap of near arrowheads at an endpoint. A positive
combination of the two neighboring directions encodes the intervening edge. -/
theorem nearArrowhead_inter_ae_eq_of_intervening_edge {K : FinitePlanarComplex}
    {v u w z : PLPoint} (hu : ({v,u} : Finset PLPoint) ∈ K.edges)
    (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (hz : ({v,z} : Finset PLPoint) ∈ K.edges)
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z)
    (hπ₁ : angle (u-v) (w-v) < Real.pi) (hπ₂ : angle (u-v) (z-v) < Real.pi)
    (hπ₃ : angle (w-v) (z-v) < Real.pi)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hInter : u-v = a • (w-v) + b • (z-v))
    {r : ℝ} (hr : 0 < r) (hR : r < K.admissibleRadius) :
    nearArrowhead v u w r ∩ nearArrowhead v u z r =ᵐ[volume] nearArrowhead v w z r := by
  have hθ := K.incident_angle_pos hw hu huw.symm
  obtain ⟨B,hB₀,hB₁⟩ := exists_incident_basis (FinitePlanarComplex.edge_endpoints_ne hw)
    (FinitePlanarComplex.edge_endpoints_ne hu) hθ (by rwa [angle_comm])
  have hzDirection : z-v = (-a/b) • B 0 + (1/b) • B 1 := by
    have hmove : b • (z-v) = (u-v)-a • (w-v) := by rw [hInter]; abel
    calc
      _ = (1/b) • (b • (z-v)) := by rw [smul_smul, one_div_mul_cancel hb.ne', one_smul]
      _ = _ := by
        rw [hmove, hB₀, hB₁, smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul, add_comm]
        congr 2
        ring
  have hSide (y : PLPoint) (hy : y ∈ segment ℝ v z) : B.repr (y-v) 0 ≤ 0 ∧ 0 ≤ B.repr (y-v) 1 := by
    obtain ⟨s,hs,hsy⟩ := (segment_eq_image_lineMap ℝ v z) ▸ hy
    have hy' : y-v = (s*(-a/b)) • B 0 + (s*(1/b)) • B 1 := by
      rw [← hsy, AffineMap.lineMap_apply_module', add_sub_cancel_right, hzDirection, smul_add, smul_smul, smul_smul]
    rw [hy', sector_coordinate_of_combination, sector_coordinate_of_combination, Module.Basis.repr_self,
      Module.Basis.repr_self]
    simpa using And.intro (mul_nonpos_of_nonneg_of_nonpos hs.1 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hb.le))
      (mul_nonneg hs.1 (div_nonneg zero_le_one hb.le))
  have hContain := inter_offset_subset_offset_of_intervening_edge hw hu huw.symm (by rwa [angle_comm])
    hr hR B hB₀ hB₁ (isClosed_planar_segment v z) hSide
  filter_upwards [inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead hu hw huw hπ₁ hr hR,
    inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead hu hz huz hπ₂ hr hR,
    inter_edge_offsets_sdiff_ball_ae_eq_nearArrowhead hw hz hwz hπ₃ hr hR] with x h₁ h₂ h₃
  constructor
  · rintro ⟨hu₁,hu₂⟩
    obtain ⟨⟨_,hW⟩,hOut⟩ := h₁.mpr hu₁
    obtain ⟨⟨_,hZ⟩,_⟩ := h₂.mpr hu₂
    exact h₃.mp ⟨⟨hW,hZ⟩,hOut⟩
  · intro h
    obtain ⟨⟨hW,hZ⟩,hOut⟩ := h₃.mpr h
    have hU := hContain (show x ∈ offset (segment ℝ v w) r ∩ offset (segment ℝ v z) r from ⟨hW,hZ⟩)
    exact ⟨h₁.mp ⟨⟨hU,hW⟩,hOut⟩,h₂.mp ⟨⟨hU,hZ⟩,hOut⟩⟩

/-- In the reflex configuration the opposite of the deleted edge lies in
the open sector of the two neighboring edges. The near kites meet only at
their common endpoint. -/
theorem nearKite_inter_eq_singleton_of_reflex {v u w z : PLPoint} {r a b : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hz : z ≠ v) (hr : 0 ≤ r)
    (hθ₁ : 0 < angle (u - v) (w - v)) (hθ₂ : 0 < angle (u - v) (z - v))
    (hπ₁ : angle (u - v) (w - v) < Real.pi) (hπ₂ : angle (u - v) (z - v) < Real.pi)
    (ha : 0 < a) (hb : 0 < b) (hReflex : -(u - v) = a • (w - v) + b • (z - v)) :
    nearKite v u w r ∩ nearKite v u z r = {v} := by
  ext x
  constructor
  · rintro ⟨hx₁, hx₂⟩
    have hwK : x ∈ nearKite v w u r := nearKite_comm v u w r ▸ hx₁
    have hzK : x ∈ nearKite v z u r := nearKite_comm v u z r ▸ hx₂
    have hU := inner_nonneg_of_mem_nearKite hr hu hw hθ₁ hπ₁ hx₁
    have hW := inner_nonneg_of_mem_nearKite hr hw hu (by rwa [angle_comm]) (by rwa [angle_comm]) hwK
    have hZ := inner_nonneg_of_mem_nearKite hr hz hu (by rwa [angle_comm]) (by rwa [angle_comm]) hzK
    have hRaw {y : PLPoint} (hy : 0 ≤ ⟪x - v, normalize (y - v)⟫) : 0 ≤ ⟪x - v, y - v⟫ := by
      calc
        0 ≤ ‖y - v‖ * ⟪x - v, normalize (y - v)⟫ := mul_nonneg (norm_nonneg _) hy
        _ = ⟪x - v, ‖y - v‖ • normalize (y - v)⟫ := (real_inner_smul_right _ _ _).symm
        _ = _ := by rw [norm_smul_normalize]
    have huRaw := hRaw hU
    have hwRaw := hRaw hW
    have hzRaw := hRaw hZ
    have hs : -⟪x - v, u - v⟫ = a * ⟪x - v, w - v⟫ + b * ⟪x - v, z - v⟫ := by
      calc
        _ = ⟪x - v, -(u - v)⟫ := (inner_neg_right _ _).symm
        _ = _ := by rw [hReflex, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hu₀ : ⟪x - v, u - v⟫ = 0 := by
      linarith only [hs, huRaw, mul_nonneg ha.le hwRaw, mul_nonneg hb.le hzRaw]
    have hw₀ : ⟪x - v, w - v⟫ = 0 := by
      refine le_antisymm (le_of_not_gt fun h => ?_) hwRaw
      linarith only [hs, hu₀, mul_pos ha h, mul_nonneg hb.le hzRaw]
    obtain ⟨B, hB₀, hB₁⟩ := exists_incident_basis hu hw hθ₁ hπ₁
    have hrep := B.sum_repr (x - v)
    rw [Fin.sum_univ_two, hB₀, hB₁] at hrep
    have hZero : ⟪x - v, x - v⟫ = 0 := calc
      _ = ⟪x - v, B.repr (x - v) 0 • (u - v) + B.repr (x - v) 1 • (w - v)⟫ :=
        congrArg (fun t : PLPoint => ⟪x - v, t⟫) hrep.symm
      _ = _ := by simp only [inner_add_right, real_inner_smul_right, hu₀, hw₀, mul_zero, add_zero]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hZero)
  · rintro rfl
    exact ⟨subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp)⟩

theorem disjoint_nearArrowheads_of_reflex {v u w z : PLPoint} {r a b : ℝ}
    (hu : u ≠ v) (hw : w ≠ v) (hz : z ≠ v) (hr : 0 < r)
    (hθ₁ : 0 < angle (u - v) (w - v)) (hθ₂ : 0 < angle (u - v) (z - v))
    (hπ₁ : angle (u - v) (w - v) < Real.pi) (hπ₂ : angle (u - v) (z - v) < Real.pi)
    (ha : 0 < a) (hb : 0 < b) (hReflex : -(u - v) = a • (w - v) + b • (z - v)) :
    Disjoint (nearArrowhead v u w r) (nearArrowhead v u z r) := by
  apply Set.disjoint_left.mpr
  intro x h₁ h₂
  rw [nearArrowhead, ite_eq_left hπ₁] at h₁
  rw [nearArrowhead, ite_eq_left hπ₂] at h₂
  have hx : x ∈ nearKite v u w r ∩ nearKite v u z r := ⟨interior_subset h₁.1, interior_subset h₂.1⟩
  rw [nearKite_inter_eq_singleton_of_reflex hu hw hz hr.le hθ₁ hθ₂ hπ₁ hπ₂ ha hb hReflex] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact h₁.2 (Metric.mem_ball_self hr)

end SteinerProof
