import SteinerProof.TriangleFacet
import SteinerProof.Separation

/-! The common vertex-face separation bounds the triangle inradii in Section 6.1. -/

open Set

noncomputable section

namespace Affine.Simplex

variable (T : Simplex ℝ Point2 2)

private theorem altitudeFoot_mem_opposite_hull_of_dist_le (i : Fin 3)
    (h₀ : dist (T.points i) ((T.faceOpposite i).points 0) ≤
      dist ((T.faceOpposite i).points 0) ((T.faceOpposite i).points 1))
    (h₁ : dist (T.points i) ((T.faceOpposite i).points 1) ≤
      dist ((T.faceOpposite i).points 0) ((T.faceOpposite i).points 1)) :
    T.altitudeFoot i ∈ convexHull ℝ (range (T.faceOpposite i).points) := by
  let F := T.faceOpposite i
  let x := F.points 0
  let y := F.points 1
  let z := T.altitudeFoot i
  let v := T.points i
  have hxy : 0 < dist x y := dist_pos.mpr
    (fun h => by have := F.independent.injective h; contradiction)
  have hpair : range F.points = {x, y} := by
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [x, y]
    · rintro (rfl | rfl)
      · exact mem_range_self (0 : Fin 2)
      · exact mem_range_self (1 : Fin 2)
  have hz : z ∈ affineSpan ℝ ({x, y} : Set Point2) := by
    rw [← hpair]
    exact T.altitudeFoot_mem_affineSpan_faceOpposite i
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  have hx := F.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq v
    (subset_affineSpan ℝ _ (mem_range_self (0 : Fin 2)))
  have hy := F.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq v
    (subset_affineSpan ℝ _ (mem_range_self (1 : Fin 2)))
  change dist x v * dist x v = dist x z * dist x z + dist v z * dist v z at hx
  change dist y v * dist y v = dist y z * dist y z + dist v z * dist v z at hy
  have hprojection (p : Point2)
      (hsq : dist p v * dist p v = dist p z * dist p z + dist v z * dist v z)
      (hp : dist p v ≤ dist x y) : dist p z ≤ dist x y := by
    refine le_trans (le_of_not_gt ?_) hp
    intro hn
    have hpv : 0 ≤ dist p v := dist_nonneg
    have hsum : 0 < dist p z + dist p v := by linarith
    nlinarith only [hsq, sq_nonneg (dist v z), mul_pos (sub_pos.mpr hn) hsum]
  have hdx := hprojection x hx (by simpa only [dist_comm x v] using h₀)
  have hdy := hprojection y hy (by simpa only [dist_comm y v] using h₁)

  rw [← ht, dist_left_lineMap, Real.norm_eq_abs] at hdx
  rw [← ht, dist_right_lineMap, Real.norm_eq_abs] at hdy
  have ht₀ : |t| ≤ 1 :=
    (mul_le_mul_iff_left₀ hxy).mp (by simpa only [one_mul] using hdx)
  have ht₁ : |1 - t| ≤ 1 :=
    (mul_le_mul_iff_left₀ hxy).mp (by simpa only [one_mul] using hdy)
  change z ∈ convexHull ℝ (range F.points)
  rw [hpair, convexHull_pair, segment_eq_image_lineMap]
  exact ⟨t, ⟨by linarith [(abs_le.mp ht₁).2], (abs_le.mp ht₀).2⟩, ht⟩

/-- Some minimum altitude lands on the opposite edge. -/
theorem exists_min_height_altitudeFoot_mem_opposite_hull :
    ∃ i : Fin 3,
      T.altitudeFoot i ∈ convexHull ℝ (range (T.faceOpposite i).points) ∧
      ∀ j : Fin 3, T.height i ≤ T.height j := by
  let L (i : Fin 3) :=
    dist ((T.faceOpposite i).points 0) ((T.faceOpposite i).points 1)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ L Finset.univ_nonempty
  have hle (j : Fin 3) : L j ≤ L i := hmax j (Finset.mem_univ j)
  have h₀ (k : Fin 3) :
      ∃ j : Fin 3, dist (T.points k) ((T.faceOpposite k).points 0) = L j := by
    fin_cases k
    · exact ⟨2, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; rfl⟩
    · exact ⟨2, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; exact dist_comm _ _⟩
    · exact ⟨1, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; exact dist_comm _ _⟩
  have h₁ (k : Fin 3) :
      ∃ j : Fin 3, dist (T.points k) ((T.faceOpposite k).points 1) = L j := by
    fin_cases k
    · exact ⟨1, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; rfl⟩
    · exact ⟨0, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; rfl⟩
    · exact ⟨0, by simp only [L, T.faceOpposite_point_eq_point_succAbove]; exact dist_comm _ _⟩
  obtain ⟨j₀, hj₀⟩ := h₀ i
  obtain ⟨j₁, hj₁⟩ := h₁ i
  refine ⟨i, T.altitudeFoot_mem_opposite_hull_of_dist_le i (hj₀.trans_le (hle j₀))
    (hj₁.trans_le (hle j₁)), ?_⟩
  intro j
  have hprod (k : Fin 3) : (2 : ℝ) * T.volume = T.height k * L k := by
    dsimp [L]
    rw [← volume_eq_dist, T.volume_eq k]
    ring
  have hi : 0 < L i := by
    rw [show L i = (T.faceOpposite i).volume from (volume_eq_dist _).symm]
    exact (T.faceOpposite i).volume_pos
  apply (mul_le_mul_iff_left₀ hi).mp
  rw [← hprod i, hprod j]
  exact mul_le_mul_of_nonneg_left (hle j) (T.height_pos j).le

theorem third_le_inradius_of_le_heights {M : ℝ} (hM : 0 < M)
    (hheight : ∀ i : Fin 3, M ≤ T.height i) : M / 3 ≤ T.inradius := by
  have hpos := T.sum_excenterWeightsUnnorm_empty_pos
  have hle : (∑ i, T.excenterWeightsUnnorm ∅ i) ≤ 3 * M⁻¹ := by
    calc
      _ ≤ ∑ _ : Fin 3, M⁻¹ := Finset.sum_le_sum fun i _ => by
        rw [T.excenterWeightsUnnorm_empty_apply]
        exact (inv_le_inv₀ (T.height_pos i) hM).mpr (hheight i)
      _ = _ := by simp
  rw [T.inradius_eq_abs_inv_sum, abs_of_pos (inv_pos.mpr hpos)]
  calc
    M / 3 = (3 * M⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]; ring
    _ ≤ (∑ i, T.excenterWeightsUnnorm ∅ i)⁻¹ :=
      (inv_le_inv₀ (by positivity : 0 < 3 * M⁻¹) hpos).mpr hle

end Affine.Simplex

namespace FinitePlanarComplex

/-- The vertex-face separation of an ambient triangulation gives the inradius
bound for every one of its three-vertex faces, including obtuse triangles. -/
theorem third_vertexFaceSeparation_le_triangle_inradius
    {K A : FinitePlanarComplex} (hAK : A.simplices.faces ⊆ K.simplices.faces)
    (s : Finset PLPoint) (hs : s ∈ A.simplices.faces) (hcard : s.card = 3) :
    K.vertexFaceSeparation / 3 ≤ (A.triangleOfFace s hs hcard).inradius := by
  classical
  let T := A.triangleOfFace s hs hcard
  have hT : range T.points = (s : Set PLPoint) := A.range_triangleOfFace s hs hcard
  obtain ⟨i, hi, hmin⟩ := T.exists_min_height_altitudeFoot_mem_opposite_hull
  have hv : T.points i ∈ (s : Set PLPoint) := hT ▸ Set.mem_range_self i
  have hvK : T.points i ∈ K.simplices.vertices :=
    K.simplices.down_closed (hAK hs) (Finset.singleton_subset_iff.mpr hv) (by simp)
  let e := s.erase (T.points i)
  have he : range (T.faceOpposite i).points = (e : Set PLPoint) := by
    rw [T.range_faceOpposite_points]
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Finset.mem_erase.mpr
        ⟨fun h => hj (Set.mem_singleton_iff.mpr (T.independent.injective h)),
          (show T.points j ∈ (s : Set PLPoint) from hT ▸ Set.mem_range_self j)⟩
    · intro hz
      obtain ⟨hne, hzS⟩ := Finset.mem_erase.mp hz
      obtain ⟨j, rfl⟩ : z ∈ range T.points := hT.symm ▸ (show z ∈ (s : Set PLPoint) from hzS)
      exact ⟨j, fun hj => hne (congrArg T.points hj), rfl⟩
  have heNonempty : e.Nonempty := by
    apply Finset.coe_nonempty.mp
    rw [← he]
    exact Set.range_nonempty _
  have heK : e ∈ K.simplices.faces :=
    K.simplices.down_closed (hAK hs) (Finset.erase_subset _ _) heNonempty
  have hheight : K.vertexFaceSeparation ≤ T.height i := by
    rw [he] at hi
    exact K.vertexFaceSeparation_le_dist hvK heK (Finset.notMem_erase _ _) hi
  exact T.third_le_inradius_of_le_heights K.vertexFaceSeparation_pos
    (fun j => hheight.trans (hmin j))

end FinitePlanarComplex
