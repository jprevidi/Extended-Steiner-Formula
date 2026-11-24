import SteinerProof.Background
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Finite extensions of a planar complex inside the hull of its vertices. -/

open Set

noncomputable section

namespace FinitePlanarComplex

theorem finite_vertexSet (K : FinitePlanarComplex) : K.simplices.vertices.Finite := by
  rw [K.simplices.vertices_eq]
  exact K.finite_faces.biUnion fun s _ => s.finite_toSet

private theorem face_subset_vertexSet {K : FinitePlanarComplex} {s : Finset PLPoint}
    (hs : s ∈ K.simplices.faces) : (s : Set PLPoint) ⊆ K.simplices.vertices :=
  fun x hx => K.simplices.down_closed hs (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

/-- Taking the hull of the realization only requires the finitely many vertices. -/
theorem convexHull_realization_eq_convexHull_vertices (K : FinitePlanarComplex) :
    convexHull ℝ K.realization = convexHull ℝ K.simplices.vertices := by
  apply Subset.antisymm
  · apply convexHull_min ?_ (convex_convexHull _ _)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := (K.mem_realization_iff x).mp hx
    exact convexHull_mono (face_subset_vertexSet hs) hxs
  · exact convexHull_mono K.simplices.vertices_subset_space

/-- Enlarge a complex maximally among complexes with the same vertices. -/
theorem exists_maximal_vertex_extension (A : FinitePlanarComplex) :
    ∃ K : FinitePlanarComplex,
      A.simplices.faces ⊆ K.simplices.faces ∧ K.simplices.vertices = A.simplices.vertices ∧
      ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
        L.simplices.vertices ⊆ A.simplices.vertices → L.simplices.faces = K.simplices.faces := by
  classical
  let V := A.finite_vertexSet.toFinset
  let candidates := V.powerset.powerset.filter fun F =>
    ∃ K : FinitePlanarComplex, K.faceFinset = F ∧
      A.simplices.faces ⊆ K.simplices.faces ∧ K.simplices.vertices ⊆ A.simplices.vertices
  have hmem (K : FinitePlanarComplex) (hA : A.simplices.faces ⊆ K.simplices.faces)
      (hV : K.simplices.vertices ⊆ A.simplices.vertices) : K.faceFinset ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, K, rfl, hA, hV⟩
    intro s hs
    apply Finset.mem_powerset.mpr
    intro x hx
    apply A.finite_vertexSet.mem_toFinset.mpr
    exact hV (face_subset_vertexSet ((K.mem_faceFinset_iff s).mp hs) hx)
  obtain ⟨F, hF, hmax⟩ := candidates.exists_max_image Finset.card ⟨A.faceFinset, hmem A (Subset.rfl) (Subset.rfl)⟩
  obtain ⟨K, rfl, hAK, hKV⟩ := (Finset.mem_filter.mp hF).2
  refine ⟨K, hAK, hKV.antisymm (fun _ hx => hAK hx), ?_⟩
  intro L hKL hLV
  have hle := hmax L.faceFinset (hmem L (hAK.trans hKL) hLV)
  have hsub : K.faceFinset ⊆ L.faceFinset := fun s hs =>
    (L.mem_faceFinset_iff s).mpr (hKL ((K.mem_faceFinset_iff s).mp hs))
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  ext s
  rw [← L.mem_faceFinset_iff, ← K.mem_faceFinset_iff, heq]

/-- A nonempty simplex can be added once its proper faces are present
and its intersections with the existing simplices are common faces. -/
def adjoinFace (K : FinitePlanarComplex) (s : Finset PLPoint) (hs : s.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : s → PLPoint))
    (hproper : ∀ t ⊂ s, t.Nonempty → t ∈ K.simplices.faces)
    (hglue : ∀ t ∈ K.simplices.faces,
      convexHull ℝ (s : Set PLPoint) ∩ convexHull ℝ (t : Set PLPoint) ⊆
        convexHull ℝ ((s : Set PLPoint) ∩ (t : Set PLPoint))) : FinitePlanarComplex := by
  classical
  refine ⟨⟨⟨insert s K.simplices.faces, ?_⟩, ?_, ?_⟩, K.finite_faces.insert s⟩
  · rintro t (rfl | ht)
    · refine ⟨hs, fun u hu hne => ?_⟩
      by_cases he : u = t
      · exact Or.inl he
      · exact Or.inr (hproper u (ssubset_of_subset_of_ne hu he) hne)
    · exact ⟨K.simplices.nonempty_of_mem_faces ht,
        fun u hu hne => Or.inr (K.simplices.down_closed ht hu hne)⟩
  · rintro t (rfl | ht)
    · exact hind
    · exact K.simplices.indep ht
  · rintro t u (rfl | ht) (rfl | hu)
    · simp
    · exact hglue u hu
    · simpa only [Set.inter_comm] using hglue t ht
    · exact K.simplices.inter_subset_convexHull ht hu

/-- A hull triangulation containing the original complex directly gives a
compatible refinement. Its target coefficients are those of the original complex. -/
def CompatibleHullRefinement.of_extension {A K : FinitePlanarComplex}
    (hAK : A.simplices.faces ⊆ K.simplices.faces)
    (hHull : K.realization = convexHull ℝ A.realization) : CompatibleHullRefinement A where
  hull := K
  target := A
  target_faces_subset := hAK
  hull_realization := hHull
  target_realization := rfl
  target_twiceV1 := rfl
  target_eulerChar := rfl

private theorem exists_affine_coordinate_of_collinear {V : Set PLPoint} (hV : Collinear ℝ V) :
    ∃ f : ℝ →ᵃ[ℝ] PLPoint, Function.Injective f ∧ V ⊆ range f := by
  obtain ⟨a, d, hd⟩ := (collinear_iff_exists_forall_eq_smul_vadd V).mp hV
  by_cases hzero : d = 0
  · obtain ⟨b, hb⟩ := exists_ne a
    refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_injective ℝ hb.symm, fun p hp => ?_⟩
    obtain ⟨t, ht⟩ := hd p hp
    use 0
    simpa [hzero] using ht.symm
  · have hab : a ≠ d + a := by
      intro h
      exact hzero (add_right_cancel (show d + a = 0 + a by simpa only [zero_add] using h.symm))
    refine ⟨AffineMap.lineMap a (d + a), AffineMap.lineMap_injective ℝ hab, fun p hp => ?_⟩
    obtain ⟨t, ht⟩ := hd p hp
    exact ⟨t, by simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_right, vadd_eq_add] using ht.symm⟩

private theorem convexHull_finite_collinear_eq_image_Icc {f : ℝ →ᵃ[ℝ] PLPoint}
    (hf : Function.Injective f) {S : Set PLPoint} (hRange : S ⊆ range f) (hS : S.Finite)
    (hne : S.Nonempty) : ∃ a b, f a ∈ S ∧ f b ∈ S ∧ a ≤ b ∧ convexHull ℝ S = f '' Icc a b := by
  let U := f ⁻¹' S
  have hU : U.Finite := hS.preimage hf.injOn
  have hneU : U.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨t, rfl⟩ := hRange hx
    exact ⟨t, hx⟩
  obtain ⟨a, ha, hMin⟩ := U.exists_min_image id hU hneU
  obtain ⟨b, hb, hMax⟩ := U.exists_max_image id hU hneU
  have hab : a ≤ b := hMin b hb
  refine ⟨a, b, ha, hb, hab, ?_⟩
  have hHull : convexHull ℝ U = Icc a b := by
    apply Subset.antisymm
    · exact convexHull_min (fun t ht => ⟨hMin t ht, hMax t ht⟩) (convex_Icc a b)
    · rw [← segment_eq_Icc hab]
      exact (convex_convexHull ℝ U).segment_subset (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb)
  rw [← hHull, f.image_convexHull, image_preimage_eq_of_subset hRange]

private theorem pair_face_mem_of_no_interior_vertices {K : FinitePlanarComplex}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    {f : ℝ →ᵃ[ℝ] PLPoint} (hf : Function.Injective f)
    (hSection : ∀ t ∈ K.simplices.faces, convexHull ℝ (t : Set PLPoint) ∩ range f ⊆
      convexHull ℝ ((t : Set PLPoint) ∩ range f))
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (ha : f a ∈ K.simplices.vertices)
    (hb : f b ∈ K.simplices.vertices) (hgap : ∀ t ∈ Ioo a b, f t ∉ K.simplices.vertices)
    (hc : f c ∉ K.realization) : ({f a, f b} : Finset PLPoint) ∈ K.simplices.faces := by
  classical
  let s : Finset PLPoint := {f a, f b}
  have hne : f a ≠ f b := hf.ne (hac.trans hcb).ne
  have hind : AffineIndependent ℝ ((↑) : s → PLPoint) := by
    have hrange : range (![f a, f b] : Fin 2 → PLPoint) = (s : Set PLPoint) := by
      simp [s, Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    change AffineIndependent ℝ (fun x : ↥(s : Set PLPoint) => x.val)
    rw [← hrange]
    exact (affineIndependent_of_ne ℝ hne).range
  have hproper (t : Finset PLPoint) (ht : t ⊂ s) (hne' : t.Nonempty) : t ∈ K.simplices.faces := by
    have hcard : t.card < 2 := by simpa [s, Finset.card_pair hne] using Finset.card_lt_card ht
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by have := Finset.card_pos.mpr hne'; omega)
    have hu : u ∈ s := (ssubset_iff_subset_ne.mp ht).1 (Finset.mem_singleton_self u)
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ha
    · rw [Finset.mem_singleton.mp hu]
      exact hb
  have hglue (t : Finset PLPoint) (ht : t ∈ K.simplices.faces) :
      convexHull ℝ (s : Set PLPoint) ∩ convexHull ℝ (t : Set PLPoint) ⊆
        convexHull ℝ ((s : Set PLPoint) ∩ (t : Set PLPoint)) := by
    have htV := face_subset_vertexSet ht
    have hsHull : convexHull ℝ (s : Set PLPoint) = f '' Icc a b := by
      rw [← segment_eq_Icc (hac.trans hcb).le, image_segment]
      simp [s, convexHull_pair]
    rintro x ⟨hxs, hxt⟩
    rw [hsHull] at hxs
    obtain ⟨d, hd, rfl⟩ := hxs
    have hxSlice := hSection t ht ⟨hxt, mem_range_self d⟩
    have hneSlice := convexHull_nonempty_iff.mp
      (show (convexHull ℝ ((t : Set PLPoint) ∩ range f)).Nonempty from ⟨f d, hxSlice⟩)
    obtain ⟨l, u, hl, hu, _, hHull⟩ := convexHull_finite_collinear_eq_image_Icc hf
      inter_subset_right (t.finite_toSet.inter_of_left _) hneSlice
    have hdu : d ∈ Icc l u := by
      rw [hHull] at hxSlice
      obtain ⟨e, he, heq⟩ := hxSlice
      rwa [hf heq] at he
    rcases eq_or_lt_of_le hd.1 with hda | hda
    · exact subset_convexHull ℝ _ ⟨by simp [s, ← hda], (K.simplices.vertex_mem_convexHull_iff (hda ▸ ha) ht).mp hxt⟩
    rcases eq_or_lt_of_le hd.2 with hdb | hdb
    · exact subset_convexHull ℝ _ ⟨by simp [s, hdb], (K.simplices.vertex_mem_convexHull_iff (hdb.symm ▸ hb) ht).mp hxt⟩
    have hla : l ≤ a := le_of_not_gt fun h => hgap l ⟨h, hdu.1.trans_lt hdb⟩ (htV hl.1)
    have hbu : b ≤ u := le_of_not_gt fun h => hgap u ⟨hda.trans_le hdu.2, h⟩ (htV hu.1)
    have hcSlice : f c ∈ convexHull ℝ ((t : Set PLPoint) ∩ range f) := by
      rw [hHull]
      exact ⟨c, ⟨hla.trans hac.le, hcb.le.trans hbu⟩, rfl⟩
    exact (hc (K.convexHull_face_subset_realization t ht (convexHull_mono inter_subset_left hcSlice))).elim
  let L := K.adjoinFace s (Finset.insert_nonempty _ _) hind hproper hglue
  have hKL : K.simplices.faces ⊆ L.simplices.faces := fun _ ht => Or.inr ht
  have hLV : L.simplices.vertices ⊆ K.simplices.vertices := by
    intro x hx
    change ({x} : Finset PLPoint) ∈ insert s K.simplices.faces at hx
    rcases hx with heq | hx
    · have hcard := congrArg Finset.card heq
      simp [s, Finset.card_pair hne] at hcard
    · exact hx
  exact (hmax L hKL hLV) ▸ (show s ∈ L.simplices.faces from Or.inl rfl)

/-- A maximal extension fills the interval between its extreme vertices on
a line if each simplex meets the line in the hull of its vertices there. -/
theorem convexHull_vertices_inter_line_subset_of_maximal {K : FinitePlanarComplex}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    {f : ℝ →ᵃ[ℝ] PLPoint} (hf : Function.Injective f)
    (hSection : ∀ t ∈ K.simplices.faces, convexHull ℝ (t : Set PLPoint) ∩ range f ⊆
      convexHull ℝ ((t : Set PLPoint) ∩ range f)) :
    convexHull ℝ (K.simplices.vertices ∩ range f) ⊆ K.realization := by
  intro x hx
  by_contra hNot
  have hne := convexHull_nonempty_iff.mp (show (convexHull ℝ (K.simplices.vertices ∩ range f)).Nonempty from ⟨x, hx⟩)
  obtain ⟨l, u, hl, hu, _, hHull⟩ := convexHull_finite_collinear_eq_image_Icc hf
    inter_subset_right (K.finite_vertexSet.inter_of_left _) hne
  rw [hHull] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  let U := f ⁻¹' K.simplices.vertices
  have hU : U.Finite := K.finite_vertexSet.preimage hf.injOn
  obtain ⟨a, ha, hMax⟩ := (U ∩ Iic c).exists_max_image id (hU.inter_of_left _) ⟨l, hl.1, hc.1⟩
  obtain ⟨b, hb, hMin⟩ := (U ∩ Ici c).exists_min_image id (hU.inter_of_left _) ⟨u, hu.1, hc.2⟩
  have hNotV : f c ∉ K.simplices.vertices := fun h => hNot (K.simplices.vertices_subset_space h)
  have hac : a < c := lt_of_le_of_ne ha.2 fun h => hNotV (h ▸ ha.1)
  have hcb : c < b := lt_of_le_of_ne hb.2 fun h => hNotV (h.symm ▸ hb.1)
  have hgap (t : ℝ) (ht : t ∈ Ioo a b) : f t ∉ K.simplices.vertices := by
    intro hv
    rcases le_total t c with htc | hct
    · exact ht.1.not_ge (hMax t ⟨hv, htc⟩)
    · exact ht.2.not_ge (hMin t ⟨hv, hct⟩)
  have he := pair_face_mem_of_no_interior_vertices hmax hf hSection hac hcb ha.1 hb.1 hgap hNot
  apply hNot (K.convexHull_face_subset_realization _ he ?_)
  simpa [convexHull_pair, ← image_segment, segment_eq_Icc (hac.trans hcb).le] using
    (show f c ∈ f '' Icc a b from ⟨c, ⟨hac.le, hcb.le⟩, rfl⟩)

/-- Collinear complexes admit a hull triangulation on exactly their original
vertices, by adjoining the segments between consecutive vertices. -/
theorem exists_hull_extension_of_collinear (A : FinitePlanarComplex)
    (hcol : Collinear ℝ A.simplices.vertices) :
    ∃ K : FinitePlanarComplex, A.simplices.faces ⊆ K.simplices.faces ∧
      K.simplices.vertices = A.simplices.vertices ∧ K.realization = convexHull ℝ A.realization := by
  obtain ⟨K, hAK, hV, hmax⟩ := A.exists_maximal_vertex_extension
  refine ⟨K, hAK, hV, ?_⟩
  rw [A.convexHull_realization_eq_convexHull_vertices, ← hV]
  apply Subset.antisymm
  · rw [← K.convexHull_realization_eq_convexHull_vertices]
    exact subset_convexHull ℝ _
  obtain ⟨f, hf, hRange⟩ := exists_affine_coordinate_of_collinear (hV.symm ▸ hcol)
  rw [← inter_eq_left.mpr hRange]
  apply convexHull_vertices_inter_line_subset_of_maximal (fun L hKL hLV => hmax L hKL (hLV.trans hV.subset)) hf
  intro t ht
  rw [inter_eq_left.mpr ((face_subset_vertexSet ht).trans hRange)]
  exact inter_subset_left

/-- The compatible hull refinement is available for every collinear input. -/
theorem nonempty_compatibleHullRefinement_of_collinear (A : FinitePlanarComplex)
    (hcol : Collinear ℝ A.simplices.vertices) : Nonempty (CompatibleHullRefinement A) := by
  obtain ⟨K, hAK, _, hHull⟩ := A.exists_hull_extension_of_collinear hcol
  exact ⟨CompatibleHullRefinement.of_extension hAK hHull⟩

/-- A supporting level meets a finite convex hull in the hull of the points on that level. -/
theorem convexHull_finset_inter_level {s : Finset PLPoint} {g : PLPoint →ₗ[ℝ] ℝ} {b : ℝ}
    (hbound : ∀ p ∈ s, g p ≤ b) :
    convexHull ℝ (s : Set PLPoint) ∩ {p | g p = b} ⊆
      convexHull ℝ ((s : Set PLPoint) ∩ {p | g p = b}) := by
  classical
  intro x hx
  obtain ⟨w, hw, hSum, hPoint⟩ := Finset.mem_convexHull'.mp hx.1
  have hSumg : ∑ p ∈ s, w p * g p = b := by
    calc
      _ = g (∑ p ∈ s, w p • p) := by simp [map_sum]
      _ = b := hPoint ▸ hx.2
  have hGap : ∑ p ∈ s, w p * (b - g p) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum, hSumg, one_mul, sub_self]
  have hNonneg (p : PLPoint) (hp : p ∈ s) : 0 ≤ w p * (b - g p) :=
    mul_nonneg (hw p hp) (sub_nonneg.mpr (hbound p hp))
  have hZero (p : PLPoint) (hp : p ∈ s) (h : g p ≠ b) : w p = 0 := by
    have hle := Finset.single_le_sum (f := fun p => w p * (b - g p)) (fun p hp => hNonneg p hp) hp
    rw [hGap] at hle
    exact (mul_eq_zero.mp (le_antisymm hle (hNonneg p hp))).resolve_right (sub_ne_zero.mpr h.symm)
  let t := s.filter fun p => g p = b
  have hSet : (t : Set PLPoint) = (s : Set PLPoint) ∩ {p | g p = b} := by
    ext p
    simp [t]
  rw [← hSet, Finset.mem_convexHull']
  have ht := Finset.filter_subset (fun p => g p = b) s
  have hZero' (p : PLPoint) (hp : p ∈ s) (hn : p ∉ t) : w p = 0 :=
    hZero p hp fun he => hn (Finset.mem_filter.mpr ⟨hp, he⟩)
  refine ⟨w, fun p hp => hw p (ht hp), ?_, ?_⟩
  · rwa [Finset.sum_subset ht hZero']
  · rwa [Finset.sum_subset ht (fun p hp hn => by rw [hZero' p hp hn, zero_smul])]

private theorem exists_affine_coordinate_level {g : PLPoint →ₗ[ℝ] ℝ} (hg : g ≠ 0) (x : PLPoint) :
    ∃ f : ℝ →ᵃ[ℝ] PLPoint, Function.Injective f ∧ range f = {y | g y = g x} := by
  have hrange : g.range ≠ ⊥ := fun h => hg (LinearMap.range_eq_bot.mp h)
  have hRpos : 0 < Module.finrank ℝ g.range :=
    (Module.finrank_pos_iff_of_free ℝ g.range).mpr (Submodule.nontrivial_iff_ne_bot.mpr hrange)
  have hRle : Module.finrank ℝ g.range ≤ 1 := by simpa using Submodule.finrank_le g.range
  have hRK := g.finrank_range_add_finrank_ker
  rw [finrank_euclideanSpace_fin] at hRK
  have hK : Module.finrank ℝ g.ker = 1 := by omega
  obtain ⟨d, hd, hSpan⟩ := finrank_eq_one_iff'.mp hK
  have hd' : (d : PLPoint) ≠ 0 := fun h => hd (Subtype.ext h)
  have hxne : x ≠ (d : PLPoint) + x := by
    intro h
    exact hd' (add_right_cancel (show (d : PLPoint) + x = 0 + x by simpa only [zero_add] using h.symm))
  refine ⟨AffineMap.lineMap x ((d : PLPoint) + x), AffineMap.lineMap_injective ℝ hxne, ?_⟩
  ext y
  simp only [Set.mem_range, AffineMap.lineMap_apply_module', add_sub_cancel_right, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp [LinearMap.mem_ker.mp d.property]
  · intro hy
    have hdiff : y - x ∈ g.ker := LinearMap.mem_ker.mpr (by rw [map_sub, hy, sub_self])
    obtain ⟨t, ht⟩ := hSpan ⟨y - x, hdiff⟩
    exact ⟨t, by rw [show t • (d : PLPoint) = y - x from congrArg Subtype.val ht, sub_add_cancel]⟩

/-- A maximal extension contains every point on the supporting boundary of
its full-dimensional convex hull. -/
theorem frontier_convexHull_vertices_subset_of_maximal {K : FinitePlanarComplex}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    (hInt : (interior (convexHull ℝ K.simplices.vertices)).Nonempty) :
    frontier (convexHull ℝ K.simplices.vertices) ⊆ K.realization := by
  intro x hx
  obtain ⟨g, hg, hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ K.simplices.vertices) hx.2 hInt
  have hg' : g.toLinearMap ≠ 0 := fun h => hg (ContinuousLinearMap.ext fun y => LinearMap.congr_fun h y)
  obtain ⟨f, hf, hLevel⟩ := exists_affine_coordinate_level hg' x
  have hClip (t : Finset PLPoint) (ht : (t : Set PLPoint) ⊆ K.simplices.vertices) :
      convexHull ℝ (t : Set PLPoint) ∩ range f ⊆ convexHull ℝ ((t : Set PLPoint) ∩ range f) := by
    rw [hLevel]
    exact convexHull_finset_inter_level fun y hy => hbound y (subset_convexHull ℝ _ (ht hy))
  have hFill := convexHull_vertices_inter_line_subset_of_maximal hmax hf
    (fun t ht => hClip t (face_subset_vertexSet ht))
  let V := K.finite_vertexSet.toFinset
  have hV : (V : Set PLPoint) = K.simplices.vertices := K.finite_vertexSet.coe_toFinset
  have hxHull : x ∈ convexHull ℝ K.simplices.vertices := by
    simpa only [← hV, (V.finite_toSet.isClosed_convexHull ℝ).closure_eq] using frontier_subset_closure hx
  apply hFill
  rw [← hV]
  apply hClip V hV.subset
  exact ⟨hV.symm ▸ hxHull, hLevel.symm ▸ (show g.toLinearMap x = g.toLinearMap x from rfl)⟩

end FinitePlanarComplex
