import SteinerProof.HullSector

/-! Filling the consecutive sector of a hull gap by adjoining simplices. -/

open Set Filter
open scoped Topology

noncomputable section

namespace FinitePlanarComplex

private def sectorCoord (B : Module.Basis (Fin 2) ℝ PLPoint) (v : PLPoint) (i : Fin 2) : PLPoint →ᵃ[ℝ] ℝ :=
  (B.coord i).toAffineMap.comp (AffineMap.id ℝ PLPoint - AffineMap.const ℝ PLPoint v)

private theorem affine_real_lineMap (f : PLPoint →ᵃ[ℝ] ℝ) (x y : PLPoint) (t : ℝ) :
    f (AffineMap.lineMap x y t) = (1 - t) * f x + t * f y := by
  rw [f.apply_lineMap, AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]

private theorem exists_point_on_supporting_side {f₀ f₁ : PLPoint →ᵃ[ℝ] ℝ} {p q : PLPoint}
    (hp₀ : 0 < f₀ p) (hp₁ : 0 < f₁ p) (hp : f₀ p + f₁ p = 1) (hq : f₀ q + f₁ q < 1) :
    ∃ z ∈ segment ℝ p q, 0 < f₀ z ∧ 0 < f₁ z ∧ f₀ z + f₁ z < 1 := by
  let γ : ℝ → PLPoint := AffineMap.lineMap p q
  have hγ : Continuous γ := by dsimp only [γ]; exact AffineMap.continuous_of_finiteDimensional _
  have hn (f : PLPoint →ᵃ[ℝ] ℝ) (hf : 0 < f p) : {t | 0 < f (γ t)} ∈ 𝓝 (0 : ℝ) := by
    have ho : IsOpen {t | 0 < f (γ t)} := isOpen_lt continuous_const (f.continuous_of_finiteDimensional.comp hγ)
    exact ho.mem_nhds (by simpa [γ] using hf)
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 1) := by rw [closure_Ioo zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨t, ⟨ht₀, ht₁⟩, ht⟩ := mem_closure_iff_nhds.mp hcl _ (inter_mem (hn f₀ hp₀) (hn f₁ hp₁))
  refine ⟨γ t, lineMap_mem_segment ℝ _ _ ⟨ht.1.le, ht.2.le⟩, ht₀, ht₁, ?_⟩
  rw [show γ t = AffineMap.lineMap p q t from rfl, affine_real_lineMap, affine_real_lineMap]
  have heq : (1 - t) * f₀ p + t * f₀ q + ((1 - t) * f₁ p + t * f₁ q) =
      1 + t * (f₀ q + f₁ q - 1) := by linear_combination (1 - t) * hp
  rw [heq]
  linarith only [mul_neg_of_pos_of_neg ht.1 (sub_neg.mpr hq)]

private theorem opposite_vertices_mem_face {K : FinitePlanarComplex} {v u w p : PLPoint}
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges)
    (hc : SteinerProof.ConsecutiveIncident K v u w) (hTri : ({v,u,w} : Finset PLPoint) ∉ K.simplices.faces)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    (hNoLow : ∀ y ∈ K.simplices.vertices, 0 < B.repr (y-v) 0 → 0 < B.repr (y-v) 1 →
      1 < B.repr (y-v) 0 + B.repr (y-v) 1)
    {s : Finset PLPoint} (hs : s ∈ K.simplices.faces) (hp : p ∈ openSegment ℝ u w)
    (hpS : p ∈ convexHull ℝ (s : Set PLPoint)) : u ∈ s ∧ w ∈ s := by
  classical
  let f := sectorCoord B v
  have hf (y : PLPoint) (i : Fin 2) : f i y = B.repr (y-v) i := rfl
  have hu₀ : f 0 u = 1 := by rw [hf, ← hB₀, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hu₁ : f 1 u = 0 := by rw [hf, ← hB₀, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]
  have hw₀ : f 0 w = 0 := by rw [hf, ← hB₁, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]
  have hw₁ : f 1 w = 1 := by rw [hf, ← hB₁, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hpF : 0 < f 0 p ∧ 0 < f 1 p ∧ f 0 p + f 1 p = 1 := by
    rw [openSegment_eq_image_lineMap] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [affine_real_lineMap, affine_real_lineMap, hu₀, hu₁, hw₀, hw₁]
    simp only [mul_one, mul_zero, add_zero, zero_add, sub_add_cancel, and_true]
    exact ⟨sub_pos.mpr ht.2, ht.1⟩
  have hUpper (y : PLPoint) (hy : y ∈ s) : 1 ≤ f 0 y + f 1 y := by
    by_contra! h
    obtain ⟨z, hz, hz₀, hz₁, hzLt⟩ := exists_point_on_supporting_side hpF.1 hpF.2.1 hpF.2.2 h
    have hzK := K.convexHull_face_subset_realization s hs
      ((convex_convexHull ℝ _).segment_subset hpS (subset_convexHull ℝ _ hy) hz)
    exact notMem_realization_of_positive_coordinates_lt_vertex_height hu hw hc hTri B hB₀ hB₁ le_rfl
      (fun x hx h₀ h₁ => (hNoLow x hx h₀ h₁).le) hz₀ hz₁ hzLt hzK
  let G : PLPoint →ₗ[ℝ] ℝ := -(B.coord 0 + B.coord 1)
  have hG (y : PLPoint) : G y = G v - (f 0 y + f 1 y) := by
    change -(B.coord 0 y + B.coord 1 y) =
      -(B.coord 0 v + B.coord 1 v) - (B.coord 0 (y-v) + B.coord 1 (y-v))
    rw [map_sub, map_sub]
    ring
  let t := s.filter (fun y => f 0 y + f 1 y = 1)
  have ht : (t : Set PLPoint) = (s : Set PLPoint) ∩ {y | G y = G v - 1} := by
    ext y
    simp only [t, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hG y]
    exact and_congr_right fun _ => ⟨fun h => by rw [h], fun h => by linarith only [h]⟩
  have hpT : p ∈ convexHull ℝ (t : Set PLPoint) := by
    rw [ht]
    apply convexHull_finset_inter_level (fun y hy => by rw [hG]; exact sub_le_sub_left (hUpper y hy) _)
    exact ⟨hpS, by change G p = G v - 1; rw [hG, hpF.2.2]⟩
  have hEndpoint (i : Fin 2) (q : PLPoint) (hqV : q ∈ K.simplices.vertices)
      (hq₀ : f i q = 0) (hqH : f 0 q + f 1 q = 1) : q ∈ s := by
    obtain ⟨y, hy, hyLe⟩ := exists_le_face_vertex_of_mem_convexHull (f i) hpT
    have hyS := Finset.mem_filter.mp hy
    have hpI : 0 < f i p ∧ f i p < 1 := by
      fin_cases i
      · exact ⟨hpF.1, by change f 0 p < 1; linarith only [hpF.2.1, hpF.2.2]⟩
      · exact ⟨hpF.2.1, by change f 1 p < 1; linarith only [hpF.1, hpF.2.2]⟩
    have hy₀ : f i y ≤ 0 := by
      by_contra! hypos
      have hylt := hyLe.trans_lt hpI.2
      have hyV : y ∈ K.simplices.vertices := K.simplices.down_closed hs
        (Finset.singleton_subset_iff.mpr hyS.1) (by simp)
      have hBoth : 0 < f 0 y ∧ 0 < f 1 y := by
        fin_cases i
        · change f 0 y < 1 at hylt
          exact ⟨hypos, by linarith only [hylt, hyS.2]⟩
        · change f 1 y < 1 at hylt
          exact ⟨by linarith only [hylt, hyS.2], hypos⟩
      exact (ne_of_gt (hNoLow y hyV hBoth.1 hBoth.2)) hyS.2
    let a := f i p / (f i p - f i y)
    have hDen : 0 < f i p - f i y := sub_pos.mpr (hy₀.trans_lt hpI.1)
    have ha : a ∈ Icc (0 : ℝ) 1 := ⟨(div_pos hpI.1 hDen).le, (div_le_one hDen).mpr (by linarith)⟩
    let z := AffineMap.lineMap p y a
    have hz₀ : f i z = 0 := by
      rw [show z = AffineMap.lineMap p y a from rfl, affine_real_lineMap]
      have hCancel : a * (f i p - f i y) = f i p := div_mul_cancel₀ _ hDen.ne'
      nlinarith only [hCancel]
    have hzH : f 0 z + f 1 z = 1 := by
      rw [show z = AffineMap.lineMap p y a from rfl, affine_real_lineMap, affine_real_lineMap]
      linear_combination (1 - a) * hpF.2.2 + a * hyS.2
    have hzero : f 0 z = f 0 q := by
      fin_cases i
      · exact hz₀.trans hq₀.symm
      · change f 1 z = 0 at hz₀
        change f 1 q = 0 at hq₀
        linarith only [hz₀, hq₀, hzH, hqH]
    have hone : f 1 z = f 1 q := by linarith only [hzero, hzH, hqH]
    have hsub : z - v = q - v := by
      apply B.repr.injective
      ext j
      rw [← hf, ← hf]
      fin_cases j
      · exact hzero
      · exact hone
    have heq : z = q := sub_left_inj.mp hsub
    have hzS : z ∈ convexHull ℝ (s : Set PLPoint) := (convex_convexHull ℝ _).segment_subset hpS
      (subset_convexHull ℝ _ hyS.1) (lineMap_mem_segment ℝ p y ha)
    exact (K.simplices.vertex_mem_convexHull_iff hqV hs).mp (heq ▸ hzS)
  have hVertex {z : PLPoint} (he : ({v,z} : Finset PLPoint) ∈ K.edges) : z ∈ K.simplices.vertices :=
    K.simplices.down_closed ((K.mem_edges_iff _).mp he).1 (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
  exact ⟨hEndpoint 1 u (hVertex hu) hu₁ (by rw [hu₀, hu₁, add_zero]),
    hEndpoint 0 w (hVertex hw) hw₀ (by rw [hw₀, hw₁, zero_add])⟩

private theorem opposite_face_mem_of_maximal {K : FinitePlanarComplex} {v u w : PLPoint}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    (hu : ({v,u} : Finset PLPoint) ∈ K.edges) (hw : ({v,w} : Finset PLPoint) ∈ K.edges) (huw : u ≠ w)
    (hc : SteinerProof.ConsecutiveIncident K v u w) (hTri : ({v,u,w} : Finset PLPoint) ∉ K.simplices.faces)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    (hNoLow : ∀ y ∈ K.simplices.vertices, 0 < B.repr (y-v) 0 → 0 < B.repr (y-v) 1 →
      1 < B.repr (y-v) 0 + B.repr (y-v) 1) : ({u,w} : Finset PLPoint) ∈ K.simplices.faces := by
  classical
  by_contra h
  have hVertex {z : PLPoint} (he : ({v,z} : Finset PLPoint) ∈ K.edges) : z ∈ K.simplices.vertices :=
    K.simplices.down_closed ((K.mem_edges_iff _).mp he).1 (Finset.singleton_subset_iff.mpr (by simp)) (by simp)
  apply not_empty_openSegment_of_maximal hmax (hVertex hu) (hVertex hw) huw
  intro p hp hpK
  obtain ⟨s, hs, hpS⟩ := (K.mem_realization_iff _).mp hpK
  obtain ⟨huS, hwS⟩ := opposite_vertices_mem_face hu hw hc hTri B hB₀ hB₁ hNoLow hs hp hpS
  exact h (K.simplices.down_closed hs (Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hwS⟩)
    (Finset.insert_nonempty _ _))

private theorem triangle_mem_faces_of_covered_edges {K : FinitePlanarComplex} {v u w : PLPoint}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    (hVU : ({v,u} : Finset PLPoint) ∈ K.simplices.faces) (hVW : ({v,w} : Finset PLPoint) ∈ K.simplices.faces)
    (hUW : ({u,w} : Finset PLPoint) ∈ K.simplices.faces)
    (B : Module.Basis (Fin 2) ℝ PLPoint) (hB₀ : B 0 = u-v) (hB₁ : B 1 = w-v)
    (hHole : ∀ x : PLPoint, 0 < B.repr (x-v) 0 → 0 < B.repr (x-v) 1 →
      B.repr (x-v) 0 + B.repr (x-v) 1 < 1 → x ∉ K.realization) :
    ({v,u,w} : Finset PLPoint) ∈ K.simplices.faces := by
  classical
  let s : Finset PLPoint := {v,u,w}
  have hCard : s.card = 3 := by simp [s, hvu, hvw, Finset.card_pair huw]
  have hSpan : vectorSpan ℝ (s : Set PLPoint) = ⊤ := by
    apply top_unique
    rw [← B.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change B 0 ∈ vectorSpan ℝ (s : Set PLPoint)
      rw [hB₀]
      exact vsub_mem_vectorSpan ℝ (by simp [s]) (by simp [s])
    · change B 1 ∈ vectorSpan ℝ (s : Set PLPoint)
      rw [hB₁]
      exact vsub_mem_vectorSpan ℝ (by simp [s]) (by simp [s])
  have hInd : AffineIndependent ℝ ((↑) : s → PLPoint) := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (n := 2) (by simpa using hCard)).mpr
    rw [show range ((↑) : s → PLPoint) = (s : Set PLPoint) from by ext x; simp, hSpan]
    simp
  have hProper (t : Finset PLPoint) (ht : t ⊂ s) (hne : t.Nonempty) : t ∈ K.simplices.faces := by
    obtain ⟨p, hp, hpt⟩ := Finset.exists_of_ssubset ht
    have hSub : t ⊆ s.erase p := fun x hx => Finset.mem_erase.mpr
      ⟨fun h => hpt (h ▸ hx), (ssubset_iff_subset_ne.mp ht).1 hx⟩
    apply K.simplices.down_closed ?_ hSub hne
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa [s, hvu, hvw, ne_comm] using hUW
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have hErase : s.erase p = {v,w} := by
        ext y
        simp only [s, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h, rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact (h rfl).elim
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨hvu, Or.inl rfl⟩
          · exact ⟨huw.symm, Or.inr (Or.inr rfl)⟩
      rwa [hErase]
    · have hpw := Finset.mem_singleton.mp hp
      subst p
      have hErase : s.erase w = {v,u} := by
        ext y
        simp only [s, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h, rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact (h rfl).elim
        · rintro (rfl | rfl)
          · exact ⟨hvw, Or.inl rfl⟩
          · exact ⟨huw, Or.inr (Or.inl rfl)⟩
      rwa [hErase]
  let f := sectorCoord B v
  have hf (x : PLPoint) (i : Fin 2) : f i x = B.repr (x-v) i := rfl
  have hvF (i : Fin 2) : f i v = 0 := by rw [hf, sub_self, map_zero, Finsupp.zero_apply]
  have hu₀ : f 0 u = 1 := by rw [hf, ← hB₀, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hu₁ : f 1 u = 0 := by rw [hf, ← hB₀, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]
  have hw₀ : f 0 w = 0 := by rw [hf, ← hB₁, Module.Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]
  have hw₁ : f 1 w = 1 := by rw [hf, ← hB₁, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hInject {x y : PLPoint} (h₀ : f 0 x = f 0 y) (h₁ : f 1 x = f 1 y) : x = y := by
    apply sub_left_inj.mp
    apply B.repr.injective
    ext i
    rw [← hf, ← hf]
    fin_cases i
    · exact h₀
    · exact h₁
  have hGlue (t : Finset PLPoint) (ht : t ∈ K.simplices.faces) :
      convexHull ℝ (s : Set PLPoint) ∩ convexHull ℝ (t : Set PLPoint) ⊆
        convexHull ℝ ((s : Set PLPoint) ∩ (t : Set PLPoint)) := by
    rintro x ⟨hxS, hxT⟩
    have hxK := K.convexHull_face_subset_realization t ht hxT
    have hNonneg (i : Fin 2) : 0 ≤ f i x := by
      apply convexHull_min ?_ ((convex_Ici 0).affine_preimage (f i)) hxS
      intro y hy
      change 0 ≤ f i y
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · rw [hvF]
      · fin_cases i
        · exact hu₀ ▸ zero_le_one
        · exact hu₁ ▸ le_rfl
      · fin_cases i
        · exact hw₀ ▸ le_rfl
        · exact hw₁ ▸ zero_le_one
    have hHeight : f 0 x + f 1 x ≤ 1 := by
      apply convexHull_min ?_ ((convex_Iic 1).affine_preimage (f 0 + f 1)) hxS
      intro y hy
      change f 0 y + f 1 y ≤ 1
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · rw [hvF, hvF, add_zero]
        exact zero_le_one
      · rw [hu₀, hu₁, add_zero]
      · rw [hw₀, hw₁, zero_add]
    have hLine {a b : PLPoint} {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1)
        (h₀ : (1-l)*f 0 a + l*f 0 b = f 0 x) (h₁ : (1-l)*f 1 a + l*f 1 b = f 1 x) :
        x ∈ convexHull ℝ (({a,b} : Finset PLPoint) : Set PLPoint) := by
      rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_image_lineMap]
      exact ⟨l, hl, hInject (by rw [affine_real_lineMap, h₀]) (by rw [affine_real_lineMap, h₁])⟩
    have hOn {e : Finset PLPoint} (he : e ∈ K.simplices.faces) (heS : e ⊆ s)
        (hxE : x ∈ convexHull ℝ (e : Set PLPoint)) : x ∈ convexHull ℝ ((s : Set PLPoint) ∩ (t : Set PLPoint)) := by
      have heT : (e : Set PLPoint) ∩ (t : Set PLPoint) ⊆ (s : Set PLPoint) ∩ (t : Set PLPoint) :=
        fun _ hz => ⟨heS hz.1, hz.2⟩
      exact convexHull_mono heT (K.simplices.inter_subset_convexHull he ht ⟨hxE,hxT⟩)
    rcases eq_or_lt_of_le (hNonneg 0) with h₀ | h₀
    · apply hOn hVW (by simp [s])
      apply hLine (l := f 1 x) ⟨hNonneg 1, by linarith only [h₀,hHeight]⟩
      · rw [hvF, hw₀, mul_zero, mul_zero, add_zero, h₀]
      · rw [hvF, hw₁, mul_zero, mul_one, zero_add]
    rcases eq_or_lt_of_le (hNonneg 1) with h₁ | h₁
    · apply hOn hVU (by simp [s])
      apply hLine (l := f 0 x) ⟨hNonneg 0, by linarith only [h₁,hHeight]⟩
      · rw [hvF, hu₀, mul_zero, mul_one, zero_add]
      · rw [hvF, hu₁, mul_zero, mul_zero, add_zero, h₁]
    rcases eq_or_lt_of_le hHeight with h | h
    · apply hOn hUW (by simp [s])
      apply hLine (l := f 1 x) ⟨hNonneg 1, by linarith only [h₀,h]⟩
      · rw [hu₀, hw₀, mul_one, mul_zero, add_zero]
        linarith only [h]
      · rw [hu₁, hw₁, mul_zero, mul_one, zero_add]
    · exact (hHole x h₀ h₁ h hxK).elim
  let L := K.adjoinFace s (Finset.insert_nonempty _ _) hInd hProper hGlue
  have hKL : K.simplices.faces ⊆ L.simplices.faces := fun _ hs => Or.inr hs
  have hLV : L.simplices.vertices ⊆ K.simplices.vertices := by
    intro p hp
    change ({p} : Finset PLPoint) ∈ insert s K.simplices.faces at hp
    rcases hp with heq | hp
    · have h := congrArg Finset.card heq
      simp [hCard] at h
    · exact hp
  exact (hmax L hKL hLV) ▸ (show s ∈ L.simplices.faces from Or.inl rfl)

/-- A finite planar complex maximal on its vertex set fills its convex hull. -/
theorem convexHull_vertices_subset_of_maximal {K : FinitePlanarComplex}
    (hmax : ∀ L : FinitePlanarComplex, K.simplices.faces ⊆ L.simplices.faces →
      L.simplices.vertices ⊆ K.simplices.vertices → L.simplices.faces = K.simplices.faces)
    (hInterior : (interior (convexHull ℝ K.simplices.vertices)).Nonempty) :
    convexHull ℝ K.simplices.vertices ⊆ K.realization := by
  by_contra hGap
  have hFrontier := frontier_convexHull_vertices_subset_of_maximal hmax hInterior
  obtain ⟨v,u,w,p,hu,hw,hInd,hc,hpNear,hpGap,c,d,hcPos,hdPos,hpVec⟩ :=
    exists_consecutive_edge_sector_of_hull_gap hFrontier hGap
  let B := basisOfLinearIndependentOfCardEqFinrank hInd (by simp)
  have hB : (B : Fin 2 → PLPoint) = ![u-v,w-v] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hB₀ : B 0 = u-v := congrFun hB 0
  have hB₁ : B 1 = w-v := congrFun hB 1
  have hvu := (K.edge_endpoints_ne hu).symm
  have hvw := (K.edge_endpoints_ne hw).symm
  have huw : u ≠ w := fun h => (by decide : (0 : Fin 2) ≠ 1) (B.injective (hB₀.trans (h ▸ hB₁.symm)))
  have hTri := triangle_notMem_faces_of_near_sector_gap hu hw hpGap.2 hpNear hcPos hdPos hpVec
  have hNoLow {y : PLPoint} := one_lt_height_of_sector_vertex_of_maximal (y := y) hmax hu hw hc hTri B hB₀ hB₁
  have hUW := opposite_face_mem_of_maximal hmax hu hw huw hc hTri B hB₀ hB₁ (fun _ => hNoLow)
  apply hTri
  apply triangle_mem_faces_of_covered_edges hmax hvu hvw huw ((K.mem_edges_iff _).mp hu).1
    ((K.mem_edges_iff _).mp hw).1 hUW B hB₀ hB₁
  intro x
  exact notMem_realization_of_positive_coordinates_lt_vertex_height (x := x) hu hw hc hTri B hB₀ hB₁ le_rfl
    (fun _ hy h₀ h₁ => (hNoLow hy h₀ h₁).le)

/-- A finite planar complex extends to a triangulation of its convex hull
on the same vertex set. Every original face is retained. -/
theorem exists_hull_extension (A : FinitePlanarComplex) :
    ∃ K : FinitePlanarComplex, A.simplices.faces ⊆ K.simplices.faces ∧
      K.simplices.vertices = A.simplices.vertices ∧ K.realization = convexHull ℝ A.realization := by
  by_cases hCollinear : Collinear ℝ A.simplices.vertices
  · exact A.exists_hull_extension_of_collinear hCollinear
  obtain ⟨K, hAK, hVertices, hmax⟩ := A.exists_maximal_vertex_extension
  have hCol : ¬ Collinear ℝ K.simplices.vertices := hVertices.symm ▸ hCollinear
  have hVerticesNonempty : K.simplices.vertices.Nonempty := by
    by_contra! h
    exact hCol (h.symm ▸ collinear_empty ℝ PLPoint)
  have hDim : Module.finrank ℝ (vectorSpan ℝ K.simplices.vertices) = 2 := by
    have hUpper := Submodule.finrank_le (vectorSpan ℝ K.simplices.vertices)
    rw [finrank_euclideanSpace_fin] at hUpper
    have hLower : 1 < Module.finrank ℝ (vectorSpan ℝ K.simplices.vertices) :=
      lt_of_not_ge fun h => hCol (collinear_iff_finrank_le_one.mpr h)
    omega
  have hSpan : vectorSpan ℝ K.simplices.vertices = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa only [finrank_euclideanSpace_fin] using hDim)
  have hAffine : affineSpan ℝ K.simplices.vertices = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      (hVerticesNonempty.mono (subset_affineSpan ℝ _))).mp
    rwa [direction_affineSpan]
  have hInterior : (interior (convexHull ℝ K.simplices.vertices)).Nonempty := by
    rw [(convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top, affineSpan_convexHull]
    exact hAffine
  refine ⟨K, hAK, hVertices, ?_⟩
  rw [A.convexHull_realization_eq_convexHull_vertices, ← hVertices]
  apply Subset.antisymm
  · rw [← K.convexHull_realization_eq_convexHull_vertices]
    exact subset_convexHull ℝ _
  · exact convexHull_vertices_subset_of_maximal (fun L hKL hLV => hmax L hKL (hLV.trans hVertices.subset)) hInterior

/-- The hull refinement required for the deletion induction exists for every
finite planar complex. Its target is the original complex itself. -/
theorem nonempty_compatibleHullRefinement (A : FinitePlanarComplex) : Nonempty (CompatibleHullRefinement A) := by
  obtain ⟨K, hAK, _, hHull⟩ := A.exists_hull_extension
  exact ⟨CompatibleHullRefinement.of_extension hAK hHull⟩

end FinitePlanarComplex
