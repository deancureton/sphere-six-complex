module

public import TauCeti.Analysis.Complex.Conformal.MonotoneExtension
import all TauCeti.Analysis.Complex.Conformal.MonotoneExtension
public import TauCeti.Analysis.Complex.Conformal.Biholomorph
import all TauCeti.Analysis.Complex.Conformal.Biholomorph

@[expose] public section

open Set Metric Topology Function Filter

noncomputable section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A set has **preconnected approach regions at `a`** if every neighbourhood of `a` contains a
smaller neighbourhood whose trace on the set is preconnected.  This is the exact local input in
the cluster-set continuum theorem. -/
def IsPreconnectedApproachAt (U : Set X) (a : X) : Prop :=
  ∀ s ∈ nhds a, ∃ t ∈ nhds a, t ⊆ s ∧ IsPreconnected (U ∩ t)

/-- Preconnected approach regions are preserved by an ambient homeomorphism. -/
theorem IsPreconnectedApproachAt.image_homeomorph {U : Set X} {a : X}
    (h : IsPreconnectedApproachAt U a) (e : X ≃ₜ Y) :
    IsPreconnectedApproachAt (e '' U) (e a) := by
  intro s hs
  have hs' : e ⁻¹' s ∈ nhds a := e.continuous.continuousAt.preimage_mem_nhds hs
  obtain ⟨t, ht, hts, htpre⟩ := h _ hs'
  have ht' : t ∈ nhds (e.symm (e a)) := by simpa using ht
  refine ⟨e.symm ⁻¹' t, e.symm.continuous.continuousAt.preimage_mem_nhds ht', ?_, ?_⟩
  · intro y hy
    have : e.symm y ∈ e ⁻¹' s := hts hy
    simpa using this
  · have himage : (e '' U) ∩ e.symm ⁻¹' t = e '' (U ∩ t) := by
      apply subset_antisymm
      · rintro y ⟨⟨x, hxU, rfl⟩, hxt⟩
        exact ⟨x, ⟨hxU, by simpa using hxt⟩, rfl⟩
      · rintro y ⟨x, ⟨hxU, hxt⟩, rfl⟩
        exact ⟨⟨x, hxU, rfl⟩, by simpa⟩
    rw [himage]
    exact htpre.image e e.continuous.continuousOn

/-- Invariance of preconnected approach regions under an ambient homeomorphism. -/
theorem isPreconnectedApproachAt_image_homeomorph_iff {U : Set X} {a : X}
    (e : X ≃ₜ Y) :
    IsPreconnectedApproachAt U a ↔ IsPreconnectedApproachAt (e '' U) (e a) := by
  refine ⟨fun h ↦ h.image_homeomorph e, fun h ↦ ?_⟩
  have h' := h.image_homeomorph e.symm
  have himage : e.symm '' (e '' U) = U := by
    ext x
    simp
  rw [himage] at h'
  simpa using h'

/-- The approach-region condition depends only on the germ of the set at the point. -/
theorem isPreconnectedApproachAt_inter_iff {U V : Set X} {a : X} (hV : V ∈ nhds a) :
    IsPreconnectedApproachAt (U ∩ V) a ↔ IsPreconnectedApproachAt U a := by
  have shrink (A : Set X) (hA : IsPreconnectedApproachAt A a) :
      ∀ s ∈ nhds a, ∃ t ∈ nhds a, t ⊆ s ∩ V ∧ IsPreconnected (A ∩ t) := by
    intro s hs
    exact hA _ (inter_mem hs hV)
  constructor
  · intro h s hs
    obtain ⟨t, ht, hts, htpre⟩ := shrink (U ∩ V) h s hs
    refine ⟨t, ht, hts.trans inter_subset_left, ?_⟩
    have htV : t ⊆ V := hts.trans inter_subset_right
    have heq : (U ∩ V) ∩ t = U ∩ t := by
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩, fun hx ↦ ⟨⟨hx.1, htV hx.2⟩, hx.2⟩⟩
    rwa [heq] at htpre
  · intro h s hs
    obtain ⟨t, ht, hts, htpre⟩ := shrink U h s hs
    refine ⟨t, ht, hts.trans inter_subset_left, ?_⟩
    have htV : t ⊆ V := hts.trans inter_subset_right
    have heq : (U ∩ V) ∩ t = U ∩ t := by
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩, fun hx ↦ ⟨⟨hx.1, htV hx.2⟩, hx.2⟩⟩
    rwa [heq]

/-- An open partial homeomorphism preserves preconnected approach regions for sets contained in
its source. -/
theorem IsPreconnectedApproachAt.image_openPartialHomeomorph {U : Set X} {a : X}
    (h : IsPreconnectedApproachAt U a) (e : OpenPartialHomeomorph X Y)
    (ha : a ∈ e.source) (hU : U ⊆ e.source) :
    IsPreconnectedApproachAt (e '' U) (e a) := by
  intro s hs
  have hs' : e ⁻¹' s ∈ nhds a := (e.continuousAt ha).preimage_mem_nhds hs
  obtain ⟨t, ht, hts, htpre⟩ := h _ hs'
  have ht' : t ∈ nhds (e.symm (e a)) := by simpa [e.left_inv ha] using ht
  let T : Set Y := e.symm ⁻¹' t ∩ e.target
  have hT : T ∈ nhds (e a) := inter_mem
    ((e.continuousAt_symm (e.map_source ha)).preimage_mem_nhds ht')
    (e.open_target.mem_nhds (e.map_source ha))
  refine ⟨T, hT, ?_, ?_⟩
  · rintro y ⟨hyt, hytarget⟩
    have hy : e.symm y ∈ e ⁻¹' s := hts hyt
    exact (e.right_inv hytarget) ▸ hy
  · have himage : (e '' U) ∩ T = e '' (U ∩ t) := by
      apply subset_antisymm
      · rintro y ⟨⟨x, hxU, hxy⟩, hyt, -⟩
        subst y
        exact ⟨x, ⟨hxU, by simpa [e.left_inv (hU hxU)] using hyt⟩, rfl⟩
      · rintro y ⟨x, ⟨hxU, hxt⟩, rfl⟩
        exact ⟨⟨x, hxU, rfl⟩, by simpa [T, e.left_inv (hU hxU)], e.map_source (hU hxU)⟩
    rw [himage]
    exact htpre.image e (e.continuousOn.mono (inter_subset_left.trans hU))

/-- Invariance under an open partial homeomorphism, for a set contained in its source. -/
theorem isPreconnectedApproachAt_image_openPartialHomeomorph_iff {U : Set X} {a : X}
    (e : OpenPartialHomeomorph X Y) (ha : a ∈ e.source) (hU : U ⊆ e.source) :
    IsPreconnectedApproachAt U a ↔ IsPreconnectedApproachAt (e '' U) (e a) := by
  refine ⟨fun h ↦ h.image_openPartialHomeomorph e ha hU, fun h ↦ ?_⟩
  have himage : e.symm '' (e '' U) = U := e.symm_image_image_of_subset_source hU
  have htarget : e '' U ⊆ e.target := fun _ ⟨x, hxU, hxy⟩ ↦ hxy ▸ e.map_source (hU hxU)
  have h' := h.image_openPartialHomeomorph e.symm (e.map_source ha) htarget
  rw [himage] at h'
  simpa [e.left_inv ha] using h'

/-- Local-germ form of invariance under an open partial homeomorphism.  The two ambient sets need
only agree through the chart near the distinguished points. -/
theorem isPreconnectedApproachAt_openPartialHomeomorph_iff {U : Set X} {V : Set Y} {a : X}
    (e : OpenPartialHomeomorph X Y) (ha : a ∈ e.source)
    (hUV : V ∩ e.target = e '' (U ∩ e.source)) :
    IsPreconnectedApproachAt U a ↔ IsPreconnectedApproachAt V (e a) := by
  have hs : e.source ∈ nhds a := e.open_source.mem_nhds ha
  have ht : e.target ∈ nhds (e a) := e.open_target.mem_nhds (e.map_source ha)
  have hpartial := isPreconnectedApproachAt_image_openPartialHomeomorph_iff
    (U := U ∩ e.source) e ha inter_subset_right
  constructor
  · intro hU
    have hUs : IsPreconnectedApproachAt (U ∩ e.source) a :=
      (isPreconnectedApproachAt_inter_iff hs).mpr hU
    have hVt : IsPreconnectedApproachAt (V ∩ e.target) (e a) := hUV ▸ hpartial.mp hUs
    exact (isPreconnectedApproachAt_inter_iff ht).mp hVt
  · intro hV
    have hVt : IsPreconnectedApproachAt (V ∩ e.target) (e a) :=
      (isPreconnectedApproachAt_inter_iff ht).mpr hV
    have hUs : IsPreconnectedApproachAt (U ∩ e.source) a := hpartial.mpr (hUV ▸ hVt)
    exact (isPreconnectedApproachAt_inter_iff hs).mp hUs

/-! ## A reusable finite logarithm chart -/

/-- The branch of the exponential chart centered at `z₀`, precomposed with multiplication by
`A`.  Its map is globally the function `z ↦ exp (A * z)`, while its source is the width-`2π`
strip centered at `z₀` after applying `A`. -/
noncomputable def centeredLinearExpChart (A z₀ : ℂ) (hA : A ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.transHomeomorph
    (Homeomorph.transOpenPartialHomeomorph
      ((Homeomorph.addRight (-z₀)).trans (Homeomorph.mulLeft₀ A hA))
      Complex.expOpenPartialHomeomorph)
    (Homeomorph.mulLeft₀ (Complex.exp (A * z₀)) (Complex.exp_ne_zero _))

@[simp] theorem centeredLinearExpChart_apply (A z₀ : ℂ) (hA : A ≠ 0) (z : ℂ) :
    centeredLinearExpChart A z₀ hA z = Complex.exp (A * z) := by
  change Complex.exp (A * z₀) * Complex.exp (A * (z + -z₀)) = Complex.exp (A * z)
  rw [← Complex.exp_add]
  congr 1
  ring

theorem mem_centeredLinearExpChart_source_iff (A z₀ : ℂ) (hA : A ≠ 0) (z : ℂ) :
    z ∈ (centeredLinearExpChart A z₀ hA).source ↔
      -Real.pi < (A * (z - z₀)).im ∧ (A * (z - z₀)).im < Real.pi := by
  rfl

theorem mem_centeredLinearExpChart_source (A z₀ : ℂ) (hA : A ≠ 0) :
    z₀ ∈ (centeredLinearExpChart A z₀ hA).source := by
  rw [mem_centeredLinearExpChart_source_iff]
  simp [Real.pi_pos]

/-- No finite logarithm chart reaches the cusp value `0`. -/
theorem zero_not_mem_centeredLinearExpChart_target (A z₀ : ℂ) (hA : A ≠ 0) :
    0 ∉ (centeredLinearExpChart A z₀ hA).target := by
  intro hzero
  have hr := (centeredLinearExpChart A z₀ hA).right_inv hzero
  rw [centeredLinearExpChart_apply] at hr
  exact Complex.exp_ne_zero _ hr

/-- A local logarithm chart for `z ↦ exp (2 π i z / width)`, centered at an arbitrary
finite preimage `z₀`. -/
noncomputable def cuspExponentialLocalChart (width : ℝ) (z₀ : ℂ) (hwidth : width ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  centeredLinearExpChart (2 * Real.pi * Complex.I / width) z₀
    (div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
      (by exact_mod_cast hwidth))

@[simp] theorem cuspExponentialLocalChart_apply (width : ℝ) (z₀ : ℂ)
    (hwidth : width ≠ 0) (z : ℂ) :
    cuspExponentialLocalChart width z₀ hwidth z =
      Complex.exp (2 * Real.pi * Complex.I * z / width) := by
  rw [cuspExponentialLocalChart, centeredLinearExpChart_apply]
  congr 1
  ring

theorem mem_cuspExponentialLocalChart_source (width : ℝ) (z₀ : ℂ)
    (hwidth : width ≠ 0) : z₀ ∈ (cuspExponentialLocalChart width z₀ hwidth).source :=
  mem_centeredLinearExpChart_source _ _ _

theorem zero_not_mem_cuspExponentialLocalChart_target (width : ℝ) (z₀ : ℂ)
    (hwidth : width ≠ 0) : 0 ∉ (cuspExponentialLocalChart width z₀ hwidth).target :=
  zero_not_mem_centeredLinearExpChart_target _ _ _

/-- A useful geometric criterion for putting a set into the centered cusp-exponential chart. -/
theorem subset_cuspExponentialLocalChart_source_of_abs_re_sub_lt
    {A : Set ℂ} {width : ℝ} {z₀ : ℂ} (hwidth : 0 < width)
    (hA : ∀ z ∈ A, |z.re - z₀.re| < width / 2) :
    A ⊆ (cuspExponentialLocalChart width z₀ hwidth.ne').source := by
  intro z hz
  rw [cuspExponentialLocalChart, mem_centeredLinearExpChart_source_iff]
  have him : ((2 * Real.pi * Complex.I / width) * (z - z₀)).im =
      2 * Real.pi * (z.re - z₀.re) / width := by
    simp [Complex.div_im, Complex.mul_im]
    field_simp
  rw [him]
  have habs := hA z hz
  rw [abs_lt] at habs
  constructor
  · rw [lt_div_iff₀ hwidth]
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ hwidth]
    nlinarith [Real.pi_pos]

/-- A whole chamber of horizontal span at most `width / 2` lies in the logarithm chart centered
at any point whose real coordinate is in the closed chamber interval. -/
theorem subset_cuspExponentialLocalChart_source_of_re_mem_Ioo_Icc
    {A : Set ℂ} {width l r : ℝ} {z₀ : ℂ} (hwidth : 0 < width)
    (hspan : r - l ≤ width / 2)
    (hA : ∀ z ∈ A, l < z.re ∧ z.re < r)
    (hz₀ : l ≤ z₀.re ∧ z₀.re ≤ r) :
    A ⊆ (cuspExponentialLocalChart width z₀ hwidth.ne').source := by
  apply subset_cuspExponentialLocalChart_source_of_abs_re_sub_lt hwidth
  intro z hz
  rw [abs_lt]
  obtain ⟨hzl, hzr⟩ := hA z hz
  constructor <;> linarith

/-- Closure-friendly version of the preceding strip criterion.  This is directly applicable to
finite boundary preimages of the cusp chamber. -/
theorem subset_cuspExponentialLocalChart_source_of_re_mem_Ioo_of_mem_closure
    {A : Set ℂ} {width l r : ℝ} {z₀ : ℂ} (hwidth : 0 < width)
    (hspan : r - l ≤ width / 2)
    (hA : ∀ z ∈ A, l < z.re ∧ z.re < r)
    (hz₀ : z₀ ∈ closure A) :
    A ⊆ (cuspExponentialLocalChart width z₀ hwidth.ne').source := by
  apply subset_cuspExponentialLocalChart_source_of_re_mem_Ioo_Icc hwidth hspan hA
  have hclosed : IsClosed {z : ℂ | l ≤ z.re ∧ z.re ≤ r} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hsub : A ⊆ {z : ℂ | l ≤ z.re ∧ z.re ≤ r} := by
    intro z hz
    exact ⟨(hA z hz).1.le, (hA z hz).2.le⟩
  exact closure_minimal hsub hclosed hz₀

/-- Every convex subset of a real normed space has preconnected approach regions at every point.
Neither openness nor nonemptiness is needed. -/
theorem Convex.isPreconnectedApproachAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (a : E) : IsPreconnectedApproachAt U a := by
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨ball a ε, ball_mem_nhds a hε, hεs, (hU.inter (convex_ball a ε)).isPreconnected⟩

/-- If an ambient homeomorphism straightens a set to a convex set, the original set has
preconnected approach regions. -/
theorem isPreconnectedApproachAt_of_homeomorph_image_convex {U : Set ℂ} (a : ℂ)
    (e : ℂ ≃ₜ ℂ) (hconv : Convex ℝ (e '' U)) : IsPreconnectedApproachAt U a :=
  (isPreconnectedApproachAt_image_homeomorph_iff e).mpr
    (Convex.isPreconnectedApproachAt hconv (e a))

/-- A convenient local-chart package: straighten the source-side set by an ambient homeomorphism,
then carry the connected-approach basis through an open partial homeomorphism.  This is the form
used at every finite point of an exponentially bounded cusp. -/
theorem isPreconnectedApproachAt_of_openPartialHomeomorph_homeomorph_image_convex
    {A B : Set ℂ} {a : ℂ} (e : OpenPartialHomeomorph ℂ ℂ) (ha : a ∈ e.source)
    (hAB : B ∩ e.target = e '' (A ∩ e.source))
    (g : ℂ ≃ₜ ℂ) (hconv : Convex ℝ (g '' A)) :
    IsPreconnectedApproachAt B (e a) :=
  (isPreconnectedApproachAt_openPartialHomeomorph_iff e ha hAB).mp
    (isPreconnectedApproachAt_of_homeomorph_image_convex a g hconv)

/-- Finite-point cusp-exponential instance.  Once the source chamber lies in the centered
logarithm strip, no further local-set equality has to be proved: it follows from the exact image
description. -/
theorem isPreconnectedApproachAt_cuspExponential_image
    {A : Set ℂ} (width : ℝ) (z₀ : ℂ) (hwidth : width ≠ 0)
    (hA : A ⊆ (cuspExponentialLocalChart width z₀ hwidth).source)
    (g : ℂ ≃ₜ ℂ) (hconv : Convex ℝ (g '' A)) :
    IsPreconnectedApproachAt
      ((fun z : ℂ ↦ Complex.exp (2 * Real.pi * Complex.I * z / width)) '' A)
      (Complex.exp (2 * Real.pi * Complex.I * z₀ / width)) := by
  let e := cuspExponentialLocalChart width z₀ hwidth
  let q : ℂ → ℂ := fun z ↦ Complex.exp (2 * Real.pi * Complex.I * z / width)
  have heq : Set.EqOn e q A := fun z _ ↦ cuspExponentialLocalChart_apply width z₀ hwidth z
  have heA : e '' A ⊆ e.target := (image_mono hA).trans e.image_source_subset
  have hAB : q '' A ∩ e.target = e '' (A ∩ e.source) := by
    rw [← heq.image_eq, inter_eq_left.mpr heA, inter_eq_left.mpr hA]
  have h := isPreconnectedApproachAt_of_openPartialHomeomorph_homeomorph_image_convex
    e (mem_cuspExponentialLocalChart_source width z₀ hwidth) hAB g hconv
  simpa only [e, q, cuspExponentialLocalChart_apply] using h

variable {U : Set ℂ} {f F : ℂ → ℂ} {a : ℂ}

/-- The fibre of a continuous conformal extension over an image-boundary point is the
cluster set of the inverse conformal map at that point. -/
theorem clusterSetOn_invFunOn_eq_boundary_fiber
    (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (ha : a ∈ frontier (f '' U)) :
    clusterSetOn (invFunOn f U) (f '' U) a = {z | z ∈ frontier U ∧ F z = a} := by
  let g : ℂ → ℂ := invFunOn f U
  have hbij : BijOn f U (f '' U) := hfi.bijOn_image
  have hgU : MapsTo g (f '' U) U := hbij.surjOn.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hbij.invOn_invFunOn.1
  have hright : RightInvOn g f (f '' U) := hbij.invOn_invFunOn.2
  ext z
  constructor
  · intro hz
    have hz' : MapClusterPt z (nhdsWithin a (f '' U)) g :=
      mem_clusterSetOn_iff.mp hz
    have hzcl : z ∈ closure U :=
      closure_mono (Function.invFunOn_image_image_subset f U)
        (clusterSetOn_subset_closure_image hz)
    let l : Filter ℂ := nhdsWithin a (f '' U)
    have hmap_closure : map g l ≤ principal (closure U) := by
      rw [le_principal_iff, mem_map]
      exact mem_of_superset self_mem_nhdsWithin fun y hy ↦ subset_closure (hgU hy)
    have hF_tendsto : Tendsto F (nhds z ⊓ map g l) (nhds (F z)) := by
      apply (hFc z hzcl).mono_left
      rw [nhdsWithin]
      exact inf_le_inf le_rfl hmap_closure
    have hzF : MapClusterPt (F z) l (F ∘ g) := by
      exact hz'.tendsto_comp' hF_tendsto
    have hFg : F ∘ g =ᶠ[l] id := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      change F (g y) = y
      rw [hFf (hgU hy), hright hy]
    have hzid : MapClusterPt (F z) l id := hzF.congrFun hFg
    have hlim : Tendsto id l (nhds a) := tendsto_id.mono_left nhdsWithin_le_nhds
    have : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure ha)
    have hFa : F z = a := by
      have : NeBot (nhds (F z) ⊓ l) := hzid.clusterPt
      exact tendsto_nhds_unique
        (tendsto_id.mono_left inf_le_left)
        (hlim.mono_left inf_le_right)
    have hzU : z ∉ U := by
      intro hzU
      have ha_image : a ∈ f '' U := ⟨z, hzU, by rw [← hFa, hFf hzU]⟩
      exact ((isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi).frontier_eq.subset ha).2
        ha_image
    refine ⟨?_, hFa⟩
    rw [hUo.frontier_eq]
    exact ⟨hzcl, hzU⟩
  · rintro ⟨hzfr, hFza⟩
    let p : Filter ℂ := nhdsWithin z U
    have : NeBot p :=
      mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hzfr)
    have hgf : g ∘ f =ᶠ[p] id := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hleft hx
    have hzcomp : MapClusterPt z p (g ∘ f) := by
      exact (ClusterPt.of_le_nhds nhdsWithin_le_nhds).mapClusterPt_id.congrFun hgf.symm
    have hftend_nhds : Tendsto f p (nhds a) := by
      have hFtend : Tendsto F p (nhds (F z)) :=
        (hFc z (frontier_subset_closure hzfr)).mono_left (nhdsWithin_mono z subset_closure)
      have hfeq : f =ᶠ[p] F := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hFf hx).symm
      simpa only [hFza] using (tendsto_congr' hfeq).mpr hFtend
    have hftend : Tendsto f p (nhdsWithin a (f '' U)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hftend_nhds
        (mem_of_superset self_mem_nhdsWithin fun x hx ↦ ⟨x, hx, rfl⟩)
    exact mem_clusterSetOn_iff.mpr (MapClusterPt.of_comp hftend hzcomp)

/-- If the image domain is locally preconnected from within at a boundary point, the fibre of a
continuous conformal extension over that point is preconnected. -/
theorem isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (ha : a ∈ frontier (f '' U))
    (hloc : IsPreconnectedApproachAt (f '' U) a) :
    IsPreconnected {z : frontier U | F z = a} := by
  let g : ℂ → ℂ := invFunOn f U
  let e := DifferentiableOn.toOpenPartialHomeomorph hfd hUo hfi
  have hgU : MapsTo g (f '' U) U := hfi.bijOn_image.surjOn.mapsTo_invFunOn
  have hgc : ContinuousOn g (f '' U) := by
    simpa only [g, e, DifferentiableOn.toOpenPartialHomeomorph_target,
      DifferentiableOn.toOpenPartialHomeomorph_coe_symm] using e.continuousOn_symm
  have hcluster : IsPreconnected (clusterSetOn g (f '' U) a) :=
    isPreconnected_clusterSetOn hUb.isCompact_closure
      (fun z hz ↦ subset_closure (hgU hz)) hgc hloc
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  have himage : Subtype.val '' {z : frontier U | F z = a} =
      {z | z ∈ frontier U ∧ F z = a} := by
    ext z
    simp [and_comm]
  rw [himage, ← clusterSetOn_invFunOn_eq_boundary_fiber hUo hfd hfi hFc hFf ha]
  exact hcluster

/-- A convex conformal image has preconnected boundary fibres. -/
theorem isPreconnected_boundary_fiber_of_convex_image
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (ha : a ∈ frontier (f '' U)) (hconv : Convex ℝ (f '' U)) :
    IsPreconnected {z : frontier U | F z = a} :=
  isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    hUo hUb hfd hfi hFc hFf ha (Convex.isPreconnectedApproachAt hconv a)

/-- More generally, it is enough that an ambient homeomorphism straighten the conformal image to
a convex set. -/
theorem isPreconnected_boundary_fiber_of_homeomorph_image_convex
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (ha : a ∈ frontier (f '' U)) (e : ℂ ≃ₜ ℂ)
    (hconv : Convex ℝ (e '' (f '' U))) :
    IsPreconnected {z : frontier U | F z = a} :=
  isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    hUo hUb hfd hfi hFc hFf ha
      (isPreconnectedApproachAt_of_homeomorph_image_convex a e hconv)

/-- Boundary-fibre theorem in local-chart form.  The chart only has to identify the germ of the
conformal image with a source-side set that can be straightened to a convex set. -/
theorem isPreconnected_boundary_fiber_of_openPartialHomeomorph_germ
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    {A : Set ℂ} {z₀ : ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hz₀ : z₀ ∈ e.source)
    (hchart : f '' U ∩ e.target = e '' (A ∩ e.source))
    (g : ℂ ≃ₜ ℂ) (hconv : Convex ℝ (g '' A))
    (hboundary : e z₀ ∈ frontier (f '' U)) :
    IsPreconnected {z : frontier U | F z = e z₀} :=
  isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    hUo hUb hfd hfi hFc hFf hboundary
      (isPreconnectedApproachAt_of_openPartialHomeomorph_homeomorph_image_convex
        e hz₀ hchart g hconv)

/-- Direct finite-point cusp-exponential boundary-fibre corollary.  Its only model-specific
condition is that the (open) source chamber stays within the centered logarithm strip. -/
theorem isPreconnected_boundary_fiber_of_cuspExponential_image
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    {A : Set ℂ} (width : ℝ) (z₀ : ℂ) (hwidth : width ≠ 0)
    (himage : f '' U =
      (fun z : ℂ ↦ Complex.exp (2 * Real.pi * Complex.I * z / width)) '' A)
    (hA : A ⊆ (cuspExponentialLocalChart width z₀ hwidth).source)
    (g : ℂ ≃ₜ ℂ) (hconv : Convex ℝ (g '' A))
    (hboundary : Complex.exp (2 * Real.pi * Complex.I * z₀ / width) ∈ frontier (f '' U)) :
    IsPreconnected
      {z : frontier U | F z = Complex.exp (2 * Real.pi * Complex.I * z₀ / width)} := by
  apply isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    hUo hUb hfd hfi hFc hFf hboundary
  rw [himage]
  exact isPreconnectedApproachAt_cuspExponential_image width z₀ hwidth hA g hconv

/-- A local connected-approach basis at every image-boundary point makes every fibre of the
boundary restriction preconnected. -/
theorem isPreconnected_frontier_fiber_of_image_approach
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hloc : ∀ a ∈ frontier (f '' U), IsPreconnectedApproachAt (f '' U) a) :
    ∀ a, IsPreconnected {z : frontier U | F z = a} := by
  intro a
  by_cases ha : a ∈ frontier (f '' U)
  · exact isPreconnected_boundary_fiber_of_isPreconnected_image_approach
      hUo hUb hfd hfi hFc hFf ha (hloc a ha)
  · have hboundary : F '' frontier U ⊆ frontier (f '' U) :=
      image_frontier_subset_frontier_image hUo hfd hfi hFc hFf
    have hempty : {z : frontier U | F z = a} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hz
      exact ha (hboundary ⟨z, z.2, hz⟩)
    rw [hempty]
    exact isPreconnected_empty

variable {c : ℂ} {r : ℝ}

/-- The preceding inverse-cluster reduction, specialized to a disc and fed to Tau Ceti's
monotone-extension theorem. -/
theorem injOn_closedBall_of_isPreconnected_image_approach
    (hr : 0 < r) (hfd : DifferentiableOn ℂ f (ball c r))
    (hfi : InjOn f (ball c r)) (hFc : ContinuousOn F (closedBall c r))
    (hFf : EqOn F f (ball c r))
    (hloc : ∀ a ∈ frontier (f '' ball c r),
      IsPreconnectedApproachAt (f '' ball c r) a) :
    InjOn F (closedBall c r) := by
  have hcl : closure (ball c r) = closedBall c r := closure_ball c hr.ne'
  have hpre : ∀ a, IsPreconnected {z : sphere c r | F z = a} := by
    intro a
    have h := isPreconnected_frontier_fiber_of_image_approach
      isOpen_ball isBounded_ball hfd hfi (hcl.symm ▸ hFc) hFf hloc a
    rw [frontier_ball c hr.ne'] at h
    exact h
  have hfdF : DifferentiableOn ℂ F (ball c r) :=
    hfd.congr fun z hz ↦ hFf hz
  have hfiF : InjOn F (ball c r) := by
    intro x hx y hy hxy
    apply hfi hx hy
    rw [← hFf hx, ← hFf hy]
    exact hxy
  exact injOn_closedBall_of_isPreconnected_boundary_fiber hr hFc hfdF hfiF hpre


end TauCeti
