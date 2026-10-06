module

public import TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster
import all TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster

@[expose] public section

open Set Metric Topology Function Filter

noncomputable section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Preconnected approach regions are preserved by an ambient homeomorphism. -/
theorem IsPreconnectedApproachAt.image_homeomorph {U : Set X} {a : X}
    (h : IsPreconnectedApproachAt U a) (e : X ≃ₜ Y) :
    IsPreconnectedApproachAt (e '' U) (e a) := by
  rw [isPreconnectedApproachAt_def]
  intro s hs
  have hs' : e ⁻¹' s ∈ nhds a := e.continuous.continuousAt.preimage_mem_nhds hs
  obtain ⟨t, ht, hts, htpre⟩ := isPreconnectedApproachAt_def.mp h _ hs'
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
    exact isPreconnectedApproachAt_def.mp hA _ (inter_mem hs hV)
  constructor
  · intro h
    rw [isPreconnectedApproachAt_def]
    intro s hs
    obtain ⟨t, ht, hts, htpre⟩ := shrink (U ∩ V) h s hs
    refine ⟨t, ht, hts.trans inter_subset_left, ?_⟩
    have htV : t ⊆ V := hts.trans inter_subset_right
    have heq : (U ∩ V) ∩ t = U ∩ t := by
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩, fun hx ↦ ⟨⟨hx.1, htV hx.2⟩, hx.2⟩⟩
    rwa [heq] at htpre
  · intro h
    rw [isPreconnectedApproachAt_def]
    intro s hs
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
  rw [isPreconnectedApproachAt_def]
  intro s hs
  have hs' : e ⁻¹' s ∈ nhds a := (e.continuousAt ha).preimage_mem_nhds hs
  obtain ⟨t, ht, hts, htpre⟩ := isPreconnectedApproachAt_def.mp h _ hs'
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


/-- Every convex subset of a real normed space has preconnected approach regions at every point.
Neither openness nor nonemptiness is needed. -/
theorem Convex.isPreconnectedApproachAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (a : E) : IsPreconnectedApproachAt U a := by
  rw [isPreconnectedApproachAt_def]
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

end TauCeti
