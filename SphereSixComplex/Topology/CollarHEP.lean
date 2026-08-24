module

public import SphereSixComplex.Topology.RelativeHomotopy

/-!
# The homotopy-extension property of a compact collar

This file supplies the missing cofibration argument for an explicit collar.  The construction is
elementary.  In collar coordinates, let `r` be the inward coordinate and let
`lambda(r) = max (1 - 2r) 0`.  A point `(r,t)` of the cylinder is retracted to its bottom or its
vertical zero-section by taking the positive and negative parts of `r - t * lambda(r)`.  Since
`lambda` vanishes for `r >= 1/2`, the construction agrees with the identity on the bottom outside
a compact subcollar and therefore extends continuously to the whole ambient space.
-/

@[expose] public section

noncomputable section

open ContinuousMap Function Set TopologicalSpace Topology
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe u uE uH

/-! ## The scalar retraction in a half collar -/

/-- A cutoff which is one at the zero section and vanishes beyond the half-depth subcollar. -/
public def collarHEPCutoff (r : HalfCollarParameter) : ℝ :=
  max (1 - 2 * (r.1 : ℝ)) 0

public theorem collarHEPCutoff_nonneg (r : HalfCollarParameter) :
    0 ≤ collarHEPCutoff r :=
  le_max_right _ _

public theorem collarHEPCutoff_le_one (r : HalfCollarParameter) :
    collarHEPCutoff r ≤ 1 := by
  apply max_le
  · linarith [r.1.2.1]
  · norm_num

@[simp]
public theorem collarHEPCutoff_start : collarHEPCutoff halfCollarStart = 1 := by
  norm_num [collarHEPCutoff, halfCollarStart, collarStart]

public theorem collarHEPCutoff_eq_zero_of_half_le
    {r : HalfCollarParameter} (hr : (1 / 2 : ℝ) ≤ (r.1 : ℝ)) :
    collarHEPCutoff r = 0 := by
  rw [collarHEPCutoff, max_eq_right]
  linarith

public theorem continuous_collarHEPCutoff : Continuous collarHEPCutoff := by
  unfold collarHEPCutoff
  fun_prop

/-- The amount of cylinder time used by the collar retraction. -/
public def collarHEPEffectiveTime (t : unitInterval) (r : HalfCollarParameter) : ℝ :=
  (t : ℝ) * collarHEPCutoff r

public theorem collarHEPEffectiveTime_nonneg (t : unitInterval) (r : HalfCollarParameter) :
    0 ≤ collarHEPEffectiveTime t r :=
  mul_nonneg t.2.1 (collarHEPCutoff_nonneg r)

public theorem collarHEPEffectiveTime_le (t : unitInterval) (r : HalfCollarParameter) :
    collarHEPEffectiveTime t r ≤ (t : ℝ) := by
  simpa [collarHEPEffectiveTime] using
    mul_le_mul_of_nonneg_left (collarHEPCutoff_le_one r) t.2.1

public theorem continuous_collarHEPEffectiveTime :
    Continuous (fun p : unitInterval × HalfCollarParameter ↦
      collarHEPEffectiveTime p.1 p.2) := by
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_collarHEPCutoff.comp continuous_snd)

/-- The radial coordinate after retracting the collar cylinder to its L-shaped boundary. -/
public def collarHEPRadius (t : unitInterval) (r : HalfCollarParameter) :
    HalfCollarParameter :=
  ⟨⟨max ((r.1 : ℝ) - collarHEPEffectiveTime t r) 0, by
      constructor
      · exact le_max_right _ _
      · have hle : max ((r.1 : ℝ) - collarHEPEffectiveTime t r) 0 ≤ (r.1 : ℝ) := by
          apply max_le
          · linarith [collarHEPEffectiveTime_nonneg t r]
          · exact r.1.2.1
        exact hle.trans r.1.2.2⟩, by
    have hle : max ((r.1 : ℝ) - collarHEPEffectiveTime t r) 0 ≤ (r.1 : ℝ) := by
      apply max_le
      · linarith [collarHEPEffectiveTime_nonneg t r]
      · exact r.1.2.1
    exact hle.trans_lt r.2⟩

/-- The vertical coordinate after retracting the collar cylinder to its L-shaped boundary. -/
public def collarHEPVerticalTime (t : unitInterval) (r : HalfCollarParameter) :
    unitInterval :=
  ⟨max (collarHEPEffectiveTime t r - (r.1 : ℝ)) 0, by
    constructor
    · exact le_max_right _ _
    · apply max_le
      · exact (sub_le_self _ r.1.2.1).trans (collarHEPEffectiveTime_le t r) |>.trans t.2.2
      · exact zero_le_one⟩

public theorem continuous_collarHEPRadius :
    Continuous (fun p : unitInterval × HalfCollarParameter ↦
      collarHEPRadius p.1 p.2) := by
  have hreal : Continuous (fun p : unitInterval × HalfCollarParameter ↦
      max ((p.2.1 : ℝ) - collarHEPEffectiveTime p.1 p.2) 0) := by
    exact (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd).sub
      continuous_collarHEPEffectiveTime).max continuous_const
  exact (hreal.subtype_mk _).subtype_mk _

public theorem continuous_collarHEPVerticalTime :
    Continuous (fun p : unitInterval × HalfCollarParameter ↦
      collarHEPVerticalTime p.1 p.2) := by
  have hreal : Continuous (fun p : unitInterval × HalfCollarParameter ↦
      max (collarHEPEffectiveTime p.1 p.2 - (p.2.1 : ℝ)) 0) := by
    exact (continuous_collarHEPEffectiveTime.sub
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)).max
        continuous_const
  exact hreal.subtype_mk _

@[simp]
public theorem collarHEPRadius_zero (r : HalfCollarParameter) :
    collarHEPRadius 0 r = r := by
  apply Subtype.ext
  apply Subtype.ext
  simp [collarHEPRadius, collarHEPEffectiveTime, collarHEPCutoff, r.1.2.1]

@[simp]
public theorem collarHEPVerticalTime_zero (r : HalfCollarParameter) :
    collarHEPVerticalTime 0 r = 0 := by
  apply Subtype.ext
  simp [collarHEPVerticalTime, collarHEPEffectiveTime, r.1.2.1]

@[simp]
public theorem collarHEPEffectiveTime_start (t : unitInterval) :
    collarHEPEffectiveTime t halfCollarStart = (t : ℝ) := by
  simp [collarHEPEffectiveTime]

@[simp]
public theorem collarHEPRadius_start (t : unitInterval) :
    collarHEPRadius t halfCollarStart = halfCollarStart := by
  apply Subtype.ext
  apply Subtype.ext
  change max (0 - collarHEPEffectiveTime t halfCollarStart) 0 = 0
  rw [collarHEPEffectiveTime_start]
  exact max_eq_right (by linarith [t.2.1])

@[simp]
public theorem collarHEPVerticalTime_start (t : unitInterval) :
    collarHEPVerticalTime t halfCollarStart = t := by
  apply Subtype.ext
  change max (collarHEPEffectiveTime t halfCollarStart - 0) 0 = (t : ℝ)
  rw [collarHEPEffectiveTime_start, sub_zero, max_eq_left t.2.1]

public theorem collarHEPRadius_eq_self_of_half_le
    (t : unitInterval) {r : HalfCollarParameter} (hr : (1 / 2 : ℝ) ≤ (r.1 : ℝ)) :
    collarHEPRadius t r = r := by
  apply Subtype.ext
  apply Subtype.ext
  simp [collarHEPRadius, collarHEPEffectiveTime,
    collarHEPCutoff_eq_zero_of_half_le hr, r.1.2.1]

public theorem collarHEPVerticalTime_eq_zero_of_half_le
    (t : unitInterval) {r : HalfCollarParameter} (hr : (1 / 2 : ℝ) ≤ (r.1 : ℝ)) :
    collarHEPVerticalTime t r = 0 := by
  apply Subtype.ext
  simp [collarHEPVerticalTime, collarHEPEffectiveTime,
    collarHEPCutoff_eq_zero_of_half_le hr, r.1.2.1]

public theorem collarHEPRadius_eq_start_of_effective_eq
    {t : unitInterval} {r : HalfCollarParameter}
    (h : collarHEPEffectiveTime t r = (r.1 : ℝ)) :
    collarHEPRadius t r = halfCollarStart := by
  apply Subtype.ext
  apply Subtype.ext
  simp [collarHEPRadius, h, halfCollarStart, collarStart]

public theorem collarHEPVerticalTime_eq_zero_of_effective_eq
    {t : unitInterval} {r : HalfCollarParameter}
    (h : collarHEPEffectiveTime t r = (r.1 : ℝ)) :
    collarHEPVerticalTime t r = 0 := by
  apply Subtype.ext
  simp [collarHEPVerticalTime, h]

/-! ## Extending a homotopy in collar coordinates -/

section LocalExtension

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hmodel : Type uH} [TopologicalSpace Hmodel]
  {I : ModelWithCorners ℝ E Hmodel}
  {M W Y : Type u}
  [TopologicalSpace M] [ChartedSpace Hmodel M] [IsManifold I ∞ M]
  [TopologicalSpace W]
  [ChartedSpace (ModelProd Hmodel (EuclideanHalfSpace 1)) W]
  [TopologicalSpace Y]

/-- The extension formula on the collar chart.  It first moves along the bottom of the ambient
cylinder; after reaching the zero section it follows the prescribed vertical homotopy. -/
public def collarLocalHomotopyExtension
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁) :
    unitInterval × CollarSource M → Y :=
  fun p ↦
    if collarHEPEffectiveTime p.1 p.2.2 ≤ (p.2.2.1 : ℝ) then
      f (c.chart (p.2.1, collarHEPRadius p.1 p.2.2))
    else
      K (collarHEPVerticalTime p.1 p.2.2, p.2.1)

public theorem continuous_collarLocalHomotopyExtension
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁) :
    Continuous (collarLocalHomotopyExtension c f K) := by
  let e : unitInterval × CollarSource M → ℝ :=
    fun p ↦ collarHEPEffectiveTime p.1 p.2.2
  let r : unitInterval × CollarSource M → ℝ := fun p ↦ (p.2.2.1 : ℝ)
  let bottom : unitInterval × CollarSource M → Y := fun p ↦
    f (c.chart (p.2.1, collarHEPRadius p.1 p.2.2))
  let vertical : unitInterval × CollarSource M → Y := fun p ↦
    K (collarHEPVerticalTime p.1 p.2.2, p.2.1)
  have he : Continuous e :=
    continuous_collarHEPEffectiveTime.comp (continuous_fst.prodMk continuous_snd.snd)
  have hr : Continuous r :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd.snd
  have hradius : Continuous (fun p : unitInterval × CollarSource M ↦
      collarHEPRadius p.1 p.2.2) :=
    continuous_collarHEPRadius.comp (continuous_fst.prodMk continuous_snd.snd)
  have hsource : Continuous (fun p : unitInterval × CollarSource M ↦
      (p.2.1, collarHEPRadius p.1 p.2.2)) :=
    continuous_snd.fst.prodMk hradius
  have hbottom : Continuous bottom :=
    f.continuous.comp (c.chart.contMDiff.continuous.comp hsource)
  have hvertical : Continuous vertical := by
    exact K.continuous.comp
      ((continuous_collarHEPVerticalTime.comp
          (continuous_fst.prodMk continuous_snd.snd)).prodMk continuous_snd.fst)
  change Continuous (fun p ↦ if e p ≤ r p then bottom p else vertical p)
  apply hbottom.if_le hvertical he hr
  intro p hp
  have hrad := collarHEPRadius_eq_start_of_effective_eq hp
  have htime := collarHEPVerticalTime_eq_zero_of_effective_eq hp
  change f (c.chart (p.2.1, collarHEPRadius p.1 p.2.2)) =
    K (collarHEPVerticalTime p.1 p.2.2, p.2.1)
  rw [hrad, htime]
  exact (K.map_zero_left p.2.1).symm

@[simp]
public theorem collarLocalHomotopyExtension_zero
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (p : CollarSource M) :
    collarLocalHomotopyExtension c f K (0, p) = f (c.chart p) := by
  simp [collarLocalHomotopyExtension, collarHEPEffectiveTime,
    p.2.1.2.1]

@[simp]
public theorem collarLocalHomotopyExtension_zeroSection
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (t : unitInterval) (m : M) :
    collarLocalHomotopyExtension c f K (t, collarSourceZeroSection M m) = K (t, m) := by
  unfold collarLocalHomotopyExtension
  change (if collarHEPEffectiveTime t halfCollarStart ≤ (0 : ℝ) then
      f (c.chart (m, collarHEPRadius t halfCollarStart))
    else K (collarHEPVerticalTime t halfCollarStart, m)) = K (t, m)
  rw [collarHEPEffectiveTime_start, collarHEPRadius_start,
    collarHEPVerticalTime_start]
  split_ifs with ht
  · have ht0 : t = 0 := by
      apply Subtype.ext
      exact le_antisymm ht t.2.1
    subst t
    exact (K.map_zero_left m).symm
  · rfl

public theorem collarLocalHomotopyExtension_eq_bottom_of_half_le
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (t : unitInterval) (p : CollarSource M) (hp : (1 / 2 : ℝ) ≤ (p.2.1 : ℝ)) :
    collarLocalHomotopyExtension c f K (t, p) = f (c.chart p) := by
  change (if collarHEPEffectiveTime t p.2 ≤ (p.2.1 : ℝ) then
      f (c.chart (p.1, collarHEPRadius t p.2))
    else K (collarHEPVerticalTime t p.2, p.1)) = f (c.chart p)
  have hcut : collarHEPCutoff p.2 = 0 := collarHEPCutoff_eq_zero_of_half_le hp
  have heff : collarHEPEffectiveTime t p.2 = 0 := by
    simp [collarHEPEffectiveTime, hcut]
  rw [if_pos (heff.trans_le p.2.1.2.1), collarHEPRadius_eq_self_of_half_le t hp]

end LocalExtension

/-! ## A compactly supported ambient extension -/

/-- The compact interval used to close off the support of the collar construction. -/
public abbrev CollarHEPDeepParameter := Set.Icc (0 : ℝ) (1 / 2 : ℝ)

/-- Regard a parameter in `[0,1/2]` as a point of the half-open collar. -/
public def collarHEPDeepToHalf (r : CollarHEPDeepParameter) : HalfCollarParameter :=
  ⟨⟨(r : ℝ), ⟨r.2.1, r.2.2.trans (by norm_num)⟩⟩,
    r.2.2.trans_lt (by norm_num)⟩

public theorem continuous_collarHEPDeepToHalf : Continuous collarHEPDeepToHalf := by
  exact ((continuous_subtype_val.subtype_mk _).subtype_mk _)

section AmbientExtension

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hmodel : Type uH} [TopologicalSpace Hmodel]
  {I : ModelWithCorners ℝ E Hmodel}
  {M W Y : Type u}
  [TopologicalSpace M] [ChartedSpace Hmodel M] [IsManifold I ∞ M]
  [TopologicalSpace W]
  [ChartedSpace (ModelProd Hmodel (EuclideanHalfSpace 1)) W]
  [TopologicalSpace Y]

/-- The closed half-depth subcollar, parametrized by the compact product `M × [0,1/2]`. -/
public def collarHEPDeepMap (c : SmoothCollar I M W) :
    M × CollarHEPDeepParameter → W :=
  fun p ↦ c.chart (p.1, collarHEPDeepToHalf p.2)

public theorem continuous_collarHEPDeepMap (c : SmoothCollar I M W) :
    Continuous (collarHEPDeepMap c) := by
  exact c.chart.contMDiff.continuous.comp
    (continuous_fst.prodMk (continuous_collarHEPDeepToHalf.comp continuous_snd))

/-- Image of the closed half-depth subcollar in the ambient space. -/
public def collarHEPDeepSet (c : SmoothCollar I M W) : Set W :=
  range (collarHEPDeepMap c)

public theorem collarHEPDeepSet_subset_target (c : SmoothCollar I M W) :
    collarHEPDeepSet c ⊆ c.chart.target := by
  rintro w ⟨p, rfl⟩
  exact (c.chart.toDiffeomorph (p.1, collarHEPDeepToHalf p.2)).2

public theorem isCompact_collarHEPDeepSet [CompactSpace M]
    (c : SmoothCollar I M W) : IsCompact (collarHEPDeepSet c) := by
  simpa only [collarHEPDeepSet, image_univ] using
    (isCompact_univ.image (continuous_collarHEPDeepMap c))

public theorem isClosed_collarHEPDeepSet [CompactSpace M] [T2Space W]
    (c : SmoothCollar I M W) : IsClosed (collarHEPDeepSet c) :=
  (isCompact_collarHEPDeepSet c).isClosed

/-- A collar point of depth at most `1/2` belongs to the compact deep subcollar. -/
public theorem mem_collarHEPDeepSet_of_targetCoordinate_le
    (c : SmoothCollar I M W) (w : W) (hw : w ∈ c.chart.target)
    (hdeep : ((c.chart.toDiffeomorph.symm ⟨w, hw⟩).2.1 : ℝ) ≤ 1 / 2) :
    w ∈ collarHEPDeepSet c := by
  let q : CollarSource M := c.chart.toDiffeomorph.symm ⟨w, hw⟩
  let r : CollarHEPDeepParameter :=
    ⟨(q.2.1 : ℝ), q.2.1.2.1, hdeep⟩
  refine ⟨(q.1, r), ?_⟩
  have hr : collarHEPDeepToHalf r = q.2 := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  change c.chart (q.1, collarHEPDeepToHalf r) = w
  rw [hr]
  exact congrArg Subtype.val (c.chart.toDiffeomorph.apply_symm_apply ⟨w, hw⟩)

/-- The extension on the whole ambient cylinder.  Outside the collar chart it is the original
map.  The collar formula already becomes the original map before reaching the chart frontier. -/
public def collarAmbientHomotopyExtension
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁) :
    unitInterval × W → Y := by
  classical
  exact fun p ↦
    if hw : p.2 ∈ c.chart.target then
      collarLocalHomotopyExtension c f K
        (p.1, c.chart.toDiffeomorph.symm ⟨p.2, hw⟩)
    else
      f p.2

public theorem collarAmbientHomotopyExtension_of_mem_target
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (p : unitInterval × W) (hp : p.2 ∈ c.chart.target) :
    collarAmbientHomotopyExtension c f K p =
      collarLocalHomotopyExtension c f K
        (p.1, c.chart.toDiffeomorph.symm ⟨p.2, hp⟩) := by
  simp only [collarAmbientHomotopyExtension, dif_pos hp]

public theorem collarAmbientHomotopyExtension_of_not_mem_target
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (p : unitInterval × W) (hp : p.2 ∉ c.chart.target) :
    collarAmbientHomotopyExtension c f K p = f p.2 := by
  simp only [collarAmbientHomotopyExtension, dif_neg hp]

/-- The open part of the ambient cylinder lying over the collar target. -/
public def collarHEPCylinderTarget (c : SmoothCollar I M W) : Set (unitInterval × W) :=
  Prod.snd ⁻¹' (c.chart.target : Set W)

public theorem isOpen_collarHEPCylinderTarget (c : SmoothCollar I M W) :
    IsOpen (collarHEPCylinderTarget c) :=
  c.chart.target.isOpen.preimage continuous_snd

/-- Collar coordinates on the open cylinder above the collar target. -/
public def collarHEPCylinderCoordinates (c : SmoothCollar I M W) :
    collarHEPCylinderTarget c → unitInterval × CollarSource M :=
  fun p ↦
    (p.1.1, c.chart.toDiffeomorph.symm ⟨p.1.2, p.2⟩)

public theorem continuous_collarHEPCylinderCoordinates (c : SmoothCollar I M W) :
    Continuous (collarHEPCylinderCoordinates c) := by
  have htarget : Continuous (fun p : collarHEPCylinderTarget c ↦
      (⟨p.1.2, p.2⟩ : c.chart.target)) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    (c.chart.toDiffeomorph.contMDiff_invFun.continuous.comp htarget)

public theorem collarAmbientHomotopyExtension_continuousOn_target
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁) :
    ContinuousOn (collarAmbientHomotopyExtension c f K) (collarHEPCylinderTarget c) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hlocal := (continuous_collarLocalHomotopyExtension c f K).comp
    (continuous_collarHEPCylinderCoordinates c)
  apply hlocal.congr
  intro p
  exact (collarAmbientHomotopyExtension_of_mem_target c f K p.1 p.2).symm

public theorem collarAmbientHomotopyExtension_eq_bottom_of_not_mem_deep
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (p : unitInterval × W) (hp : p.2 ∉ collarHEPDeepSet c) :
    collarAmbientHomotopyExtension c f K p = f p.2 := by
  by_cases htarget : p.2 ∈ c.chart.target
  · rw [collarAmbientHomotopyExtension_of_mem_target c f K p htarget]
    let q : CollarSource M := c.chart.toDiffeomorph.symm ⟨p.2, htarget⟩
    have hnotle : ¬ ((q.2.1 : ℝ) ≤ 1 / 2) := by
      intro hle
      exact hp (mem_collarHEPDeepSet_of_targetCoordinate_le c p.2 htarget hle)
    have hhalf : (1 / 2 : ℝ) ≤ (q.2.1 : ℝ) := le_of_lt (lt_of_not_ge hnotle)
    rw [collarLocalHomotopyExtension_eq_bottom_of_half_le c f K p.1 q hhalf]
    exact congrArg f
      (congrArg Subtype.val (c.chart.toDiffeomorph.apply_symm_apply ⟨p.2, htarget⟩))
  · exact collarAmbientHomotopyExtension_of_not_mem_target c f K p htarget

public theorem continuous_collarAmbientHomotopyExtension [CompactSpace M] [T2Space W]
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁) :
    Continuous (collarAmbientHomotopyExtension c f K) := by
  let U : Set (unitInterval × W) := collarHEPCylinderTarget c
  let V : Set (unitInterval × W) := Prod.snd ⁻¹' (collarHEPDeepSet c)ᶜ
  have hUopen : IsOpen U := isOpen_collarHEPCylinderTarget c
  have hVopen : IsOpen V :=
    (isClosed_collarHEPDeepSet c).isOpen_compl.preimage continuous_snd
  have hU : ContinuousOn (collarAmbientHomotopyExtension c f K) U :=
    collarAmbientHomotopyExtension_continuousOn_target c f K
  have hV : ContinuousOn (collarAmbientHomotopyExtension c f K) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hbottom : Continuous (fun p : V ↦ f p.1.2) :=
      f.continuous.comp (continuous_snd.comp continuous_subtype_val)
    apply hbottom.congr
    intro p
    exact (collarAmbientHomotopyExtension_eq_bottom_of_not_mem_deep c f K p.1 p.2).symm
  have hcover : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : p.2 ∈ c.chart.target
    · exact Or.inl hp
    · apply Or.inr
      intro hdeep
      exact hp (collarHEPDeepSet_subset_target c hdeep)
  rw [← continuousOn_univ, ← hcover]
  exact hU.union_of_isOpen hV hUopen hVopen

@[simp]
public theorem collarAmbientHomotopyExtension_zero [CompactSpace M] [T2Space W]
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (w : W) : collarAmbientHomotopyExtension c f K (0, w) = f w := by
  by_cases hw : w ∈ c.chart.target
  · rw [collarAmbientHomotopyExtension_of_mem_target c f K (0, w) hw,
      collarLocalHomotopyExtension_zero]
    exact congrArg f
      (congrArg Subtype.val (c.chart.toDiffeomorph.apply_symm_apply ⟨w, hw⟩))
  · exact collarAmbientHomotopyExtension_of_not_mem_target c f K (0, w) hw

@[simp]
public theorem collarAmbientHomotopyExtension_zeroSection [CompactSpace M] [T2Space W]
    (c : SmoothCollar I M W) (f : C(W, Y)) {h₁ : C(M, Y)}
    (K : ContinuousMap.Homotopy (f.comp ⟨c.inclusion, c.inclusion_contMDiff.continuous⟩) h₁)
    (t : unitInterval) (m : M) :
    collarAmbientHomotopyExtension c f K (t, c.inclusion m) = K (t, m) := by
  have hw : c.inclusion m ∈ c.chart.target :=
    (c.chart.toDiffeomorph (collarSourceZeroSection M m)).2
  rw [collarAmbientHomotopyExtension_of_mem_target c f K _ hw]
  have hinv : c.chart.toDiffeomorph.symm ⟨c.inclusion m, hw⟩ =
      collarSourceZeroSection M m := by
    exact c.chart.toDiffeomorph.symm_apply_apply _
  rw [hinv, collarLocalHomotopyExtension_zeroSection]

end AmbientExtension

/-! ## The collar HEP theorem -/

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hmodel : Type uH} [TopologicalSpace Hmodel]
  {I : ModelWithCorners ℝ E Hmodel}
  {M W : Type u}
  [TopologicalSpace M] [ChartedSpace Hmodel M] [IsManifold I ∞ M]
  [CompactSpace M]
  [TopologicalSpace W] [T2Space W]
  [ChartedSpace (ModelProd Hmodel (EuclideanHalfSpace 1)) W]

/-- The zero section of a compact collar in a Hausdorff ambient space has the homotopy-extension
property.  The proof is the explicit compactly-supported L-shaped cylinder retraction above; it
does not appeal to an assumed cofibration theorem. -/
public theorem SmoothCollar.homotopyExtensionProperty
    (c : SmoothCollar I M W) :
    HomotopyExtensionProperty (collarAmbientZeroSection c).hom := by
  change HomotopyExtensionProperty
    (⟨c.inclusion, c.inclusion_contMDiff.continuous⟩ : C(M, W))
  refine ⟨?_⟩
  intro Y _ f h₁ K
  let G : C(unitInterval × W, Y) :=
    ⟨collarAmbientHomotopyExtension c f K,
      continuous_collarAmbientHomotopyExtension c f K⟩
  let f₁ : C(W, Y) := cylinderSlice G 1
  let F : ContinuousMap.Homotopy f f₁ :=
    { toContinuousMap := G
      map_zero_left := fun w ↦ collarAmbientHomotopyExtension_zero c f K w
      map_one_left := fun _ ↦ rfl }
  refine ⟨f₁, F, ?_⟩
  intro t m
  exact collarAmbientHomotopyExtension_zeroSection c f K t m

/-- Unnamespaced spelling of the collar HEP theorem, convenient at gluing call sites. -/
public theorem homotopyExtensionProperty_collarAmbientZeroSection
    (c : SmoothCollar I M W) :
    HomotopyExtensionProperty (collarAmbientZeroSection c).hom :=
  c.homotopyExtensionProperty

/-- A homotopy-equivalent compact collar inclusion is a strong deformation retract of its whole
ambient space.  This is the relative coherence needed by pushout gluing. -/
public theorem SmoothCollar.exists_ambientStrongDeformationRetract
    (c : SmoothCollar I M W) (hi : IsHomotopyEquivalence c.inclusion) :
    Nonempty (TopCat.StrongDeformationRetractData (collarAmbientZeroSection c)) := by
  exact c.homotopyExtensionProperty.exists_strongDeformationRetractData hi

end SphereSixComplex
