module

public import SphereSixComplex.Periods.Uniformization.ScalarContinuationCover
import all SphereSixComplex.Periods.Uniformization.ScalarContinuationCover
public import TauCeti.Analysis.Complex.Conformal.GlobalBranch
import all TauCeti.Analysis.Complex.Conformal.GlobalBranch

@[expose] public section

/-!
# Monodromy assembly of the global scalar branch

This file isolates the remaining analytic-continuation obligation.  Once the scalar chamber germ
continues along every path in the upper half-plane, Tau Ceti's global-branch theorem produces a
single holomorphic scalar function there.  The identity principle then identifies that branch
with the original seed throughout the open source chamber.
-/

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.Periods.TriangleReflections

/-- A fixed honest point in the source reflection chamber. -/
def sourceScalarContinuationBase : ℂ := 2 * Complex.I

theorem sourceScalarContinuationBase_mem_sourceOpenChamber :
    sourceScalarContinuationBase ∈ sourceOpenChamber := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num [sourceScalarContinuationBase, sourceOpenChamber, normSq_apply]
  linarith

theorem sourceScalarContinuationBase_mem_sourceUpperHalfPlaneSet :
    sourceScalarContinuationBase ∈ sourceUpperHalfPlaneSet :=
  sourceScalarContinuationBase_mem_sourceOpenChamber.2.2.1

theorem sourceUpperHalfPlaneSet_convex : Convex ℝ sourceUpperHalfPlaneSet :=
  convex_halfSpace_im_gt 0

theorem sourceUpperHalfPlaneSet_isSimplyConnected :
    IsSimplyConnected sourceUpperHalfPlaneSet := by
  letI : ContractibleSpace sourceUpperHalfPlaneSet :=
    sourceUpperHalfPlaneSet_convex.contractibleSpace
      ⟨sourceScalarContinuationBase,
        sourceScalarContinuationBase_mem_sourceUpperHalfPlaneSet⟩
  show SimplyConnectedSpace sourceUpperHalfPlaneSet
  infer_instance

private theorem sourceOpenChamber_subset_sourceUpperHalfPlaneSet :
    sourceOpenChamber ⊆ sourceUpperHalfPlaneSet := fun _ hz => hz.2.2.1

private theorem sourceScalarTriangleMap_differentiableOn_sourceOpenChamber
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarTriangleMap S) sourceOpenChamber :=
  (sourceScalarOpenChamberMap_differentiableOn S
    (sourceOrderThreeCircle_ne_otherElliptic S)).congr
      (fun z hz => sourceScalarTriangleMap_eq_open_of_mem S hz)

/-- A global scalar branch supplied by Tau Ceti monodromy, together with its prescribed initial
germ and agreement with the chamber seed on the whole open source triangle. -/
structure MonodromyScalarBranch
    (S : ChamberCaratheodorySeed sourceBoundedChamber) where
  scalar : ℂ → ℂ
  analyticOn : AnalyticOnNhd ℂ scalar sourceUpperHalfPlaneSet
  initialGerm : scalar =ᶠ[𝓝 sourceScalarContinuationBase] sourceScalarTriangleMap S
  eqOn_seed : EqOn scalar (sourceScalarTriangleMap S) sourceOpenChamber

/-- `ContinuesInside` is the one remaining input needed to construct the global holomorphic
branch. -/
noncomputable def monodromyScalarBranchOfContinuesInside
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (H : TauCeti.ContinuesInside (sourceScalarTriangleMap S)
      sourceUpperHalfPlaneSet sourceScalarContinuationBase) :
    MonodromyScalarBranch S := by
  let hex := H.exists_analyticOnNhd
    sourceUpperHalfPlaneSet_isOpen sourceUpperHalfPlaneSet_isSimplyConnected
    sourceScalarContinuationBase_mem_sourceUpperHalfPlaneSet
  let F : ℂ → ℂ := Classical.choose hex
  have hF : AnalyticOnNhd ℂ F sourceUpperHalfPlaneSet := (Classical.choose_spec hex).1
  have hFseed : F =ᶠ[𝓝 sourceScalarContinuationBase] sourceScalarTriangleMap S :=
    (Classical.choose_spec hex).2
  refine ⟨F, hF, hFseed, ?_⟩
  have hFchamber : AnalyticOnNhd ℂ F sourceOpenChamber :=
    hF.mono (fun _ hz => hz.2.2.1)
  have hseed : AnalyticOnNhd ℂ (sourceScalarTriangleMap S) sourceOpenChamber :=
    ((sourceScalarOpenChamberMap_differentiableOn S
        (sourceOrderThreeCircle_ne_otherElliptic S)).congr
          (fun z hz => sourceScalarTriangleMap_eq_open_of_mem S hz)).analyticOnNhd
      sourceOpenChamber_isOpen
  exact hFchamber.eqOn_of_preconnected_of_eventuallyEq hseed
    sourceOpenChamber_isSimplyConnected.isPathConnected.isConnected.isPreconnected
    sourceScalarContinuationBase_mem_sourceOpenChamber hFseed

namespace MonodromyScalarBranch

variable {S : ChamberCaratheodorySeed sourceBoundedChamber} (B : MonodromyScalarBranch S)

theorem differentiableOn :
    DifferentiableOn ℂ B.scalar sourceUpperHalfPlaneSet := B.analyticOn.differentiableOn

/-! ## The right reflection law -/

def sourceRightSeamPoint : ℂ := (1 / 2 : ℂ) + 2 * Complex.I

theorem sourceRightSeamPoint_mem_sourceRightDouble :
    sourceRightSeamPoint ∈ sourceRightDouble := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num [sourceRightSeamPoint, sourceRightDouble, sourceRight, normSq_apply]
  constructor <;> nlinarith

theorem sourceRightSeamPoint_mem_sourceUpperHalfPlaneSet :
    sourceRightSeamPoint ∈ sourceUpperHalfPlaneSet := by
  norm_num [sourceRightSeamPoint, sourceUpperHalfPlaneSet]

theorem sourceRight_sourceRightSeamPoint :
    sourceRight sourceRightSeamPoint = sourceRightSeamPoint := by
  apply Complex.ext <;> norm_num [sourceRight, sourceRightSeamPoint]

theorem sourceRightSeamPoint_mem_closure_sourceOpenChamber :
    sourceRightSeamPoint ∈ closure sourceOpenChamber := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 4)
  let z : ℂ := ((1 / 2 - δ : ℝ) : ℂ) + 2 * Complex.I
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδle : δ ≤ 1 / 4 := min_le_right _ _
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨z, ?_, ?_⟩
  · norm_num [z, sourceOpenChamber, normSq_apply]
    refine ⟨by nlinarith, hδpos, ?_⟩
    nlinarith [sq_nonneg (1 / 2 - δ)]
  · rw [dist_eq]
    have hdiff : sourceRightSeamPoint - z = (δ : ℂ) := by
      apply Complex.ext <;> simp [z, sourceRightSeamPoint] <;> ring
    rw [hdiff, norm_real, Real.norm_eq_abs, abs_of_nonneg hδpos.le]
    exact hδε

/-- The monodromy branch and the explicit right Schwarz double have the same germ at a regular
point of the right seam. -/
theorem eventuallyEq_sourceScalarRightDoubleMap_at_rightSeam :
    B.scalar =ᶠ[𝓝 sourceRightSeamPoint] sourceScalarRightDoubleMap S := by
  have hB : AnalyticAt ℂ B.scalar sourceRightSeamPoint :=
    B.analyticOn sourceRightSeamPoint sourceRightSeamPoint_mem_sourceUpperHalfPlaneSet
  have hR : AnalyticAt ℂ (sourceScalarRightDoubleMap S) sourceRightSeamPoint :=
    (sourceScalarRightDoubleMap_differentiableOn S).analyticAt
      (sourceRightDouble_isOpen.mem_nhds sourceRightSeamPoint_mem_sourceRightDouble)
  apply (hB.frequently_eq_iff_eventually_eq hR).mp
  apply mem_closure_ne_iff_frequently_within.mp
  apply closure_mono (s := sourceOpenChamber)
  · intro z hz
    refine ⟨?_, ?_⟩
    · exact (B.eqOn_seed hz).trans (sourceScalarRightDoubleMap_eq_seed S hz).symm
    · intro h
      subst z
      exact (ne_of_lt hz.2.1) (by norm_num [sourceRightSeamPoint])
  · exact sourceRightSeamPoint_mem_closure_sourceOpenChamber

private theorem sourceRight_preimage_sourceUpperHalfPlaneSet :
    sourceRight ⁻¹' sourceUpperHalfPlaneSet = sourceUpperHalfPlaneSet := by
  ext z
  simp [sourceUpperHalfPlaneSet]

private theorem rightReflectedScalar_analyticOn :
    AnalyticOnNhd ℂ (rightReflectedScalarMap B.scalar) sourceUpperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd
  · rw [← sourceRight_preimage_sourceUpperHalfPlaneSet]
    exact differentiableOn_rightReflectedScalarMap sourceUpperHalfPlaneSet_isOpen B.differentiableOn
  · exact sourceUpperHalfPlaneSet_isOpen

/-- The global branch obeys the right-side scalar Schwarz law throughout the upper half-plane. -/
theorem reflection_right {z : ℂ} (hz : z ∈ sourceUpperHalfPlaneSet) :
    B.scalar (sourceRight z) = (starRingEnd ℂ) (B.scalar z) := by
  have hlocal := B.eventuallyEq_sourceScalarRightDoubleMap_at_rightSeam
  have hsource : Tendsto sourceRight (𝓝 sourceRightSeamPoint)
      (𝓝 sourceRightSeamPoint) := by
    have hc : Continuous sourceRight := by
      unfold sourceRight
      fun_prop
    have h : ContinuousAt sourceRight sourceRightSeamPoint := hc.continuousAt
    change Tendsto sourceRight (𝓝 sourceRightSeamPoint)
      (𝓝 (sourceRight sourceRightSeamPoint)) at h
    rwa [sourceRight_sourceRightSeamPoint] at h
  have hlocalSource :
      (fun w => B.scalar (sourceRight w)) =ᶠ[𝓝 sourceRightSeamPoint]
        (fun w => sourceScalarRightDoubleMap S (sourceRight w)) :=
    hlocal.comp_tendsto hsource
  have hrightLaw : rightReflectedScalarMap B.scalar =ᶠ[𝓝 sourceRightSeamPoint] B.scalar := by
    filter_upwards [hlocal, hlocalSource,
      sourceRightDouble_isOpen.mem_nhds sourceRightSeamPoint_mem_sourceRightDouble]
      with w hw hwSource hwDouble
    calc
      rightReflectedScalarMap B.scalar w =
          (starRingEnd ℂ) (B.scalar (sourceRight w)) := rfl
      _ = (starRingEnd ℂ) (sourceScalarRightDoubleMap S (sourceRight w)) :=
        congrArg (starRingEnd ℂ) hwSource
      _ = sourceScalarRightDoubleMap S w := by
        rw [sourceScalarRightDoubleMap_reflection S hwDouble]
        simp
      _ = B.scalar w := hw.symm
  have hglobal := rightReflectedScalar_analyticOn B |>.eqOn_of_preconnected_of_eventuallyEq
    B.analyticOn sourceUpperHalfPlaneSet_convex.isPreconnected
      sourceRightSeamPoint_mem_sourceUpperHalfPlaneSet hrightLaw
  have heq := hglobal hz
  have hconj := congrArg (starRingEnd ℂ) heq
  simpa only [rightReflectedScalarMap, starRingEnd_self_apply] using hconj

/-! ## The left reflection law -/

def sourceLeftSeamPoint : ℂ := ((-(Real.sqrt 2) / 2 : ℝ) : ℂ) + 2 * Complex.I

theorem sourceLeftSeamPoint_mem_sourceLeftDouble :
    sourceLeftSeamPoint ∈ sourceLeftDouble := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [sourceLeftSeamPoint]
    nlinarith
  · norm_num [sourceLeftSeamPoint]
    nlinarith
  · norm_num [sourceLeftSeamPoint]
  · rw [normSq_apply]
    norm_num [sourceLeftSeamPoint]
    nlinarith
  · rw [sourceLeft_normSq]
    norm_num [sourceLeftSeamPoint]
    nlinarith

theorem sourceLeftSeamPoint_mem_sourceUpperHalfPlaneSet :
    sourceLeftSeamPoint ∈ sourceUpperHalfPlaneSet := by
  norm_num [sourceLeftSeamPoint, sourceUpperHalfPlaneSet]

theorem sourceLeft_sourceLeftSeamPoint :
    sourceLeft sourceLeftSeamPoint = sourceLeftSeamPoint := by
  apply Complex.ext
  · rw [sourceLeft_re]
    norm_num [sourceLeftSeamPoint]
    ring
  · exact sourceLeft_im sourceLeftSeamPoint

theorem sourceLeftSeamPoint_mem_closure_sourceOpenChamber :
    sourceLeftSeamPoint ∈ closure sourceOpenChamber := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 4)
  let z : ℂ := ((-(Real.sqrt 2) / 2 + δ : ℝ) : ℂ) + 2 * Complex.I
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδle : δ ≤ 1 / 4 := min_le_right _ _
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨z, ?_, ?_⟩
  · norm_num [z, sourceOpenChamber, normSq_apply]
    refine ⟨hδpos, ?_, ?_⟩
    · nlinarith
    · nlinarith [sq_nonneg (-(Real.sqrt 2) / 2 + δ)]
  · rw [dist_eq]
    have hdiff : sourceLeftSeamPoint - z = (-δ : ℂ) := by
      apply Complex.ext <;> simp [z, sourceLeftSeamPoint]
    rw [hdiff, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg hδpos.le]
    exact hδε

/-- Conjugating a holomorphic function by the affine left reflection is holomorphic. -/
def leftReflectedScalarMap (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (F (sourceLeft z))

theorem differentiableOn_leftReflectedScalarMap {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (leftReflectedScalarMap F) (sourceLeft ⁻¹' U) := by
  intro z hz
  have hFat : DifferentiableAt ℂ F (sourceLeft z) :=
    (hF _ hz).differentiableAt (hU.mem_nhds hz)
  let H : ℂ → ℂ := fun u => F (-(Real.sqrt 2 : ℂ) - u)
  have hHat : DifferentiableAt ℂ H ((starRingEnd ℂ) z) := by
    apply hFat.comp ((starRingEnd ℂ) z)
    fun_prop
  have hc := hHat.conj_conj
  change DifferentiableWithinAt ℂ
    (fun y : ℂ => (starRingEnd ℂ)
      (F (-(Real.sqrt 2 : ℂ) - (starRingEnd ℂ) y)))
    (sourceLeft ⁻¹' U) z
  simpa only [Function.comp_def, H, starRingEnd_self_apply] using hc.differentiableWithinAt

private theorem sourceLeft_preimage_sourceUpperHalfPlaneSet :
    sourceLeft ⁻¹' sourceUpperHalfPlaneSet = sourceUpperHalfPlaneSet := by
  ext z
  simp [sourceUpperHalfPlaneSet, sourceLeft]

private theorem leftReflectedScalar_analyticOn :
    AnalyticOnNhd ℂ (leftReflectedScalarMap B.scalar) sourceUpperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd
  · rw [← sourceLeft_preimage_sourceUpperHalfPlaneSet]
    exact differentiableOn_leftReflectedScalarMap sourceUpperHalfPlaneSet_isOpen B.differentiableOn
  · exact sourceUpperHalfPlaneSet_isOpen

theorem eventuallyEq_sourceScalarLeftDoubleMap_at_leftSeam :
    B.scalar =ᶠ[𝓝 sourceLeftSeamPoint] sourceScalarLeftDoubleMap S := by
  have hB : AnalyticAt ℂ B.scalar sourceLeftSeamPoint :=
    B.analyticOn sourceLeftSeamPoint sourceLeftSeamPoint_mem_sourceUpperHalfPlaneSet
  have hL : AnalyticAt ℂ (sourceScalarLeftDoubleMap S) sourceLeftSeamPoint :=
    (sourceScalarLeftDoubleMap_differentiableOn S).analyticAt
      (sourceLeftDouble_isOpen.mem_nhds sourceLeftSeamPoint_mem_sourceLeftDouble)
  apply (hB.frequently_eq_iff_eventually_eq hL).mp
  apply mem_closure_ne_iff_frequently_within.mp
  apply closure_mono (s := sourceOpenChamber)
  · intro z hz
    refine ⟨?_, ?_⟩
    · exact (B.eqOn_seed hz).trans (sourceScalarLeftDoubleMap_eq_seed S hz).symm
    · intro h
      subst z
      exact (ne_of_lt hz.1) (by simp [sourceLeftSeamPoint])
  · exact sourceLeftSeamPoint_mem_closure_sourceOpenChamber

/-- The global branch obeys the left-side scalar Schwarz law throughout the upper half-plane. -/
theorem reflection_left {z : ℂ} (hz : z ∈ sourceUpperHalfPlaneSet) :
    B.scalar (sourceLeft z) = (starRingEnd ℂ) (B.scalar z) := by
  have hlocal := B.eventuallyEq_sourceScalarLeftDoubleMap_at_leftSeam
  have hsource : Tendsto sourceLeft (𝓝 sourceLeftSeamPoint)
      (𝓝 sourceLeftSeamPoint) := by
    have hc : Continuous sourceLeft := by
      unfold sourceLeft
      fun_prop
    have h : ContinuousAt sourceLeft sourceLeftSeamPoint := hc.continuousAt
    change Tendsto sourceLeft (𝓝 sourceLeftSeamPoint)
      (𝓝 (sourceLeft sourceLeftSeamPoint)) at h
    rwa [sourceLeft_sourceLeftSeamPoint] at h
  have hlocalSource :
      (fun w => B.scalar (sourceLeft w)) =ᶠ[𝓝 sourceLeftSeamPoint]
        (fun w => sourceScalarLeftDoubleMap S (sourceLeft w)) :=
    hlocal.comp_tendsto hsource
  have hleftLaw : leftReflectedScalarMap B.scalar =ᶠ[𝓝 sourceLeftSeamPoint] B.scalar := by
    filter_upwards [hlocal, hlocalSource,
      sourceLeftDouble_isOpen.mem_nhds sourceLeftSeamPoint_mem_sourceLeftDouble]
      with w hw hwSource hwDouble
    calc
      leftReflectedScalarMap B.scalar w =
          (starRingEnd ℂ) (B.scalar (sourceLeft w)) := rfl
      _ = (starRingEnd ℂ) (sourceScalarLeftDoubleMap S (sourceLeft w)) :=
        congrArg (starRingEnd ℂ) hwSource
      _ = sourceScalarLeftDoubleMap S w := by
        rw [sourceScalarLeftDoubleMap_reflection S hwDouble]
        simp
      _ = B.scalar w := hw.symm
  have hglobal := leftReflectedScalar_analyticOn B |>.eqOn_of_preconnected_of_eventuallyEq
    B.analyticOn sourceUpperHalfPlaneSet_convex.isPreconnected
      sourceLeftSeamPoint_mem_sourceUpperHalfPlaneSet hleftLaw
  have heq := hglobal hz
  have hconj := congrArg (starRingEnd ℂ) heq
  simpa only [leftReflectedScalarMap, starRingEnd_self_apply] using hconj

/-! ## The circular reflection law -/

def sourceCircleSeamPoint : ℂ := Complex.I

theorem sourceCircleSeamPoint_mem_sourceCircleDouble :
    sourceCircleSeamPoint ∈ sourceCircleDouble := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num [sourceCircleSeamPoint, sourceCircleDouble, normSq_apply]
  nlinarith

theorem sourceCircleSeamPoint_mem_sourceUpperHalfPlaneSet :
    sourceCircleSeamPoint ∈ sourceUpperHalfPlaneSet := by
  norm_num [sourceCircleSeamPoint, sourceUpperHalfPlaneSet]

theorem sourceCircle_sourceCircleSeamPoint :
    sourceCircle sourceCircleSeamPoint = sourceCircleSeamPoint := by
  norm_num [sourceCircle, sourceCircleSeamPoint]

theorem sourceCircleSeamPoint_mem_closure_sourceOpenChamber :
    sourceCircleSeamPoint ∈ closure sourceOpenChamber := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 4)
  let z : ℂ := ((1 + δ : ℝ) : ℂ) * Complex.I
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨z, ?_, ?_⟩
  · norm_num [z, sourceOpenChamber, normSq_apply]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    nlinarith [sq_nonneg δ]
  · rw [dist_eq]
    have hdiff : sourceCircleSeamPoint - z = (-δ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [z, sourceCircleSeamPoint]
    rw [hdiff, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hδpos.le]
    simpa using hδε

def circleReflectedScalarMap (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (F (sourceCircle z))

private theorem circleReflectedScalar_analyticOn :
    AnalyticOnNhd ℂ (circleReflectedScalarMap B.scalar) sourceUpperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num [sourceUpperHalfPlaneSet] at hz
    have hcircle : sourceCircle z ∈ sourceUpperHalfPlaneSet := by
      change 0 < (sourceCircle z).im
      rw [sourceCircle_im]
      exact div_pos hz (Complex.normSq_pos.mpr hz0)
    have hFat : DifferentiableAt ℂ B.scalar (sourceCircle z) :=
      (B.differentiableOn _ hcircle).differentiableAt
        (sourceUpperHalfPlaneSet_isOpen.mem_nhds hcircle)
    let H : ℂ → ℂ := fun u => B.scalar u⁻¹
    have hconj0 : (starRingEnd ℂ) z ≠ 0 := by
      intro h
      apply hz0
      have h' := congrArg (starRingEnd ℂ) h
      simpa using h'
    have hHat : DifferentiableAt ℂ H ((starRingEnd ℂ) z) := by
      apply hFat.comp ((starRingEnd ℂ) z)
      exact differentiableAt_inv hconj0
    have hc := hHat.conj_conj
    change DifferentiableWithinAt ℂ
      (fun y : ℂ => (starRingEnd ℂ)
        (B.scalar ((starRingEnd ℂ) y)⁻¹)) sourceUpperHalfPlaneSet z
    simpa only [Function.comp_def, H, starRingEnd_self_apply] using
      hc.differentiableWithinAt
  · exact sourceUpperHalfPlaneSet_isOpen

theorem eventuallyEq_sourceScalarCircleDoubleMap_at_circleSeam :
    B.scalar =ᶠ[𝓝 sourceCircleSeamPoint] sourceScalarCircleDoubleMap S := by
  have hB : AnalyticAt ℂ B.scalar sourceCircleSeamPoint :=
    B.analyticOn sourceCircleSeamPoint sourceCircleSeamPoint_mem_sourceUpperHalfPlaneSet
  have hC : AnalyticAt ℂ (sourceScalarCircleDoubleMap S) sourceCircleSeamPoint :=
    (sourceScalarCircleDoubleMap_differentiableOn S).analyticAt
      (sourceCircleDouble_isOpen.mem_nhds sourceCircleSeamPoint_mem_sourceCircleDouble)
  apply (hB.frequently_eq_iff_eventually_eq hC).mp
  apply mem_closure_ne_iff_frequently_within.mp
  apply closure_mono (s := sourceOpenChamber)
  · intro z hz
    refine ⟨?_, ?_⟩
    · exact (B.eqOn_seed hz).trans (sourceScalarCircleDoubleMap_eq_seed S hz).symm
    · intro h
      subst z
      exact (ne_of_lt hz.2.2.2) (by norm_num [sourceCircleSeamPoint, normSq_apply])
  · exact sourceCircleSeamPoint_mem_closure_sourceOpenChamber

/-- The global branch obeys the circular scalar Schwarz law throughout the upper half-plane. -/
theorem reflection_circle {z : ℂ} (hz : z ∈ sourceUpperHalfPlaneSet) :
    B.scalar (sourceCircle z) = (starRingEnd ℂ) (B.scalar z) := by
  have hlocal := B.eventuallyEq_sourceScalarCircleDoubleMap_at_circleSeam
  have hsource : Tendsto sourceCircle (𝓝 sourceCircleSeamPoint)
      (𝓝 sourceCircleSeamPoint) := by
    have hc : ContinuousAt sourceCircle sourceCircleSeamPoint := by
      unfold sourceCircle
      have hconj : ContinuousAt (starRingEnd ℂ) sourceCircleSeamPoint :=
        Complex.continuous_conj.continuousAt
      have hne : (starRingEnd ℂ) sourceCircleSeamPoint ≠ 0 := by
        norm_num [sourceCircleSeamPoint]
      exact hconj.inv₀ hne
    change Tendsto sourceCircle (𝓝 sourceCircleSeamPoint)
      (𝓝 (sourceCircle sourceCircleSeamPoint)) at hc
    rwa [sourceCircle_sourceCircleSeamPoint] at hc
  have hlocalSource :
      (fun w => B.scalar (sourceCircle w)) =ᶠ[𝓝 sourceCircleSeamPoint]
        (fun w => sourceScalarCircleDoubleMap S (sourceCircle w)) :=
    hlocal.comp_tendsto hsource
  have hcircleLaw :
      circleReflectedScalarMap B.scalar =ᶠ[𝓝 sourceCircleSeamPoint] B.scalar := by
    filter_upwards [hlocal, hlocalSource,
      sourceCircleDouble_isOpen.mem_nhds sourceCircleSeamPoint_mem_sourceCircleDouble]
      with w hw hwSource hwDouble
    calc
      circleReflectedScalarMap B.scalar w =
          (starRingEnd ℂ) (B.scalar (sourceCircle w)) := rfl
      _ = (starRingEnd ℂ) (sourceScalarCircleDoubleMap S (sourceCircle w)) :=
        congrArg (starRingEnd ℂ) hwSource
      _ = sourceScalarCircleDoubleMap S w := by
        rw [sourceScalarCircleDoubleMap_reflection S hwDouble]
        simp
      _ = B.scalar w := hw.symm
  have hglobal := circleReflectedScalar_analyticOn B |>.eqOn_of_preconnected_of_eventuallyEq
    B.analyticOn sourceUpperHalfPlaneSet_convex.isPreconnected
      sourceCircleSeamPoint_mem_sourceUpperHalfPlaneSet hcircleLaw
  have heq := hglobal hz
  have hconj := congrArg (starRingEnd ℂ) heq
  simpa only [circleReflectedScalarMap, starRingEnd_self_apply] using hconj

end MonodromyScalarBranch

/-! ## Algebraic orbit-representative assembly

This construction avoids arbitrary pairwise compatibility of a translated atlas.  It chooses one
representative of every source orbit in the explicit doubled fundamental region and evaluates the
right Schwarz double there.  One boundary-pairing consistency theorem makes the value independent
of the representative.  Local equality with the translated regular/corner patches is then the
only analytic obligation left.
-/

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover

/-- A chosen group element carrying an upper-half-plane point into the doubled fundamental
region. -/
noncomputable def sourceFundamentalTransport (z : UpperHalfPlane) : Delta :=
  Classical.choose (exists_smul_mem_orientedFundamentalRegion z)

/-- The corresponding chosen representative in the doubled fundamental region. -/
noncomputable def sourceFundamentalRepresentative (z : UpperHalfPlane) : UpperHalfPlane :=
  fuchsianSourceAction (sourceFundamentalTransport z) • z

theorem sourceFundamentalRepresentative_mem (z : UpperHalfPlane) :
    sourceFundamentalRepresentative z ∈ orientedFundamentalRegion :=
  Classical.choose_spec (exists_smul_mem_orientedFundamentalRegion z)

theorem sourceFundamentalRepresentative_orbit (z : UpperHalfPlane) :
    ∃ g : Delta, fuchsianSourceAction g • z = sourceFundamentalRepresentative z :=
  ⟨sourceFundamentalTransport z, rfl⟩

/-- The exact missing boundary-pairing statement for the orbit-representative construction.
The converse is `sourceScalarRightDoubleMap_fundamental_fibres`. -/
def SourceFundamentalScalarConsistent
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : Prop :=
  ∀ {z w : UpperHalfPlane}, z ∈ orientedFundamentalRegion →
    w ∈ orientedFundamentalRegion →
    (∃ g : Delta, fuchsianSourceAction g • z = w) →
      sourceScalarRightDoubleMap S (z : ℂ) = sourceScalarRightDoubleMap S (w : ℂ)

/-- The algebraically assembled scalar, extended by zero outside the upper half-plane. -/
noncomputable def orbitAssembledScalar
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then
    sourceScalarRightDoubleMap S
      (sourceFundamentalRepresentative (⟨z, hz⟩ : UpperHalfPlane) : ℂ)
  else 0

@[simp] theorem orbitAssembledScalar_apply_coe
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : UpperHalfPlane) :
    orbitAssembledScalar S (z : ℂ) =
      sourceScalarRightDoubleMap S (sourceFundamentalRepresentative z : ℂ) := by
  simp [orbitAssembledScalar, z.im_pos]

/-- Consistency makes the choice construction agree with the explicit double on the entire
closed doubled fundamental region. -/
theorem orbitAssembledScalar_eq_rightDouble_on_fundamental
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S)
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    orbitAssembledScalar S (z : ℂ) = sourceScalarRightDoubleMap S (z : ℂ) := by
  rw [orbitAssembledScalar_apply_coe]
  apply hconsistent (sourceFundamentalRepresentative_mem z) hz
  refine ⟨(sourceFundamentalTransport z)⁻¹, ?_⟩
  simp [sourceFundamentalRepresentative]

/-- The choice construction is source-group invariant before any analytic argument. -/
theorem orbitAssembledScalar_invariant
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (g : Delta)
    (z : UpperHalfPlane) :
    orbitAssembledScalar S ((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ) =
      orbitAssembledScalar S (z : ℂ) := by
  rw [orbitAssembledScalar_apply_coe, orbitAssembledScalar_apply_coe]
  apply hconsistent
    (sourceFundamentalRepresentative_mem (fuchsianSourceAction g • z))
    (sourceFundamentalRepresentative_mem z)
  refine ⟨sourceFundamentalTransport z * g⁻¹ *
    (sourceFundamentalTransport (fuchsianSourceAction g • z))⁻¹, ?_⟩
  simp [sourceFundamentalRepresentative, map_mul, mul_smul]

/-- The explicit fundamental-region range calculation makes the orbit-assembled scalar
surjective. -/
theorem orbitAssembledScalar_surjective
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    Function.Surjective (fun z : UpperHalfPlane => orbitAssembledScalar S (z : ℂ)) := by
  intro q
  obtain ⟨z, hz, hq⟩ :=
    sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion S q
  refine ⟨z, ?_⟩
  change orbitAssembledScalar S (z : ℂ) = q
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hz]
  exact hq

/-- Fundamental fibre separation plus consistency gives exact source-orbit fibres globally. -/
theorem orbitAssembledScalar_eq_iff_orbit
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z w : UpperHalfPlane) :
    orbitAssembledScalar S (z : ℂ) = orbitAssembledScalar S (w : ℂ) ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w := by
  constructor
  · intro hzw
    have hrep : sourceScalarRightDoubleMap S (sourceFundamentalRepresentative z : ℂ) =
        sourceScalarRightDoubleMap S (sourceFundamentalRepresentative w : ℂ) := by
      simpa only [orbitAssembledScalar_apply_coe] using hzw
    obtain ⟨k, hk⟩ := sourceScalarRightDoubleMap_fundamental_fibres S
      (sourceFundamentalRepresentative_mem z) (sourceFundamentalRepresentative_mem w) hrep
    refine ⟨(sourceFundamentalTransport w)⁻¹ * k * sourceFundamentalTransport z, ?_⟩
    simp only [map_mul, mul_smul, sourceFundamentalRepresentative] at hk ⊢
    rw [hk]
    simp
  · rintro ⟨g, rfl⟩
    exact (orbitAssembledScalar_invariant S hconsistent g z).symm

theorem orbitAssembledScalar_fuchsianOne
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    orbitAssembledScalar S (fuchsianOneFixedPoint : ℂ) = 0 := by
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent
    (Or.inl fuchsianOneFixedPoint_mem_fundamentalTriangle)]
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S
    fuchsianOneFixedPoint_mem_fundamentalTriangle.2.1]
  exact sourceScalarTriangleMap_fuchsianOne S

theorem orbitAssembledScalar_fuchsianTwo
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    orbitAssembledScalar S (fuchsianTwoFixedPoint : ℂ) = 1 := by
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent
    (Or.inl fuchsianTwoFixedPoint_mem_fundamentalTriangle)]
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S
    fuchsianTwoFixedPoint_mem_fundamentalTriangle.2.1]
  exact sourceScalarTriangleMap_fuchsianTwo S

/-- Local holomorphic representatives for the algebraically assembled orbit scalar.  The regular
fields are supplied by translated side doubles; the two elliptic orbit types are supplied by the
six/eight-sector corner germs (or equivalently their removable-singularity extensions). -/
structure OrbitAssembledScalarLocalPatches
    (S : ChamberCaratheodorySeed sourceBoundedChamber) where
  patch : UpperHalfPlane → ℂ → ℂ
  patch_analyticAt : ∀ z : UpperHalfPlane, AnalyticAt ℂ (patch z) (z : ℂ)
  eventuallyEq : ∀ z : UpperHalfPlane,
    orbitAssembledScalar S =ᶠ[𝓝 (z : ℂ)] patch z

namespace OrbitAssembledScalarLocalPatches

variable {S : ChamberCaratheodorySeed sourceBoundedChamber}
  (P : OrbitAssembledScalarLocalPatches S)

include P

theorem analyticOnNhd :
    AnalyticOnNhd ℂ (orbitAssembledScalar S) sourceUpperHalfPlaneSet := by
  intro z hz
  let w : UpperHalfPlane := ⟨z, hz⟩
  exact (patch_analyticAt P w).congr (eventuallyEq P w).symm

/-- Local translated regular/corner patches produce the actual Tau Ceti continuation witness. -/
theorem continuesInside (z₀ : ℂ) :
    TauCeti.ContinuesInside (orbitAssembledScalar S) sourceUpperHalfPlaneSet z₀ :=
  TauCeti.ContinuesInside.of_differentiableOn sourceUpperHalfPlaneSet_isOpen
    (analyticOnNhd P).differentiableOn

/-- At a base point of the source chamber, the orbit construction continues the original seed
germ itself. -/
theorem seed_continuesInside
    (hconsistent : SourceFundamentalScalarConsistent S) :
    TauCeti.ContinuesInside (sourceScalarTriangleMap S) sourceUpperHalfPlaneSet
      sourceScalarContinuationBase := by
  apply (continuesInside P sourceScalarContinuationBase).congr
  have hopen := sourceOpenChamber_isOpen.mem_nhds
    sourceScalarContinuationBase_mem_sourceOpenChamber
  filter_upwards [hopen] with z hz
  let w : UpperHalfPlane := ⟨z, hz.2.2.1⟩
  have hwfund : w ∈ orientedFundamentalRegion := by
    left
    exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.2⟩
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hwfund]
  exact sourceScalarRightDoubleMap_eq_seed S hz

end OrbitAssembledScalarLocalPatches


end SphereSixComplex.Periods.SourceChamberTopology
