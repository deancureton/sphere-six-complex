module

public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalFibres
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalFibres
public import SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
import all SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
public import Mathlib.NumberTheory.ModularForms.QExpansion
import all Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import all TauCeti.Analysis.Complex.Conformal.LocalDegree

@[expose] public section

/-!
# Exact scalar cusps from a periodic reciprocal

This file isolates the analytic final step in the scalar cusp argument.  A reciprocal scalar
which is periodic, holomorphic and zero at infinity descends to the completed cusp disc.  Local
injectivity of that descended reciprocal makes its zero simple, hence supplies exactly the
holomorphic unit required by `HasExactFuchsianCusp`.
-/

open Complex Filter Function Metric Set Topology UpperHalfPlane
open scoped Manifold Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.Periods.TriangleReflections

local notation "Iinfinity" => Filter.comap Complex.im Filter.atTop

/-- Eventual statements at complex imaginary infinity can be made uniform above one height. -/
theorem eventually_Iinfinity_iff {p : ℂ → Prop} :
    (∀ᶠ z in Iinfinity, p z) ↔ ∃ A : ℝ, ∀ z : ℂ, A < z.im → p z := by
  rw [(Filter.atTop_basis_Ioi.comap Complex.im).eventually_iff]
  simp only [true_and, mem_preimage, mem_Ioi]

/-- The completed cusp-disc representative of a periodic reciprocal scalar. -/
def scalarReciprocalCuspFunction (r : ℂ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction sourceCuspWidth r

/-! ## The reciprocal scalar at the compactified chamber cusp -/

/-- The algebraic reciprocal of `scalarTriangleDiscMap`, written so that the pole of the
Cayley transform is filled by zero. -/
def scalarTriangleDiscReciprocal (pole first second : Circle) (u : ℂ) : ℂ :=
  (scalarTriangleDenominator pole first second : ℂ) * ((pole : ℂ) - u) /
    (Complex.I * ((pole : ℂ) + u) -
      (circleCayleyCoord pole first : ℂ) * ((pole : ℂ) - u))

@[simp] theorem scalarTriangleDiscReciprocal_pole (pole first second : Circle) :
    scalarTriangleDiscReciprocal pole first second pole = 0 := by
  simp [scalarTriangleDiscReciprocal]

/-- The filled reciprocal is continuous at the Cayley pole. -/
theorem scalarTriangleDiscReciprocal_continuousAt_pole (pole first second : Circle) :
    ContinuousAt (scalarTriangleDiscReciprocal pole first second) pole := by
  have hpole : (pole : ℂ) ≠ 0 := pole.coe_ne_zero
  have hden :
      Complex.I * ((pole : ℂ) + (pole : ℂ)) -
          (circleCayleyCoord pole first : ℂ) * ((pole : ℂ) - (pole : ℂ)) ≠ 0 := by
    have heq :
        Complex.I * ((pole : ℂ) + (pole : ℂ)) -
            (circleCayleyCoord pole first : ℂ) * ((pole : ℂ) - (pole : ℂ)) =
          Complex.I * (2 * (pole : ℂ)) := by ring
    rw [heq]
    exact mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num) hpole)
  unfold scalarTriangleDiscReciprocal
  fun_prop

/-- Away from the Cayley pole, the filled formula is the actual reciprocal scalar map. -/
theorem scalarTriangleDiscReciprocal_eq_inv
    (pole first second : Circle)
    (hfirst : first ≠ pole) (hsecond : second ≠ pole) (hfinite : first ≠ second)
    {u : ℂ} (hu : u ≠ pole) :
    scalarTriangleDiscReciprocal pole first second u =
      (scalarTriangleDiscMap pole first second u)⁻¹ := by
  have hsub : (pole : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hden : (scalarTriangleDenominator pole first second : ℂ) ≠ 0 := by
    exact_mod_cast scalarTriangleDenominator_ne_zero
      hfirst hsecond hfinite
  unfold scalarTriangleDiscReciprocal scalarTriangleDiscMap boundaryCayley
  field_simp [hsub, hden]

/-- The inverse closed-disc coordinate can hit the marked cusp circle only at the compactified
chamber cusp. -/
theorem chamberClosureDiscInverse_ne_sourceCuspCircle_of_ne_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hqne : q ≠ sourceCuspVertex) :
    chamberClosureDiscInverse S q ≠ sourceCuspCircle S := by
  by_cases hq : q ∈ closure sourceBoundedChamber
  · intro heq
    let pole : closedBall (0 : ℂ) 1 :=
      ⟨sourceCuspCircle S, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
    have hinv : S.closureEquiv.symm ⟨q, hq⟩ = pole := by
      apply Subtype.ext
      simpa [pole, chamberClosureDiscInverse_apply_of_mem S hq] using heq
    have himage := congrArg S.closureEquiv hinv
    have hpole : S.closureEquiv pole =
        ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ := by
      simpa [pole, sourceCuspCircle] using
        S.closureEquiv_boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
          sourceCuspVertex_mem_frontier
    rw [S.closureEquiv.apply_symm_apply, hpole] at himage
    exact hqne (congrArg Subtype.val himage)
  · rw [chamberClosureDiscInverse]
    simp only [dif_neg hq]
    exact (sourceCuspCircle S).coe_ne_zero.symm

/-- The filled reciprocal scalar on the compactified source chamber. -/
def sourceScalarClosureReciprocal
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (q : ℂ) : ℂ :=
  scalarTriangleDiscReciprocal (sourceCuspCircle S) (sourceOrderThreeCircle S)
    (sourceOtherEllipticCircle S) (chamberClosureDiscInverse S q)

@[simp] theorem sourceScalarClosureReciprocal_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceScalarClosureReciprocal S sourceCuspVertex = 0 := by
  have hinv : chamberClosureDiscInverse S sourceCuspVertex = sourceCuspCircle S := by
    rw [chamberClosureDiscInverse_boundaryPreimage S sourceBoundedChamber_isOpen
      sourceCuspVertex sourceCuspVertex_mem_frontier]
    rfl
  simp [sourceScalarClosureReciprocal, hinv]

/-- The filled reciprocal is continuous up to the compactified source cusp, relative to the
closed bounded chamber. -/
theorem sourceScalarClosureReciprocal_continuousWithinAt_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousWithinAt (sourceScalarClosureReciprocal S)
      (closure sourceBoundedChamber) sourceCuspVertex := by
  have hinv : chamberClosureDiscInverse S sourceCuspVertex = sourceCuspCircle S := by
    rw [chamberClosureDiscInverse_boundaryPreimage S sourceBoundedChamber_isOpen
      sourceCuspVertex sourceCuspVertex_mem_frontier]
    rfl
  have hinner : ContinuousWithinAt (chamberClosureDiscInverse S)
      (closure sourceBoundedChamber) sourceCuspVertex :=
    chamberClosureDiscInverse_continuousOn S sourceCuspVertex
      (frontier_subset_closure sourceCuspVertex_mem_frontier)
  have houter := scalarTriangleDiscReciprocal_continuousAt_pole
    (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
  have hcomp : ContinuousWithinAt
      ((scalarTriangleDiscReciprocal (sourceCuspCircle S) (sourceOrderThreeCircle S)
        (sourceOtherEllipticCircle S)) ∘ chamberClosureDiscInverse S)
      (closure sourceBoundedChamber) sourceCuspVertex :=
    ContinuousAt.comp_continuousWithinAt_of_eq
      (f := chamberClosureDiscInverse S) houter hinner hinv
  change ContinuousWithinAt
    ((scalarTriangleDiscReciprocal (sourceCuspCircle S) (sourceOrderThreeCircle S)
      (sourceOtherEllipticCircle S)) ∘ chamberClosureDiscInverse S)
    (closure sourceBoundedChamber) sourceCuspVertex
  exact hcomp

/-- On every non-cusp point, the filled closure reciprocal equals the reciprocal of the scalar
closure map. -/
theorem sourceScalarClosureReciprocal_eq_inv
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hqne : q ≠ sourceCuspVertex) :
    sourceScalarClosureReciprocal S q = (sourceScalarClosureMap S q)⁻¹ := by
  rw [sourceScalarClosureReciprocal, sourceScalarClosureMap, Function.comp_apply]
  exact scalarTriangleDiscReciprocal_eq_inv _ _ _
    (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
    (sourceOrderThreeCircle_ne_otherElliptic S)
    (chamberClosureDiscInverse_ne_sourceCuspCircle_of_ne_cusp S hqne)

/-- The filled reciprocal pulled back to the original source chamber. -/
def sourceScalarTriangleReciprocal
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : ℂ) : ℂ :=
  sourceScalarClosureReciprocal S (cuspExponential sourceCuspWidth z)

theorem sourceScalarTriangleReciprocal_eq_inv
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : ℂ) :
    sourceScalarTriangleReciprocal S z = (sourceScalarTriangleMap S z)⁻¹ := by
  rw [sourceScalarTriangleReciprocal, sourceScalarTriangleMap, Function.comp_apply]
  exact sourceScalarClosureReciprocal_eq_inv S
    (by simpa [sourceCuspVertex] using cuspExponential_ne_zero sourceCuspWidth z)

/-- A fixed vertical approach to the source cusp. -/
def sourceCuspVerticalRay (y : ℝ) : ℂ := (y : ℂ) * Complex.I

theorem sourceCuspVerticalRay_tendsto_Iinfinity :
    Tendsto sourceCuspVerticalRay Filter.atTop Iinfinity := by
  rw [tendsto_comap_iff]
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with y hy
  simpa [sourceCuspVerticalRay, Function.comp_def] using hy

theorem cuspExponential_sourceCuspVerticalRay_tendsto :
    Tendsto (fun y ↦ cuspExponential sourceCuspWidth (sourceCuspVerticalRay y))
      Filter.atTop (nhds (0 : ℂ)) := by
  have hq := (Function.Periodic.qParam_tendsto sourceCuspWidth_pos).comp
    sourceCuspVerticalRay_tendsto_Iinfinity
  have hq' : Tendsto (Function.Periodic.qParam sourceCuspWidth ∘ sourceCuspVerticalRay)
      Filter.atTop (nhds (0 : ℂ)) := hq.mono_right inf_le_left
  simpa [cuspExponential, Function.Periodic.qParam, Function.comp_def] using hq'

theorem sourceCuspVerticalRay_eventually_mem_sourceOpenChamber :
    ∀ᶠ y : ℝ in Filter.atTop, sourceCuspVerticalRay y ∈ sourceOpenChamber := by
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp only [sourceCuspVerticalRay, sourceOpenChamber, Set.mem_setOf_eq,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero,
    normSq_apply]
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · linarith
  · nlinarith

/-- The explicit scalar reciprocal tends to zero along a vertical ray in the seed chamber. -/
theorem sourceScalarTriangleReciprocal_vertical_tendsto
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    Tendsto (sourceScalarTriangleReciprocal S ∘ sourceCuspVerticalRay)
      Filter.atTop (nhds (0 : ℂ)) := by
  have hq_nhds := cuspExponential_sourceCuspVerticalRay_tendsto
  have hq_mem : ∀ᶠ y : ℝ in Filter.atTop,
      cuspExponential sourceCuspWidth (sourceCuspVerticalRay y) ∈
        closure sourceBoundedChamber := by
    filter_upwards [sourceCuspVerticalRay_eventually_mem_sourceOpenChamber] with y hy
    apply subset_closure
    rw [sourceBoundedChamber]
    exact ⟨sourceCuspVerticalRay y, hy, by simp only [sourceCuspWidth]⟩
  have hq_within :
      Tendsto (fun y ↦ cuspExponential sourceCuspWidth (sourceCuspVerticalRay y))
        Filter.atTop (nhdsWithin sourceCuspVertex (closure sourceBoundedChamber)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa [sourceCuspVertex] using hq_nhds, hq_mem⟩
  have hcomp :=
    (sourceScalarClosureReciprocal_continuousWithinAt_cusp S).tendsto.comp hq_within
  change Tendsto
    (sourceScalarClosureReciprocal S ∘
      fun y ↦ cuspExponential sourceCuspWidth (sourceCuspVerticalRay y))
    Filter.atTop (nhds (0 : ℂ))
  simpa only [sourceScalarClosureReciprocal_cusp] using hcomp

/-- For a periodic function which is holomorphic and bounded at the cusp, it suffices to identify
the limit along one vertical ray.  Mathlib supplies existence of the unrestricted cusp limit. -/
theorem zeroAtFilter_of_periodic_of_bounded_of_vertical_tendsto
    {r : ℂ → ℂ}
    (hr_periodic : Function.Periodic r sourceCuspWidth)
    (hr_holomorphic : ∀ᶠ z in Iinfinity, DifferentiableAt ℂ r z)
    (hr_bounded : BoundedAtFilter Iinfinity r)
    (hr_vertical : Tendsto (r ∘ sourceCuspVerticalRay)
      Filter.atTop (nhds (0 : ℂ))) :
    ZeroAtFilter Iinfinity r := by
  have hr_limit := Function.Periodic.tendsto_at_I_inf sourceCuspWidth_pos
    hr_periodic hr_holomorphic hr_bounded
  have hr_limit_vertical := hr_limit.comp sourceCuspVerticalRay_tendsto_Iinfinity
  have hvalue : scalarReciprocalCuspFunction r 0 = 0 :=
    tendsto_nhds_unique hr_limit_vertical hr_vertical
  change Function.Periodic.cuspFunction sourceCuspWidth r 0 = 0 at hvalue
  rw [ZeroAtFilter]
  simpa only [hvalue] using hr_limit

/-- The reciprocal of a source coordinate on the upper half-plane, extended by zero below it.
The extension is chosen only so Mathlib's complex-periodic API can be used; cusp analysis never
sees the arbitrary lower-half-plane values. -/
def fuchsianCoordinateReciprocal (C : FuchsianOrbifoldCoordinate) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then (C.coordinate ⟨z, hz⟩)⁻¹ else 0

@[simp] theorem fuchsianCoordinateReciprocal_coe
    (C : FuchsianOrbifoldCoordinate) (z : UpperHalfPlane) :
    fuchsianCoordinateReciprocal C (z : ℂ) = (C.coordinate z)⁻¹ := by
  rw [fuchsianCoordinateReciprocal]
  split_ifs with h
  · congr 2
  · exact (h z.im_pos).elim

/-- Source invariance makes the canonical reciprocal extension periodic by the exact cusp
width. -/
theorem fuchsianCoordinateReciprocal_periodic (C : FuchsianOrbifoldCoordinate) :
    Function.Periodic (fuchsianCoordinateReciprocal C) sourceCuspWidth := by
  intro z
  have him_add : (z + (sourceCuspWidth : ℂ)).im = z.im := by simp
  by_cases hz : 0 < z.im
  · have hzadd : 0 < (z + (sourceCuspWidth : ℂ)).im := by simpa [him_add] using hz
    rw [fuchsianCoordinateReciprocal, dif_pos hzadd,
      fuchsianCoordinateReciprocal, dif_pos hz]
    let zp : UpperHalfPlane := ⟨z + (sourceCuspWidth : ℂ), hzadd⟩
    let z0 : UpperHalfPlane := ⟨z, hz⟩
    have hact : fuchsianSourceAction g₀ • zp = z0 := by
      change (fuchsianSourceAction g₀) zp = z0
      apply UpperHalfPlane.coe_injective
      rw [sourceCusp_translation]
      change z + (sourceCuspWidth : ℂ) - sourceCuspWidth = z
      ring
    have hinv := C.coordinate_invariant g₀ zp
    rw [hact] at hinv
    exact congrArg Inv.inv hinv.symm
  · have hzadd : ¬ 0 < (z + (sourceCuspWidth : ℂ)).im := by simpa [him_add] using hz
    rw [fuchsianCoordinateReciprocal, dif_neg hzadd,
      fuchsianCoordinateReciprocal, dif_neg hz]

/-- The canonical source cusp parameter tends to the completed cusp point. -/
theorem fuchsianSourceCuspQ_tendsto :
    Tendsto fuchsianSourceCuspQ upperHalfPlaneAtInfinity (nhds (0 : ℂ)) := by
  rw [show upperHalfPlaneAtInfinity = UpperHalfPlane.atImInfty by rfl]
  change Tendsto
    (fun z : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / sourceCuspWidth))
    UpperHalfPlane.atImInfty (nhds (0 : ℂ))
  simpa only [Function.Periodic.qParam] using
    (UpperHalfPlane.qParam_tendsto_atImInfty sourceCuspWidth_pos)

/-- Once the coordinate is eventually nonzero, its canonical reciprocal extension is
holomorphic at every sufficiently high complex point. -/
theorem fuchsianCoordinateReciprocal_eventually_differentiableAt
    (C : FuchsianOrbifoldCoordinate)
    (hcoordinate_ne : ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0) :
    ∀ᶠ z in Iinfinity, DifferentiableAt ℂ (fuchsianCoordinateReciprocal C) z := by
  have hcoordinate_ne' :
      ∀ᶠ z in Iinfinity, C.coordinate (UpperHalfPlane.ofComplex z) ≠ 0 :=
    UpperHalfPlane.tendsto_comap_im_ofComplex.eventually hcoordinate_ne
  have him_pos : ∀ᶠ z in Iinfinity, 0 < z.im :=
    preimage_mem_comap (Ioi_mem_atTop 0)
  filter_upwards [hcoordinate_ne', him_pos] with z hzne hzim
  have hcoordinate_diff :
      DifferentiableAt ℂ (C.coordinate ∘ UpperHalfPlane.ofComplex) z := by
    apply ((UpperHalfPlane.mdifferentiable_iff.mp C.coordinate_holomorphic) z hzim).differentiableAt
    exact UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzim
  have hinv_diff :
      DifferentiableAt ℂ (fun w => (C.coordinate (UpperHalfPlane.ofComplex w))⁻¹) z :=
    hcoordinate_diff.inv hzne
  have heq : fuchsianCoordinateReciprocal C =ᶠ[nhds z]
      (fun w => (C.coordinate (UpperHalfPlane.ofComplex w))⁻¹) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzim] with w hw
    rw [fuchsianCoordinateReciprocal, dif_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact hinv_diff.congr_of_eventuallyEq heq

theorem fuchsianCoordinateReciprocal_eventually_ne_zero
    (C : FuchsianOrbifoldCoordinate)
    (hcoordinate_ne : ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0) :
    ∀ᶠ z in Iinfinity, fuchsianCoordinateReciprocal C z ≠ 0 := by
  have hcoordinate_ne' :
      ∀ᶠ z in Iinfinity, C.coordinate (UpperHalfPlane.ofComplex z) ≠ 0 :=
    UpperHalfPlane.tendsto_comap_im_ofComplex.eventually hcoordinate_ne
  have him_pos : ∀ᶠ z in Iinfinity, 0 < z.im :=
    preimage_mem_comap (Ioi_mem_atTop 0)
  filter_upwards [hcoordinate_ne', him_pos] with z hzne hzim
  rw [fuchsianCoordinateReciprocal, dif_pos hzim]
  apply inv_ne_zero
  simpa only [← UpperHalfPlane.ofComplex_apply_of_im_pos hzim] using hzne

/-- Boundedness of the canonical reciprocal is enough to prove its full cusp decay once the
global coordinate agrees with the scalar seed on the source chamber.  The value of the limit is
read off along the fixed vertical ray. -/
theorem fuchsianCoordinateReciprocal_zeroAtFilter_of_bounded_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    (hcoordinate_ne : ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0)
    (hr_bounded : BoundedAtFilter Iinfinity (fuchsianCoordinateReciprocal C)) :
    ZeroAtFilter Iinfinity (fuchsianCoordinateReciprocal C) := by
  have hray_eq :
      (fuchsianCoordinateReciprocal C ∘ sourceCuspVerticalRay) =ᶠ[Filter.atTop]
        (sourceScalarTriangleReciprocal S ∘ sourceCuspVerticalRay) := by
    filter_upwards [sourceCuspVerticalRay_eventually_mem_sourceOpenChamber] with y hy
    have him : 0 < (sourceCuspVerticalRay y).im := hy.2.2.1
    calc
      (fuchsianCoordinateReciprocal C ∘ sourceCuspVerticalRay) y =
          (C.coordinate ⟨sourceCuspVerticalRay y, him⟩)⁻¹ := by
        rw [Function.comp_apply, fuchsianCoordinateReciprocal, dif_pos him]
      _ = (F (sourceCuspVerticalRay y))⁻¹ :=
        congrArg Inv.inv (hcoordinate ⟨sourceCuspVerticalRay y, him⟩)
      _ = (sourceScalarTriangleMap S (sourceCuspVerticalRay y))⁻¹ :=
        congrArg Inv.inv (hseed hy)
      _ = (sourceScalarTriangleReciprocal S ∘ sourceCuspVerticalRay) y := by
        rw [Function.comp_apply, sourceScalarTriangleReciprocal_eq_inv]
  have hr_vertical :
      Tendsto (fuchsianCoordinateReciprocal C ∘ sourceCuspVerticalRay)
        Filter.atTop (nhds (0 : ℂ)) :=
    (sourceScalarTriangleReciprocal_vertical_tendsto S).congr' hray_eq.symm
  exact zeroAtFilter_of_periodic_of_bounded_of_vertical_tendsto
    (fuchsianCoordinateReciprocal_periodic C)
    (fuchsianCoordinateReciprocal_eventually_differentiableAt C hcoordinate_ne)
    hr_bounded hr_vertical

/-- Reciprocal decay and local injectivity of the completed cusp function force the coordinate
to be nonzero sufficiently far into the cusp. -/
theorem fuchsianCoordinate_eventually_ne_zero_of_reciprocal_zero_of_locallyInjective
    (C : FuchsianOrbifoldCoordinate)
    (hr_zero : ZeroAtFilter Iinfinity (fuchsianCoordinateReciprocal C))
    (hr_locallyInjective :
      ∃ V ∈ nhds (0 : ℂ),
        InjOn (scalarReciprocalCuspFunction (fuchsianCoordinateReciprocal C)) V) :
    ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0 := by
  let r := fuchsianCoordinateReciprocal C
  let R := scalarReciprocalCuspFunction r
  obtain ⟨V, hV, hVinj⟩ := hr_locallyInjective
  have hR_zero : R 0 = 0 := by
    exact Function.Periodic.cuspFunction_zero_of_zero_at_inf sourceCuspWidth_pos hr_zero
  have hqV : ∀ᶠ z in upperHalfPlaneAtInfinity, fuchsianSourceCuspQ z ∈ V :=
    fuchsianSourceCuspQ_tendsto.eventually hV
  have hzeroV : (0 : ℂ) ∈ V := mem_of_mem_nhds hV
  have hR_eq (z : UpperHalfPlane) : R (fuchsianSourceCuspQ z) = r (z : ℂ) := by
    simpa only [R, r, scalarReciprocalCuspFunction, fuchsianSourceCuspQ,
      Function.Periodic.qParam] using
        (Function.Periodic.eq_cuspFunction sourceCuspWidth_pos.ne'
          (fuchsianCoordinateReciprocal_periodic C) (z : ℂ))
  filter_upwards [hqV] with z hzV
  have hrne : r (z : ℂ) ≠ 0 := by
    intro hrzero
    have hRqzero : R (fuchsianSourceCuspQ z) = R 0 := by
      rw [hR_eq z, hrzero, hR_zero]
    have hqzero := hVinj hzV hzeroV hRqzero
    exact Complex.exp_ne_zero _ hqzero
  change fuchsianCoordinateReciprocal C (z : ℂ) ≠ 0 at hrne
  rw [fuchsianCoordinateReciprocal_coe] at hrne
  simpa only [ne_eq, inv_eq_zero] using hrne

/-- High-fibre separation modulo the cusp period upgrades to local injectivity of the completed
cusp function.  This is the form naturally supplied by an exact-fibres theorem together with a
classification of sufficiently high cusp stabilizers. -/
theorem scalarReciprocalCuspFunction_locallyInjective_of_high_fibres
    {r : ℂ → ℂ}
    (hr_zero : ZeroAtFilter Iinfinity r)
    (hr_eventually_ne : ∀ᶠ z in Iinfinity, r z ≠ 0)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im → r z = r w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    ∃ V ∈ nhds (0 : ℂ), InjOn (scalarReciprocalCuspFunction r) V := by
  obtain ⟨A, hA⟩ := hr_high_fibres
  let R := scalarReciprocalCuspFunction r
  have hR_zero : R 0 = 0 := by
    exact Function.Periodic.cuspFunction_zero_of_zero_at_inf sourceCuspWidth_pos hr_zero
  have hhigh : ∀ᶠ q in nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ,
      A < (Function.Periodic.invQParam sourceCuspWidth q).im :=
    (Function.Periodic.invQParam_tendsto sourceCuspWidth_pos).eventually
      (preimage_mem_comap (Ioi_mem_atTop A))
  have hne : ∀ᶠ q in nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ,
      r (Function.Periodic.invQParam sourceCuspWidth q) ≠ 0 :=
    (Function.Periodic.invQParam_tendsto sourceCuspWidth_pos).eventually hr_eventually_ne
  have hpunctured := hhigh.and hne
  have hV : ∀ᶠ q in nhds (0 : ℂ),
      q = 0 ∨ (q ≠ 0 ∧ A < (Function.Periodic.invQParam sourceCuspWidth q).im ∧
        r (Function.Periodic.invQParam sourceCuspWidth q) ≠ 0) := by
    filter_upwards [eventually_nhdsWithin_iff.mp hpunctured] with q hq
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · exact Or.inr ⟨hq0, hq hq0⟩
  let V : Set ℂ := {q | q = 0 ∨
    (q ≠ 0 ∧ A < (Function.Periodic.invQParam sourceCuspWidth q).im ∧
      r (Function.Periodic.invQParam sourceCuspWidth q) ≠ 0)}
  refine ⟨V, hV, ?_⟩
  intro q hq w hw hqw
  change R q = R w at hqw
  rcases hq with hq0 | hq
  · subst q
    rcases hw with rfl | hw
    · rfl
    · exfalso
      have hRw : R w = r (Function.Periodic.invQParam sourceCuspWidth w) := by
        exact Function.Periodic.cuspFunction_eq_of_nonzero _ _ hw.1
      have : r (Function.Periodic.invQParam sourceCuspWidth w) = 0 := by
        calc
          r (Function.Periodic.invQParam sourceCuspWidth w) = R w := hRw.symm
          _ = R 0 := hqw.symm
          _ = 0 := hR_zero
      exact hw.2.2 this
  · rcases hw with hw0 | hw
    · subst w
      exfalso
      have hRq : R q = r (Function.Periodic.invQParam sourceCuspWidth q) := by
        exact Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq.1
      have : r (Function.Periodic.invQParam sourceCuspWidth q) = 0 := by
        calc
          r (Function.Periodic.invQParam sourceCuspWidth q) = R q := hRq.symm
          _ = R 0 := hqw
          _ = 0 := hR_zero
      exact hq.2.2 this
    · have hq0 : q ≠ 0 := hq.1
      have hw0 : w ≠ 0 := hw.1
      have hrqw :
          r (Function.Periodic.invQParam sourceCuspWidth q) =
            r (Function.Periodic.invQParam sourceCuspWidth w) := by
        simpa only [R, scalarReciprocalCuspFunction,
          Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
          Function.Periodic.cuspFunction_eq_of_nonzero _ _ hw0] using hqw
      have hparam := hA _ _ hq.2.1 hw.2.1 hrqw
      simpa only [Function.Periodic.qParam_right_inv sourceCuspWidth_pos.ne' hq0,
        Function.Periodic.qParam_right_inv sourceCuspWidth_pos.ne' hw0] using hparam

/-- A reusable analytic criterion for the exact simple source cusp.

The function `r` is allowed to be an arbitrary global representative, but on the upper
half-plane it must equal the reciprocal of `C`.  This form is convenient for a globally reflected
scalar: periodicity and the hypotheses at infinity can be proved before bundling the scalar as an
orbifold coordinate.
-/
theorem nonempty_hasExactFuchsianCusp_of_periodic_reciprocal
    (C : FuchsianOrbifoldCoordinate) (r : ℂ → ℂ)
    (hr_coordinate : ∀ z : UpperHalfPlane, r (z : ℂ) = (C.coordinate z)⁻¹)
    (hr_periodic : Function.Periodic r sourceCuspWidth)
    (hr_holomorphic : ∀ᶠ z in Iinfinity, DifferentiableAt ℂ r z)
    (hr_zero : ZeroAtFilter Iinfinity r)
    (hr_locallyInjective :
      ∃ V ∈ nhds (0 : ℂ), InjOn (scalarReciprocalCuspFunction r) V) :
    Nonempty (HasExactFuchsianCusp C) := by
  let R : ℂ → ℂ := scalarReciprocalCuspFunction r
  have hR_diff_zero : DifferentiableAt ℂ R 0 := by
    exact hr_periodic.differentiableAt_cuspFunction_zero sourceCuspWidth_pos
      hr_holomorphic hr_zero.boundedAtFilter
  have hR_diff_punctured :
      ∀ᶠ q in nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ, DifferentiableAt ℂ R q := by
    exact hr_periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero
      sourceCuspWidth_pos hr_holomorphic
  have hR_analytic : AnalyticAt ℂ R 0 := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_nhdsWithin_iff.mp hR_diff_punctured] with q hq
    by_cases hq0 : q = 0
    · simpa [hq0] using hR_diff_zero
    · exact hq hq0
  have hR_zero : R 0 = 0 := by
    exact Function.Periodic.cuspFunction_zero_of_zero_at_inf sourceCuspWidth_pos hr_zero
  have hR_deriv_ne : deriv R 0 ≠ 0 :=
    (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero hR_analytic).mp hr_locallyInjective
  have hR_order : analyticOrderAt R 0 = (1 : ℕ∞) :=
    hR_analytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hR_zero hR_deriv_ne
  obtain ⟨u, hu_analytic, hu_zero_ne, hR_factor⟩ :=
    (hR_analytic.analyticOrderAt_eq_natCast (n := 1)).mp hR_order
  have hu_eventually_analytic : ∀ᶠ q in nhds (0 : ℂ), AnalyticAt ℂ u q :=
    hu_analytic.eventually_analyticAt
  have hu_eventually_ne : ∀ᶠ q in nhds (0 : ℂ), u q ≠ 0 :=
    hu_analytic.continuousAt.eventually_ne hu_zero_ne
  have hfactor_eventually : ∀ᶠ q in nhds (0 : ℂ), R q = q * u q := by
    filter_upwards [hR_factor] with q hq
    simpa [smul_eq_mul] using hq
  have hgood : ∀ᶠ q in nhds (0 : ℂ),
      AnalyticAt ℂ u q ∧ u q ≠ 0 ∧ R q = q * u q :=
    hu_eventually_analytic.and (hu_eventually_ne.and hfactor_eventually)
  obtain ⟨epsilon, hepsilon, hepsilon_good⟩ := Metric.eventually_nhds_iff.mp hgood
  have hq_eventually_ball :
      ∀ᶠ z in upperHalfPlaneAtInfinity,
        fuchsianSourceCuspQ z ∈ Metric.ball (0 : ℂ) epsilon :=
    fuchsianSourceCuspQ_tendsto.eventually (Metric.ball_mem_nhds 0 hepsilon)
  have hR_eq (z : UpperHalfPlane) :
      R (fuchsianSourceCuspQ z) = r (z : ℂ) := by
    simpa only [R, scalarReciprocalCuspFunction, fuchsianSourceCuspQ,
      Function.Periodic.qParam] using
        (Function.Periodic.eq_cuspFunction sourceCuspWidth_pos.ne'
          hr_periodic (z : ℂ))
  refine ⟨
    { cuspUnit := u
      cuspRadius := epsilon
      cuspRadius_pos := hepsilon
      cuspUnit_holomorphic := ?_
      cuspUnit_zero_ne := hu_zero_ne
      cuspParameter_eventually_mem := hq_eventually_ball
      coordinate_eventually_ne_zero := ?_
      reciprocal_factorization := ?_ }⟩
  · intro q hq
    exact (hepsilon_good hq).1.differentiableAt.mdifferentiableAt
  · filter_upwards [hq_eventually_ball] with z hz
    have hgoodz := hepsilon_good hz
    have hRne : R (fuchsianSourceCuspQ z) ≠ 0 := by
      rw [hgoodz.2.2]
      exact mul_ne_zero (Complex.exp_ne_zero _) hgoodz.2.1
    have hrne : r (z : ℂ) ≠ 0 := by simpa only [hR_eq z] using hRne
    rw [hr_coordinate z] at hrne
    simpa only [ne_eq, inv_eq_zero] using hrne
  · filter_upwards [hq_eventually_ball] with z hz
    calc
      (C.coordinate z)⁻¹ = r (z : ℂ) := (hr_coordinate z).symm
      _ = R (fuchsianSourceCuspQ z) := (hR_eq z).symm
      _ = fuchsianSourceCuspQ z * u (fuchsianSourceCuspQ z) :=
        (hepsilon_good hz).2.2

/-- Canonical-coordinate form of `nonempty_hasExactFuchsianCusp_of_periodic_reciprocal`.
Periodicity and agreement with the quotient coordinate are automatic from source invariance, so
only the three genuinely asymptotic inputs remain. -/
theorem nonempty_hasExactFuchsianCusp_of_canonical_reciprocal
    (C : FuchsianOrbifoldCoordinate)
    (hr_zero : ZeroAtFilter Iinfinity (fuchsianCoordinateReciprocal C))
    (hr_locallyInjective :
      ∃ V ∈ nhds (0 : ℂ),
        InjOn (scalarReciprocalCuspFunction (fuchsianCoordinateReciprocal C)) V) :
    Nonempty (HasExactFuchsianCusp C) := by
  have hcoordinate_ne :=
    fuchsianCoordinate_eventually_ne_zero_of_reciprocal_zero_of_locallyInjective
      C hr_zero hr_locallyInjective
  exact nonempty_hasExactFuchsianCusp_of_periodic_reciprocal C
    (fuchsianCoordinateReciprocal C)
    (fuchsianCoordinateReciprocal_coe C)
    (fuchsianCoordinateReciprocal_periodic C)
    (fuchsianCoordinateReciprocal_eventually_differentiableAt C hcoordinate_ne)
    hr_zero hr_locallyInjective

/-- Exact-cusp criterion phrased only in terms of decay, nonvanishing, and fibre separation of
the canonical reciprocal. -/
theorem nonempty_hasExactFuchsianCusp_of_reciprocal_zero_of_high_fibres
    (C : FuchsianOrbifoldCoordinate)
    (hr_zero : ZeroAtFilter Iinfinity (fuchsianCoordinateReciprocal C))
    (hr_eventually_ne : ∀ᶠ z in Iinfinity, fuchsianCoordinateReciprocal C z ≠ 0)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal C z = fuchsianCoordinateReciprocal C w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    Nonempty (HasExactFuchsianCusp C) := by
  apply nonempty_hasExactFuchsianCusp_of_canonical_reciprocal C hr_zero
  exact scalarReciprocalCuspFunction_locallyInjective_of_high_fibres
    hr_zero hr_eventually_ne hr_high_fibres

/-! ## The high full-width Schwarz strip -/

/-- A convex full-period strip lying high enough to avoid both reflected unit circles. -/
def sourceScalarCuspStrip : Set ℂ :=
  {z | -Real.sqrt 2 / 2 < z.re ∧
    z.re < 1 + Real.sqrt 2 / 2 ∧ 2 < z.im}

theorem sourceScalarCuspStrip_isOpen : IsOpen sourceScalarCuspStrip := by
  rw [show sourceScalarCuspStrip =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 + Real.sqrt 2 / 2} ∩ {z : ℂ | 2 < z.im}) by
    ext z
    simp [sourceScalarCuspStrip]]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

theorem sourceScalarCuspStrip_convex : Convex ℝ sourceScalarCuspStrip := by
  rw [show sourceScalarCuspStrip =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 + Real.sqrt 2 / 2} ∩ {z : ℂ | 2 < z.im}) by
    ext z
    simp [sourceScalarCuspStrip]]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

/-- Closing only the two vertical edges of the high strip gives points in its topological
closure.  The strict height inequality is retained, as needed for cusp estimates. -/
theorem mem_closure_sourceScalarCuspStrip {z : ℂ}
    (hleft : -Real.sqrt 2 / 2 ≤ z.re)
    (hright : z.re ≤ 1 + Real.sqrt 2 / 2)
    (hhigh : 2 < z.im) :
    z ∈ closure sourceScalarCuspStrip := by
  let p : ℂ := 3 * Complex.I
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsegment : openSegment ℝ z p ⊆ sourceScalarCuspStrip := by
    intro w hw
    rw [openSegment_eq_image] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    have hre : (((1 - t) • z + t • p : ℂ)).re = (1 - t) * z.re := by
      simp [p]
    have him : (((1 - t) • z + t • p : ℂ)).im =
        (1 - t) * z.im + t * 3 := by
      simp [p]
    change -Real.sqrt 2 / 2 < (((1 - t) • z + t • p : ℂ)).re ∧
      (((1 - t) • z + t • p : ℂ)).re < 1 + Real.sqrt 2 / 2 ∧
      2 < (((1 - t) • z + t • p : ℂ)).im
    rw [hre, him]
    have hcoef_nonneg : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
    have hcoef_pos : 0 < 1 - t := sub_pos.mpr ht.2
    have hcoef_lt_one : 1 - t < 1 := by linarith [ht.1]
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hleft hcoef_nonneg
      have hstrict := mul_lt_mul_of_neg_right hcoef_lt_one (by nlinarith : -Real.sqrt 2 / 2 < 0)
      nlinarith
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hright hcoef_nonneg
      have hstrict := mul_lt_mul_of_pos_right hcoef_lt_one (by nlinarith : 0 < 1 + Real.sqrt 2 / 2)
      nlinarith
    · have hzmul := mul_lt_mul_of_pos_left hhigh hcoef_pos
      have ht_mul : t * 2 < t * 3 := mul_lt_mul_of_pos_left (by norm_num) ht.1
      nlinarith
  apply (closure_mono hsegment)
  exact segment_subset_closure_openSegment
    (left_mem_segment ℝ z p)

/-- The same edge-closure statement while retaining any stricter lower height bound. -/
theorem mem_closure_sourceScalarCuspStrip_inter_im_gt {z : ℂ}
    (hleft : -Real.sqrt 2 / 2 ≤ z.re)
    (hright : z.re ≤ 1 + Real.sqrt 2 / 2)
    {A : ℝ} (hstrip : 2 < z.im) (hA : A < z.im) :
    z ∈ closure (sourceScalarCuspStrip ∩ {w : ℂ | A < w.im}) := by
  let p : ℂ := (z.im : ℂ) * Complex.I
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsegment : openSegment ℝ z p ⊆
      sourceScalarCuspStrip ∩ {w : ℂ | A < w.im} := by
    intro w hw
    rw [openSegment_eq_image] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    have hre : (((1 - t) • z + t • p : ℂ)).re = (1 - t) * z.re := by
      simp [p]
    have him : (((1 - t) • z + t • p : ℂ)).im = z.im := by
      simp [p]
      ring
    refine ⟨?_, ?_⟩
    · change -Real.sqrt 2 / 2 < (((1 - t) • z + t • p : ℂ)).re ∧
        (((1 - t) • z + t • p : ℂ)).re < 1 + Real.sqrt 2 / 2 ∧
        2 < (((1 - t) • z + t • p : ℂ)).im
      rw [hre, him]
      have hcoef_nonneg : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
      have hcoef_lt_one : 1 - t < 1 := by linarith [ht.1]
      constructor
      · have hmul := mul_le_mul_of_nonneg_left hleft hcoef_nonneg
        have hstrict := mul_lt_mul_of_neg_right hcoef_lt_one
          (by nlinarith : -Real.sqrt 2 / 2 < 0)
        nlinarith
      constructor
      · have hmul := mul_le_mul_of_nonneg_left hright hcoef_nonneg
        have hstrict := mul_lt_mul_of_pos_right hcoef_lt_one
          (by nlinarith : 0 < 1 + Real.sqrt 2 / 2)
        nlinarith
      · exact hstrip
    · simpa only [Set.mem_setOf_eq, him] using hA
  apply closure_mono hsegment
  exact segment_subset_closure_openSegment
    (left_mem_segment ℝ z p)

/-- A uniform bound on one closed period strip makes a periodic function bounded at imaginary
infinity. -/
theorem boundedAtFilter_of_periodic_of_bound_on_closed_cusp_strip
    {r : ℂ → ℂ} (hr_periodic : Function.Periodic r sourceCuspWidth)
    (A M : ℝ)
    (hbound : ∀ z : ℂ, A < z.im →
      -Real.sqrt 2 / 2 ≤ z.re → z.re ≤ 1 + Real.sqrt 2 / 2 → ‖r z‖ ≤ M) :
    BoundedAtFilter Iinfinity r := by
  rw [BoundedAtFilter, Asymptotics.isBigO_iff]
  refine ⟨M, ?_⟩
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop A)] with z hz
  simp only [Pi.one_apply, norm_one, mul_one]
  let n : ℤ := ⌊(z.re + Real.sqrt 2 / 2) / sourceCuspWidth⌋
  let w : ℂ := z - (n : ℂ) * (sourceCuspWidth : ℂ)
  have hrem_nonneg := Int.sub_floor_div_mul_nonneg
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  have hrem_lt := Int.sub_floor_div_mul_lt
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  change 0 ≤ z.re + Real.sqrt 2 / 2 - (n : ℝ) * sourceCuspWidth at hrem_nonneg
  change z.re + Real.sqrt 2 / 2 - (n : ℝ) * sourceCuspWidth <
    sourceCuspWidth at hrem_lt
  have hwre : w.re = z.re - (n : ℝ) * sourceCuspWidth := by
    simp [w]
  have hwim : w.im = z.im := by simp [w]
  have hwleft : -Real.sqrt 2 / 2 ≤ w.re := by
    rw [hwre]
    linarith
  have hwright : w.re ≤ 1 + Real.sqrt 2 / 2 := by
    rw [hwre, sourceCuspWidth]
    rw [sourceCuspWidth] at hrem_lt
    linarith
  have heq := hr_periodic.sub_int_mul_eq (x := z) n
  change r w = r z at heq
  calc
    ‖r z‖ = ‖r w‖ := congrArg norm heq.symm
    _ ≤ M := hbound w (by simpa [hwim] using hz) hwleft hwright

theorem sourceScalarCuspStrip_subset_sourceRightDouble :
    sourceScalarCuspStrip ⊆ sourceRightDouble := by
  intro z hz
  rcases hz with ⟨hl, hr, hi⟩
  have him : 0 < z.im := lt_trans (by norm_num) hi
  have hn : 1 < normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hnr : 1 < normSq (sourceRight z) := by
    rw [sourceRight_normSq]
    nlinarith [sq_nonneg (1 - z.re)]
  exact ⟨hl, hr, him, hn, hnr⟩

theorem cuspExponential_tendsto_Iinfinity :
    Tendsto (cuspExponential sourceCuspWidth) Iinfinity (nhds (0 : ℂ)) := by
  have hq := Function.Periodic.qParam_tendsto sourceCuspWidth_pos
  have hq' : Tendsto (Function.Periodic.qParam sourceCuspWidth)
      Iinfinity (nhds (0 : ℂ)) := hq.mono_right inf_le_left
  change Tendsto (Function.Periodic.qParam sourceCuspWidth)
    Iinfinity (nhds (0 : ℂ))
  exact hq'

theorem sourceRight_tendsto_Iinfinity :
    Tendsto sourceRight Iinfinity Iinfinity := by
  rw [tendsto_comap_iff]
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop b)] with z hz
  simpa [Function.comp_def, sourceRight] using hz.le

theorem cuspExponential_sourceRight_tendsto_Iinfinity :
    Tendsto (cuspExponential sourceCuspWidth ∘ sourceRight)
      Iinfinity (nhds (0 : ℂ)) :=
  cuspExponential_tendsto_Iinfinity.comp sourceRight_tendsto_Iinfinity

theorem sourceScalarCuspStrip_mem_sourceOpenChamber_of_re_lt_half
    {z : ℂ} (hz : z ∈ sourceScalarCuspStrip) (hre : z.re < 1 / 2) :
    z ∈ sourceOpenChamber := by
  have him : 0 < z.im := lt_trans (by norm_num) hz.2.2
  have hhigh : 2 < z.im := hz.2.2
  have hn : 1 < normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 2)]
  exact ⟨hz.1, hre, him, hn⟩

theorem cuspExponential_mem_sourceClosure_of_mem_cuspStrip_of_re_le_half
    {z : ℂ} (hz : z ∈ sourceScalarCuspStrip) (hre : z.re ≤ 1 / 2) :
    cuspExponential sourceCuspWidth z ∈ closure sourceBoundedChamber := by
  rcases hre.lt_or_eq with hrelt | hreeq
  · apply subset_closure
    rw [sourceBoundedChamber]
    exact ⟨z, sourceScalarCuspStrip_mem_sourceOpenChamber_of_re_lt_half hz hrelt, by
      simp only [sourceCuspWidth]⟩
  · apply frontier_subset_closure
    have him : 0 < z.im := lt_trans (by norm_num) hz.2.2
    have hhigh : 2 < z.im := hz.2.2
    have hn : 1 < normSq z := by
      rw [normSq_apply]
      nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 2)]
    simpa only [sourceCuspWidth] using
      cuspExponential_mem_source_frontier_of_rightSide hreeq him hn

theorem sourceRight_mem_sourceOpenChamber_of_mem_cuspStrip_of_half_lt
    {z : ℂ} (hz : z ∈ sourceScalarCuspStrip) (hre : 1 / 2 < z.re) :
    sourceRight z ∈ sourceOpenChamber := by
  have hr := sourceRightDouble_mapsTo
    (sourceScalarCuspStrip_subset_sourceRightDouble hz)
  refine ⟨hr.1, ?_, hr.2.2.1, hr.2.2.2.1⟩
  rw [sourceRight_re]
  linarith

/-- Public high-strip form of the reflected branch formula. -/
theorem sourceScalarRightDoubleMap_eq_conj_seed_of_mem_cuspStrip_of_half_lt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceScalarCuspStrip) (hre : 1 / 2 < z.re) :
    sourceScalarRightDoubleMap S z =
      (starRingEnd ℂ) (sourceScalarTriangleMap S (sourceRight z)) := by
  have hzdouble := sourceScalarCuspStrip_subset_sourceRightDouble hz
  have hrmem := sourceRightDouble_mapsTo hzdouble
  have hrle : (sourceRight z).re ≤ 1 / 2 := by
    rw [sourceRight_re]
    linarith
  have hreflect := sourceScalarRightDoubleMap_reflection S hzdouble
  have hback := congrArg (starRingEnd ℂ) hreflect
  have hbranch : sourceScalarRightDoubleMap S z =
      (starRingEnd ℂ) (sourceScalarRightDoubleMap S (sourceRight z)) := by
    simpa using hback.symm
  rw [hbranch, sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hrle]

/-- High points of the closed source fundamental triangle cannot have scalar value zero.  Indeed,
zero is already the marked order-three value, and injectivity on the closed triangle would force
the point to be the finite order-three vertex. -/
theorem sourceScalarTriangleMap_ne_zero_of_high_fundamental
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hleft : -Real.sqrt 2 / 2 ≤ z.re) (hright : z.re ≤ 1 / 2)
    (hhigh : 2 < z.im) :
    sourceScalarTriangleMap S z ≠ 0 := by
  let zu : UpperHalfPlane := ⟨z, lt_trans (by norm_num) hhigh⟩
  have hnorm : 1 ≤ normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 2)]
  have hzfund : zu ∈ fundamentalTriangle := by
    exact ⟨hleft, hright, by simpa only [zu] using hnorm⟩
  intro hzero
  have heq : zu = fuchsianOneFixedPoint :=
    sourceScalarTriangleMap_injective_on_fundamentalTriangle S hzfund
      fuchsianOneFixedPoint_mem_fundamentalTriangle
      (by
        change sourceScalarTriangleMap S z =
          sourceScalarTriangleMap S (fuchsianOneFixedPoint : ℂ)
        exact hzero.trans (sourceScalarTriangleMap_fuchsianOne S).symm)
  have him_eq := congrArg (fun w : UpperHalfPlane => w.im) heq
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  change z.im = Real.sqrt 3 / 2 at him_eq
  nlinarith

/-- The explicit right Schwarz double has no zero anywhere in the open high period strip. -/
theorem sourceScalarRightDoubleMap_ne_zero_on_cuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceScalarCuspStrip) :
    sourceScalarRightDoubleMap S z ≠ 0 := by
  by_cases hre : z.re ≤ 1 / 2
  · rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hre]
    exact sourceScalarTriangleMap_ne_zero_of_high_fundamental S hz.1.le hre hz.2.2
  · have hre' : 1 / 2 < z.re := lt_of_not_ge hre
    rw [sourceScalarRightDoubleMap_eq_conj_seed_of_mem_cuspStrip_of_half_lt S hz hre']
    have hopen := sourceRight_mem_sourceOpenChamber_of_mem_cuspStrip_of_half_lt hz hre'
    have hseed : sourceScalarTriangleMap S (sourceRight z) ≠ 0 := by
      apply sourceScalarTriangleMap_ne_zero_of_high_fundamental S hopen.1.le hopen.2.1.le
      simpa [sourceRight] using hz.2.2
    intro hstar
    apply hseed
    have := congrArg (starRingEnd ℂ) hstar
    simpa using this

/-! The left edge of the chosen period strip is interior to the left Schwarz double. -/

/-- A convex high rectangle crossing the left reflection seam. -/
def sourceScalarLeftCuspDoubleStrip : Set ℂ :=
  {z | -Real.sqrt 2 - 1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 2 < z.im}

theorem sourceScalarLeftCuspDoubleStrip_isOpen :
    IsOpen sourceScalarLeftCuspDoubleStrip := by
  rw [show sourceScalarLeftCuspDoubleStrip =
      {z : ℂ | -Real.sqrt 2 - 1 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩ {z : ℂ | 2 < z.im}) by
    ext z
    simp [sourceScalarLeftCuspDoubleStrip]]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

theorem sourceScalarLeftCuspDoubleStrip_convex :
    Convex ℝ sourceScalarLeftCuspDoubleStrip := by
  rw [show sourceScalarLeftCuspDoubleStrip =
      {z : ℂ | -Real.sqrt 2 - 1 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩ {z : ℂ | 2 < z.im}) by
    ext z
    simp [sourceScalarLeftCuspDoubleStrip]]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

theorem sourceScalarLeftCuspDoubleStrip_subset_sourceLeftDouble :
    sourceScalarLeftCuspDoubleStrip ⊆ sourceLeftDouble := by
  intro z hz
  have him : 0 < z.im := lt_trans (by norm_num) hz.2.2
  have hhigh : 2 < z.im := hz.2.2
  have hn : 1 < normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hnl : 1 < normSq (sourceLeft z) := by
    rw [sourceLeft_normSq]
    nlinarith [sq_nonneg (Real.sqrt 2 + z.re)]
  exact ⟨hz.1, hz.2.1, him, hn, hnl⟩

theorem three_I_mem_sourceScalarLeftCuspDoubleStrip :
    (3 * Complex.I : ℂ) ∈ sourceScalarLeftCuspDoubleStrip := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  norm_num [sourceScalarLeftCuspDoubleStrip]
  linarith

/-- On the original side, including its reflection seam, the left Schwarz double is the seed. -/
theorem sourceScalarLeftDoubleMap_eq_seed_of_left_le_re
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hre : -Real.sqrt 2 / 2 ≤ z.re) :
    sourceScalarLeftDoubleMap S z = sourceScalarTriangleMap S z := by
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) (by simp) one_ne_zero
  rw [sourceLeft_coord_im]
  linarith

/-- A holomorphic global scalar agreeing with the chamber seed agrees with the explicit left
Schwarz reflection throughout a high neighborhood of the left period edge. -/
theorem globalScalar_eqOn_leftDoubleMap_on_highStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    EqOn F (sourceScalarLeftDoubleMap S) sourceScalarLeftCuspDoubleStrip := by
  have hstrip_upper : sourceScalarLeftCuspDoubleStrip ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact lt_trans (by norm_num) hz.2.2
  have hFanalytic : AnalyticOnNhd ℂ F sourceScalarLeftCuspDoubleStrip :=
    (hF.mono hstrip_upper).analyticOnNhd sourceScalarLeftCuspDoubleStrip_isOpen
  have hGanalytic : AnalyticOnNhd ℂ (sourceScalarLeftDoubleMap S)
      sourceScalarLeftCuspDoubleStrip :=
    ((sourceScalarLeftDoubleMap_differentiableOn S).mono
      sourceScalarLeftCuspDoubleStrip_subset_sourceLeftDouble).analyticOnNhd
        sourceScalarLeftCuspDoubleStrip_isOpen
  have heq_seed : EqOn F (sourceScalarLeftDoubleMap S) sourceOpenChamber := by
    intro z hz
    exact (hseed hz).trans (sourceScalarLeftDoubleMap_eq_seed S hz).symm
  have heventually :
      F =ᶠ[nhds (3 * Complex.I : ℂ)] sourceScalarLeftDoubleMap S :=
    heq_seed.eventuallyEq_of_mem
      (sourceOpenChamber_isOpen.mem_nhds (by
        have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        norm_num [sourceOpenChamber, normSq_apply]
        linarith))
  exact hFanalytic.eqOn_of_preconnected_of_eventuallyEq hGanalytic
    sourceScalarLeftCuspDoubleStrip_convex.isPreconnected
    three_I_mem_sourceScalarLeftCuspDoubleStrip heventually

/-- The explicit Schwarz-double reciprocal is uniformly small on the open high period strip. -/
theorem sourceScalarRightDoubleMap_inv_eventually_norm_lt_one_on_cuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ∀ᶠ z in Iinfinity, z ∈ sourceScalarCuspStrip →
      ‖(sourceScalarRightDoubleMap S z)⁻¹‖ < 1 := by
  let R := sourceScalarClosureReciprocal S
  have hsmall_within : ∀ᶠ q in nhdsWithin sourceCuspVertex
      (closure sourceBoundedChamber), ‖R q‖ < 1 := by
    have hnorm := (sourceScalarClosureReciprocal_continuousWithinAt_cusp S).norm
    change ∀ᶠ q in nhdsWithin sourceCuspVertex
      (closure sourceBoundedChamber), ‖sourceScalarClosureReciprocal S q‖ < 1
    have hvalue : ‖sourceScalarClosureReciprocal S sourceCuspVertex‖ < 1 := by simp
    exact hnorm.tendsto.eventually (Iio_mem_nhds hvalue)
  have hsmall_nhds : ∀ᶠ q in nhds sourceCuspVertex,
      q ∈ closure sourceBoundedChamber → ‖R q‖ < 1 :=
    eventually_nhdsWithin_iff.mp hsmall_within
  have hsmall_left := cuspExponential_tendsto_Iinfinity.eventually hsmall_nhds
  have hsmall_right :=
    cuspExponential_sourceRight_tendsto_Iinfinity.eventually hsmall_nhds
  filter_upwards [hsmall_left, hsmall_right] with z hzsmall hrzsmall
  intro hz
  by_cases hre : z.re ≤ 1 / 2
  · have hqmem :=
      cuspExponential_mem_sourceClosure_of_mem_cuspStrip_of_re_le_half hz hre
    have hsmall := hzsmall hqmem
    change ‖sourceScalarTriangleReciprocal S z‖ < 1 at hsmall
    rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hre]
    simpa only [sourceScalarTriangleReciprocal_eq_inv] using hsmall
  · have hre' : 1 / 2 < z.re := lt_of_not_ge hre
    have hopen :=
      sourceRight_mem_sourceOpenChamber_of_mem_cuspStrip_of_half_lt hz hre'
    have hqmem : cuspExponential sourceCuspWidth (sourceRight z) ∈
        closure sourceBoundedChamber := by
      apply subset_closure
      rw [sourceBoundedChamber]
      exact ⟨sourceRight z, hopen, by simp only [sourceCuspWidth]⟩
    have hsmall := hrzsmall hqmem
    change ‖sourceScalarTriangleReciprocal S (sourceRight z)‖ < 1 at hsmall
    rw [sourceScalarRightDoubleMap_eq_conj_seed_of_mem_cuspStrip_of_half_lt S hz hre']
    rw [sourceScalarTriangleReciprocal_eq_inv] at hsmall
    simpa using hsmall

theorem three_I_mem_sourceScalarCuspStrip :
    (3 * Complex.I : ℂ) ∈ sourceScalarCuspStrip := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num [sourceScalarCuspStrip]
  constructor <;> linarith

theorem three_I_mem_sourceOpenChamber :
    (3 * Complex.I : ℂ) ∈ sourceOpenChamber := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num [sourceOpenChamber, normSq_apply]
  linarith

/-- A holomorphic global scalar agreeing with the seed on the original chamber agrees with the
explicit Schwarz reflection on the entire high full-period strip. -/
theorem globalScalar_eqOn_rightDoubleMap_on_cuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    EqOn F (sourceScalarRightDoubleMap S) sourceScalarCuspStrip := by
  have hstrip_upper : sourceScalarCuspStrip ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    change -Real.sqrt 2 / 2 < z.re ∧
      z.re < 1 + Real.sqrt 2 / 2 ∧ 2 < z.im at hz
    exact lt_trans (by norm_num) hz.2.2
  have hFanalytic : AnalyticOnNhd ℂ F sourceScalarCuspStrip :=
    (hF.mono hstrip_upper).analyticOnNhd sourceScalarCuspStrip_isOpen
  have hGanalytic : AnalyticOnNhd ℂ (sourceScalarRightDoubleMap S)
      sourceScalarCuspStrip :=
    ((sourceScalarRightDoubleMap_differentiableOn S).mono
      sourceScalarCuspStrip_subset_sourceRightDouble).analyticOnNhd
        sourceScalarCuspStrip_isOpen
  have heq_seed : EqOn F (sourceScalarRightDoubleMap S) sourceOpenChamber := by
    intro z hz
    exact (hseed hz).trans (sourceScalarRightDoubleMap_eq_seed S hz).symm
  have heventually :
      F =ᶠ[nhds (3 * Complex.I : ℂ)] sourceScalarRightDoubleMap S :=
    heq_seed.eventuallyEq_of_mem
      (sourceOpenChamber_isOpen.mem_nhds three_I_mem_sourceOpenChamber)
  exact hFanalytic.eqOn_of_preconnected_of_eventuallyEq hGanalytic
    sourceScalarCuspStrip_convex.isPreconnected
    three_I_mem_sourceScalarCuspStrip heventually

/-- Seed agreement forces the global scalar to be nonzero on one half-open high period strip.
The open part is controlled by the right Schwarz double, while the included left endpoint is
controlled by the left Schwarz double. -/
theorem globalScalar_ne_zero_on_halfOpen_cusp_period
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    {z : ℂ} (hleft : -Real.sqrt 2 / 2 ≤ z.re)
    (hright : z.re < 1 + Real.sqrt 2 / 2) (hhigh : 2 < z.im) :
    F z ≠ 0 := by
  rcases hleft.lt_or_eq with hleft' | hleft'
  · have hzstrip : z ∈ sourceScalarCuspStrip := ⟨hleft', hright, hhigh⟩
    rw [globalScalar_eqOn_rightDoubleMap_on_cuspStrip S F hF hseed hzstrip]
    exact sourceScalarRightDoubleMap_ne_zero_on_cuspStrip S hzstrip
  · have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hzleft : z ∈ sourceScalarLeftCuspDoubleStrip := by
      change -Real.sqrt 2 - 1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 2 < z.im
      rw [← hleft']
      exact ⟨by nlinarith, by nlinarith, hhigh⟩
    have hrightFund : z.re ≤ 1 / 2 := by rw [← hleft']; nlinarith
    rw [globalScalar_eqOn_leftDoubleMap_on_highStrip S F hF hseed hzleft,
      sourceScalarLeftDoubleMap_eq_seed_of_left_le_re S hleft]
    exact sourceScalarTriangleMap_ne_zero_of_high_fundamental
      S hleft hrightFund hhigh

/-- For a global holomorphic scalar agreeing with the chamber seed, the canonical reciprocal is
automatically nonzero at every sufficiently high complex point. -/
theorem fuchsianCoordinateReciprocal_eventually_ne_zero_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    ∀ᶠ z in Iinfinity, fuchsianCoordinateReciprocal C z ≠ 0 := by
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop 2)] with z hz
  let n : ℤ := ⌊(z.re + Real.sqrt 2 / 2) / sourceCuspWidth⌋
  let w : ℂ := z - (n : ℂ) * (sourceCuspWidth : ℂ)
  have hrem_nonneg := Int.sub_floor_div_mul_nonneg
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  have hrem_lt := Int.sub_floor_div_mul_lt
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  change 0 ≤ z.re + Real.sqrt 2 / 2 - (n : ℝ) * sourceCuspWidth at hrem_nonneg
  change z.re + Real.sqrt 2 / 2 - (n : ℝ) * sourceCuspWidth <
    sourceCuspWidth at hrem_lt
  have hwre : w.re = z.re - (n : ℝ) * sourceCuspWidth := by
    simp [w]
  have hwim : w.im = z.im := by simp [w]
  change 2 < z.im at hz
  have hwleft : -Real.sqrt 2 / 2 ≤ w.re := by
    rw [hwre]
    linarith
  have hwright : w.re < 1 + Real.sqrt 2 / 2 := by
    rw [hwre, sourceCuspWidth]
    rw [sourceCuspWidth] at hrem_lt
    linarith
  have hwhigh : 2 < w.im := by simpa only [hwim] using hz
  have hFw : F w ≠ 0 :=
    globalScalar_ne_zero_on_halfOpen_cusp_period S F hF hseed
      hwleft hwright hwhigh
  have hwpos : 0 < w.im := lt_trans (by norm_num) hwhigh
  have hrw : fuchsianCoordinateReciprocal C w ≠ 0 := by
    rw [fuchsianCoordinateReciprocal, dif_pos hwpos, hcoordinate]
    exact inv_ne_zero hFw
  have heq := (fuchsianCoordinateReciprocal_periodic C).sub_int_mul_eq (x := z) n
  change fuchsianCoordinateReciprocal C w = fuchsianCoordinateReciprocal C z at heq
  rw [← heq]
  exact hrw

/-- Equivalently, the upper-half-plane coordinate itself is eventually nonzero; this is no
longer an independent cusp hypothesis. -/
theorem fuchsianCoordinate_eventually_ne_zero_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0 := by
  have hr_ne : ∀ᶠ z : UpperHalfPlane in upperHalfPlaneAtInfinity,
      fuchsianCoordinateReciprocal C (z : ℂ) ≠ 0 :=
    UpperHalfPlane.tendsto_coe_atImInfty.eventually
      (fuchsianCoordinateReciprocal_eventually_ne_zero_of_seed
        S C F hcoordinate hF hseed)
  filter_upwards [hr_ne] with z hz
  intro hzero
  apply hz
  rw [fuchsianCoordinateReciprocal_coe, hzero, inv_zero]

/-- The canonical reciprocal of a global scalar coordinate is uniformly small on the open high
period strip. -/
theorem fuchsianCoordinateReciprocal_eventually_norm_lt_one_on_cuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    ∀ᶠ z in Iinfinity, z ∈ sourceScalarCuspStrip →
      ‖fuchsianCoordinateReciprocal C z‖ < 1 := by
  have heq := globalScalar_eqOn_rightDoubleMap_on_cuspStrip S F hF hseed
  filter_upwards [sourceScalarRightDoubleMap_inv_eventually_norm_lt_one_on_cuspStrip S]
    with z hzsmall
  intro hz
  have him : 0 < z.im := lt_trans (by norm_num) hz.2.2
  calc
    ‖fuchsianCoordinateReciprocal C z‖ =
        ‖(C.coordinate ⟨z, him⟩)⁻¹‖ := by
      rw [fuchsianCoordinateReciprocal, dif_pos him]
    _ = ‖(F z)⁻¹‖ := congrArg norm (congrArg Inv.inv (hcoordinate ⟨z, him⟩))
    _ = ‖(sourceScalarRightDoubleMap S z)⁻¹‖ :=
      congrArg norm (congrArg Inv.inv (heq hz))
    _ < 1 := hzsmall hz

/-- The canonical reciprocal is bounded at imaginary infinity.  The open-strip estimate extends
to both vertical edges by continuity, and periodicity reduces every point to that closed strip. -/
theorem fuchsianCoordinateReciprocal_boundedAtFilter_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    BoundedAtFilter Iinfinity (fuchsianCoordinateReciprocal C) := by
  have hcoordinate_ne : ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0 :=
    fuchsianCoordinate_eventually_ne_zero_of_seed S C F hcoordinate hF hseed
  obtain ⟨Aopen, hAopen⟩ := eventually_Iinfinity_iff.mp
    (fuchsianCoordinateReciprocal_eventually_norm_lt_one_on_cuspStrip
      S C F hcoordinate hF hseed)
  obtain ⟨Adiff, hAdiff⟩ := eventually_Iinfinity_iff.mp
    (fuchsianCoordinateReciprocal_eventually_differentiableAt C hcoordinate_ne)
  let A : ℝ := max 2 (max Aopen Adiff)
  apply boundedAtFilter_of_periodic_of_bound_on_closed_cusp_strip
    (fuchsianCoordinateReciprocal_periodic C) A 1
  intro z hz hleft hright
  have htwo : 2 < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hopen : Aopen < z.im :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 2 _)) hz
  have hdiff : Adiff < z.im :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 2 _)) hz
  let T : Set ℂ := sourceScalarCuspStrip ∩ {w : ℂ | Aopen < w.im}
  have hzclosure : z ∈ closure T := by
    exact mem_closure_sourceScalarCuspStrip_inter_im_gt hleft hright htwo hopen
  have hcontinuous : ContinuousWithinAt (fuchsianCoordinateReciprocal C) T z :=
    (hAdiff z hdiff).continuousAt.continuousWithinAt
  have hmaps : MapsTo (fuchsianCoordinateReciprocal C) T (closedBall (0 : ℂ) 1) := by
    intro w hw
    apply mem_closedBall_zero_iff.mpr
    exact (hAopen w hw.2 hw.1).le
  have hmem := hcontinuous.mem_closure hzclosure hmaps
  rw [isClosed_closedBall.closure_eq] at hmem
  exact mem_closedBall_zero_iff.mp hmem

/-- Hence seed agreement and eventual cusp nonvanishing force reciprocal decay, with no separate
boundedness hypothesis. -/
theorem fuchsianCoordinateReciprocal_zeroAtFilter_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    ZeroAtFilter Iinfinity (fuchsianCoordinateReciprocal C) := by
  have hcoordinate_ne : ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0 :=
    fuchsianCoordinate_eventually_ne_zero_of_seed S C F hcoordinate hF hseed
  apply fuchsianCoordinateReciprocal_zeroAtFilter_of_bounded_of_seed
    S C F hcoordinate hseed hcoordinate_ne
  exact fuchsianCoordinateReciprocal_boundedAtFilter_of_seed
    S C F hcoordinate hF hseed

/-- Complete exact-cusp constructor from global scalar seed agreement and high-fibre separation. -/
theorem nonempty_hasExactFuchsianCusp_of_seed_of_high_fibres
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal C z = fuchsianCoordinateReciprocal C w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    Nonempty (HasExactFuchsianCusp C) := by
  apply nonempty_hasExactFuchsianCusp_of_reciprocal_zero_of_high_fibres C
    (fuchsianCoordinateReciprocal_zeroAtFilter_of_seed
      S C F hcoordinate hF hseed)
    (fuchsianCoordinateReciprocal_eventually_ne_zero_of_seed
      S C F hcoordinate hF hseed)
    hr_high_fibres

/-- Consequently the global scalar is injective throughout the high full-period Schwarz strip. -/
theorem globalScalar_injOn_cuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    InjOn F sourceScalarCuspStrip := by
  have heq := globalScalar_eqOn_rightDoubleMap_on_cuspStrip S F hF hseed
  intro z hz w hw hzw
  apply sourceScalarRightDoubleMap_injOn S
    (sourceScalarCuspStrip_subset_sourceRightDouble hz)
    (sourceScalarCuspStrip_subset_sourceRightDouble hw)
  rw [← heq hz, ← heq hw]
  exact hzw

/-! ## Full source-coordinate wiring -/

open SphereSixComplex.Periods.ExactSourceAssembly

/-- All exact-source data except the completed cusp.  This interface lets the independent
regularity and elliptic-order arguments plug directly into the scalar cusp theorem without
duplicating them here. -/
structure SourceCoordinateCoreExceptCusp where
  coordinate : UpperHalfPlane → ℂ
  coordinate_holomorphic : MDiff coordinate
  coordinate_invariant : ∀ g z,
    coordinate (fuchsianSourceAction g • z) = coordinate z
  coordinate_surjective : Function.Surjective coordinate
  coordinate_isOpenMap : IsOpenMap coordinate
  coordinate_eq_iff_orbit : ∀ z w,
    coordinate z = coordinate w ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w
  coordinate_at_one : coordinate fuchsianOneFixedPoint = 0
  coordinate_at_two : coordinate fuchsianTwoFixedPoint = 1
  regular_localHomeomorph :
    IsLocalHomeomorph (sourceRegularValueSet.restrictPreimage coordinate)
  branch_one : HasExactHolomorphicBranchAt coordinate fuchsianOneFixedPoint 0 3
  branch_two : HasExactHolomorphicBranchAt coordinate fuchsianTwoFixedPoint 1 4

namespace SourceCoordinateCoreExceptCusp

variable (K : SourceCoordinateCoreExceptCusp)

/-- The underlying invariant holomorphic coordinate before adding exact quotient data. -/
def toFuchsianOrbifoldCoordinate : FuchsianOrbifoldCoordinate where
  coordinate := K.coordinate
  coordinate_holomorphic := K.coordinate_holomorphic
  coordinate_invariant := K.coordinate_invariant

/-- Reciprocal decay and local cusp-disc injectivity fill the final cusp field and immediately
assemble a fully exact source orbifold coordinate. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate
    (hr_zero : ZeroAtFilter Iinfinity
      (fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate))
    (hr_locallyInjective :
      ∃ V ∈ nhds (0 : ℂ), InjOn
        (scalarReciprocalCuspFunction
          (fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate)) V) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  obtain ⟨hcusp⟩ := nonempty_hasExactFuchsianCusp_of_canonical_reciprocal
    K.toFuchsianOrbifoldCoordinate hr_zero hr_locallyInjective
  let Kfull : SourceCoordinateCore :=
    { coordinate := K.coordinate
      coordinate_holomorphic := K.coordinate_holomorphic
      coordinate_invariant := K.coordinate_invariant
      coordinate_surjective := K.coordinate_surjective
      coordinate_isOpenMap := K.coordinate_isOpenMap
      coordinate_eq_iff_orbit := K.coordinate_eq_iff_orbit
      coordinate_at_one := K.coordinate_at_one
      coordinate_at_two := K.coordinate_at_two
      regular_localHomeomorph := K.regular_localHomeomorph
      branch_one := K.branch_one
      branch_two := K.branch_two
      cusp := by
        simpa only [toFuchsianOrbifoldCoordinate] using hcusp }
  exact ⟨Kfull.toExactFuchsianOrbifoldCoordinate⟩

/-- High reciprocal-fibre separation is a convenient replacement for explicitly constructing
the locally injective cusp-disc germ. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_high_fibres
    (hr_zero : ZeroAtFilter Iinfinity
      (fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate))
    (hr_eventually_ne : ∀ᶠ z in Iinfinity,
      fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate z ≠ 0)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate z =
          fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  apply K.nonempty_exactFuchsianOrbifoldCoordinate hr_zero
  exact scalarReciprocalCuspFunction_locallyInjective_of_high_fibres
    hr_zero hr_eventually_ne hr_high_fibres

/-- Full exact-source assembly from a global scalar branch, apart from the high-cusp fibre
classification.  Reciprocal decay, boundedness, and the exact simple cusp are automatic. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_seed_of_high_fibres
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, K.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate z =
          fuchsianCoordinateReciprocal K.toFuchsianOrbifoldCoordinate w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  have hcoordinate' : ∀ z : UpperHalfPlane,
      K.toFuchsianOrbifoldCoordinate.coordinate z = F (z : ℂ) := by
    simpa only [toFuchsianOrbifoldCoordinate] using hcoordinate
  apply K.nonempty_exactFuchsianOrbifoldCoordinate_of_high_fibres
    (fuchsianCoordinateReciprocal_zeroAtFilter_of_seed S
      K.toFuchsianOrbifoldCoordinate F hcoordinate' hF hseed)
    (fuchsianCoordinateReciprocal_eventually_ne_zero_of_seed S
      K.toFuchsianOrbifoldCoordinate F hcoordinate' hF hseed)
    hr_high_fibres

end SourceCoordinateCoreExceptCusp


end SphereSixComplex.Periods.SourceChamberTopology
