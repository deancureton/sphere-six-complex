module

public import SphereSixComplex.Periods.Uniformization.SourceAutomaticRegularity
import all SphereSixComplex.Periods.Uniformization.SourceAutomaticRegularity
public import SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau
import all SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau
public import SphereSixComplex.Periods.Uniformization.FiniteCornerReflection
import all SphereSixComplex.Periods.Uniformization.FiniteCornerReflection
public import SphereSixComplex.Geometry.ProperlyDiscontinuousSlice
import all SphereSixComplex.Geometry.ProperlyDiscontinuousSlice
public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
import all SphereSixComplex.Geometry.EllipticCayleyHomeomorph
public import SphereSixComplex.TriangleGroup.EstablishedFuchsianEllipticStabilizers
import all SphereSixComplex.TriangleGroup.EstablishedFuchsianEllipticStabilizers
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import all TauCeti.Analysis.Complex.Conformal.LocalDegree

@[expose] public section

/-!
# Automatic elliptic orders from exact orbit fibres

For a holomorphic quotient coordinate, proper discontinuity isolates the finite stabilizer at an
elliptic point.  Nearby noncentral fibres are regular and hence simple.  Tau Ceti's local-degree
theorem then identifies the analytic order with the number of nearby points in a fibre, which is
bounded by the cardinality of the stabilizer.
-/

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceAutomaticBranch

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The inverse Cayley fractional-linear expression, without restricting its argument to the
unit disc.  Near zero it is an analytic chart into the upper half-plane. -/
def cayleyRawInverse (a : UpperHalfPlane) (w : ℂ) : ℂ :=
  ((a : ℂ) - w * starRingEnd ℂ (a : ℂ)) / (1 - w)

@[simp]
theorem cayleyRawInverse_zero (a : UpperHalfPlane) :
    cayleyRawInverse a 0 = (a : ℂ) := by
  simp [cayleyRawInverse]

theorem cayleyRawInverse_analyticAt_zero (a : UpperHalfPlane) :
    AnalyticAt ℂ (cayleyRawInverse a) 0 := by
  apply (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id)
  norm_num

theorem cayleyRawInverse_analyticAt {a : UpperHalfPlane} {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ (cayleyRawInverse a) w := by
  apply (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id)
  change (1 : ℂ) - w ≠ 0
  exact sub_ne_zero.mpr hw.symm

theorem cayleyRawInverse_im_pos {a : UpperHalfPlane} {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayleyRawInverse a w).im := by
  let wd : ComplexUnitDisc := ⟨w, hw⟩
  simpa only [cayleyRawInverse, cayleyInverse, wd] using cayleyInverse_im_pos a wd

theorem cayleyCoordinate_rawInverse {a : UpperHalfPlane} {w : ℂ} (hw : ‖w‖ < 1) :
    cayleyCoordinate a
      (UpperHalfPlane.ofComplex (cayleyRawInverse a w)) = w := by
  let wd : ComplexUnitDisc := ⟨w, hw⟩
  have him : 0 < (cayleyRawInverse a w).im := cayleyRawInverse_im_pos hw
  have hof : UpperHalfPlane.ofComplex (cayleyRawInverse a w) =
      cayleyInverseUpper a wd := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    rfl
  rw [hof]
  have h := congrArg Subtype.val (cayley_cayleyInverse a wd)
  exact h

/-- The analytic source coordinate written in a raw Cayley chart. -/
def ellipticChartFunction (coordinate : UpperHalfPlane → ℂ)
    (a : UpperHalfPlane) (w : ℂ) : ℂ :=
  coordinate (UpperHalfPlane.ofComplex (cayleyRawInverse a w))

theorem ellipticChartFunction_analyticAt_zero
    {coordinate : UpperHalfPlane → ℂ} (hcoordinate : MDiff coordinate)
    (a : UpperHalfPlane) :
    AnalyticAt ℂ (ellipticChartFunction coordinate a) 0 := by
  have houter := TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex
    hcoordinate a.im_pos
  have hcomp : AnalyticAt ℂ
      ((coordinate ∘ UpperHalfPlane.ofComplex) ∘ cayleyRawInverse a) 0 :=
    AnalyticAt.comp_of_eq
      (g := coordinate ∘ UpperHalfPlane.ofComplex)
      (f := cayleyRawInverse a) (x := (0 : ℂ)) (y := (a : ℂ))
      houter (cayleyRawInverse_analyticAt_zero a) (cayleyRawInverse_zero a)
  change AnalyticAt ℂ
    (fun x ↦ coordinate (UpperHalfPlane.ofComplex (cayleyRawInverse a x))) 0
  simpa only [Function.comp_def] using hcomp

theorem ellipticChartFunction_analyticAt_of_norm_lt_one
    {coordinate : UpperHalfPlane → ℂ} (hcoordinate : MDiff coordinate)
    {a : UpperHalfPlane} {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (ellipticChartFunction coordinate a) w := by
  have him := cayleyRawInverse_im_pos (a := a) hw
  have houter := TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcoordinate him
  have hwone : w ≠ 1 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hcomp : AnalyticAt ℂ
      ((coordinate ∘ UpperHalfPlane.ofComplex) ∘ cayleyRawInverse a) w :=
    houter.comp (cayleyRawInverse_analyticAt hwone)
  change AnalyticAt ℂ
    (fun x ↦ coordinate (UpperHalfPlane.ofComplex (cayleyRawInverse a x))) w
  simpa only [Function.comp_def] using hcomp

theorem cayleyRawChart_continuousAt {a : UpperHalfPlane} {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousAt (fun z ↦ UpperHalfPlane.ofComplex (cayleyRawInverse a z)) w := by
  exact (UpperHalfPlane.mdifferentiableAt_ofComplex (cayleyRawInverse_im_pos hw)).continuousAt.comp
    (cayleyRawInverse_analyticAt (by
      intro h
      rw [h] at hw
      norm_num at hw)).continuousAt

theorem cayleyRawChart_injOn_ball (a : UpperHalfPlane) :
    InjOn (fun z ↦ UpperHalfPlane.ofComplex (cayleyRawInverse a z)) (ball 0 1) := by
  intro z hz w hw hzw
  have hzc : cayleyCoordinate a
      (UpperHalfPlane.ofComplex (cayleyRawInverse a z)) = z :=
    cayleyCoordinate_rawInverse (by simpa only [mem_ball, dist_zero_right] using hz)
  have hwc : cayleyCoordinate a
      (UpperHalfPlane.ofComplex (cayleyRawInverse a w)) = w :=
    cayleyCoordinate_rawInverse (by simpa only [mem_ball, dist_zero_right] using hw)
  have hc := congrArg (cayleyCoordinate a) hzw
  exact hzc.symm.trans (hc.trans hwc)

theorem cayleyRawInverse_deriv_zero_ne (a : UpperHalfPlane) :
    deriv (cayleyRawInverse a) 0 ≠ 0 := by
  apply (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero
    (cayleyRawInverse_analyticAt_zero a)).mp
  refine ⟨ball 0 1, isOpen_ball.mem_nhds (by simp), ?_⟩
  intro z hz w hw hzw
  apply cayleyRawChart_injOn_ball a hz hw
  exact congrArg UpperHalfPlane.ofComplex hzw

theorem cayleyRawChart_orderThree_rotate {w : ℂ} (hw : ‖w‖ < 1) :
    UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianOneFixedPoint (orderThreeMultiplier * w)) =
      fuchsianSourceAction g₁ •
        UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w) := by
  have hrotNorm : ‖orderThreeMultiplier * w‖ < 1 := by
    rw [norm_mul, norm_orderThreeMultiplier, one_mul]
    exact hw
  apply (cayleyHomeomorph fuchsianOneFixedPoint).injective
  apply Subtype.ext
  change cayleyCoordinate fuchsianOneFixedPoint
      (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianOneFixedPoint (orderThreeMultiplier * w))) =
    cayleyCoordinate fuchsianOneFixedPoint
      (fuchsianSourceAction g₁ •
        UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w))
  calc
    cayleyCoordinate fuchsianOneFixedPoint
        (UpperHalfPlane.ofComplex
          (cayleyRawInverse fuchsianOneFixedPoint (orderThreeMultiplier * w))) =
        orderThreeMultiplier * w := cayleyCoordinate_rawInverse hrotNorm
    _ = orderThreeMultiplier * cayleyCoordinate fuchsianOneFixedPoint
        (UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w)) := by
      rw [cayleyCoordinate_rawInverse hw]
    _ = cayleyCoordinate fuchsianOneFixedPoint
        (fuchsianSourceAction g₁ •
          UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w)) := by
      simpa only [orderThreeCayley] using
        (orderThreeCayley_generator
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianOneFixedPoint w))).symm

theorem cayleyRawChart_orderFour_rotate {w : ℂ} (hw : ‖w‖ < 1) :
    UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianTwoFixedPoint (orderFourMultiplier * w)) =
      fuchsianSourceAction g₂ •
        UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w) := by
  have hrotNorm : ‖orderFourMultiplier * w‖ < 1 := by
    rw [norm_mul, norm_orderFourMultiplier, one_mul]
    exact hw
  apply (cayleyHomeomorph fuchsianTwoFixedPoint).injective
  apply Subtype.ext
  change cayleyCoordinate fuchsianTwoFixedPoint
      (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianTwoFixedPoint (orderFourMultiplier * w))) =
    cayleyCoordinate fuchsianTwoFixedPoint
      (fuchsianSourceAction g₂ •
        UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w))
  calc
    cayleyCoordinate fuchsianTwoFixedPoint
        (UpperHalfPlane.ofComplex
          (cayleyRawInverse fuchsianTwoFixedPoint (orderFourMultiplier * w))) =
        orderFourMultiplier * w := cayleyCoordinate_rawInverse hrotNorm
    _ = orderFourMultiplier * cayleyCoordinate fuchsianTwoFixedPoint
        (UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w)) := by
      rw [cayleyCoordinate_rawInverse hw]
    _ = cayleyCoordinate fuchsianTwoFixedPoint
        (fuchsianSourceAction g₂ •
          UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w)) := by
      simpa only [orderFourCayley] using
        (orderFourCayley_generator
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianTwoFixedPoint w))).symm

/-- A finite analytic order computed in the Cayley chart is the same order in the ordinary
upper-half-plane chart and hence packages the project's exact branch contract. -/
noncomputable def hasExactHolomorphicBranchAt_of_cayley_order
    {f : UpperHalfPlane → ℂ} (hf : MDiff f) (center : UpperHalfPlane)
    (value : ℂ) (order : ℕ) (horderPos : 0 < order)
    (hne : (fun z ↦ f z - value) ≠ 0)
    (horder : analyticOrderAt
      (fun w ↦ ellipticChartFunction f center w - value) 0 = order) :
    HasExactHolomorphicBranchAt f center value order := by
  let F : UpperHalfPlane → ℂ := fun z ↦ f z - value
  let A : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex
  have hF : MDiff F := hf.sub mdifferentiable_const
  have hA : AnalyticAt ℂ A (center : ℂ) :=
    TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hF center.im_pos
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := A) (g := cayleyRawInverse center) (z₀ := (0 : ℂ))
    (cayleyRawInverse_analyticAt_zero center)
    (cayleyRawInverse_deriv_zero_ne center)
  have hcomp' : analyticOrderAt
      (fun w ↦ ellipticChartFunction f center w - value) 0 =
        analyticOrderAt A (center : ℂ) := by
    simpa only [A, F, Function.comp_def, ellipticChartFunction,
      cayleyRawInverse_zero, UpperHalfPlane.ofComplex_apply] using hcomp
  have hAorder : analyticOrderAt A (center : ℂ) = order := by
    exact hcomp'.symm.trans horder
  have hvanish : TauCeti.orderOfVanishingAt F center = order := by
    rw [TauCeti.orderOfVanishingAt_def, hA.meromorphicOrderAt_eq, hAorder]
    simp
  exact ExactNormalizedModularJTau.hasExactHolomorphicBranchAt_of_order hf center value order
    horderPos hne (by simpa only [F] using hvanish)

/-- At a regular source point, exact orbit fibres make a holomorphic coordinate locally
injective in every locally injective analytic chart. -/
theorem deriv_comp_chart_ne_zero_of_regular
    (coordinate : UpperHalfPlane → ℂ)
    (hfibres : ∀ z w,
      coordinate z = coordinate w ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w)
    {chart : ℂ → UpperHalfPlane} {w : ℂ}
    (hchart_cont : ContinuousAt chart w)
    (hchart_inj : ∃ V ∈ nhds w, InjOn chart V)
    (hregular : FreeProductTorsion.IsFuchsianRegularPoint (chart w))
    (hanalytic : AnalyticAt ℂ (coordinate ∘ chart) w) :
    deriv (coordinate ∘ chart) w ≠ 0 := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianSourceAction_properlyDiscontinuous
  obtain ⟨U, hU, htranslate⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Delta (chart w)
  obtain ⟨V, hV, hchart_inj⟩ := hchart_inj
  let W : Set ℂ := chart ⁻¹' U ∩ V
  have hW : W ∈ nhds w := inter_mem (hchart_cont hU) hV
  apply (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero hanalytic).mp
  refine ⟨W, hW, ?_⟩
  intro x hx y hy hxy
  obtain ⟨g, hg⟩ := (hfibres (chart x) (chart y)).mp hxy
  have hinter : (((g • ·) '' U) ∩ U).Nonempty := by
    refine ⟨chart y, ⟨chart x, hx.1, ?_⟩, hy.1⟩
    exact hg
  have hfix : fuchsianSourceAction g • chart w = chart w := htranslate g hinter
  have hgOne : g = 1 :=
    fuchsian_fixed_regular_eq_one fuchsianSourceAction_properlyDiscontinuous
      hregular hfix
  apply hchart_inj hx.2 hy.2
  simpa only [hgOne, map_one, one_smul] using hg

/-- A local fibre parametrized by a finite type bounds the analytic local degree.  This is the
cardinality step used at both source elliptic points. -/
theorem analyticOrderNatAt_le_card_of_local_fibre_parametrization
    {f : ℂ → ℂ} {c : ℂ} {α : Type*} [Fintype α]
    (hf : AnalyticAt ℂ f c)
    (hisol : ∀ᶠ z in nhdsWithin c {c}ᶜ, f z ≠ f c)
    (hderiv : ∀ᶠ z in nhdsWithin c {c}ᶜ, deriv f z ≠ 0)
    (T : α → ℂ → ℂ)
    (hparam : ∃ V ∈ nhds c, ∀ z ∈ V, ∀ w ∈ V,
      f z = f w → ∃ a : α, T a z = w) :
    analyticOrderNatAt (fun z ↦ f z - f c) c ≤ Fintype.card α := by
  classical
  obtain ⟨V, hV, hparam⟩ := hparam
  have hall : ∀ᶠ z in nhds c,
      AnalyticAt ℂ f z ∧
        (z ≠ c → f z ≠ f c) ∧
        (z ≠ c → deriv f z ≠ 0) ∧
        z ∈ V := by
    filter_upwards [hf.eventually_analyticAt, eventually_nhdsWithin_iff.mp hisol,
      eventually_nhdsWithin_iff.mp hderiv, hV] with z hzA hzisol hzderiv hzV
    exact ⟨hzA, fun hzc ↦ hzisol (by simpa using hzc),
      fun hzc ↦ hzderiv (by simpa using hzc), hzV⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsub : ∀ z ∈ closedBall c r, dist z c < ε := by
    intro z hz
    exact lt_of_le_of_lt (mem_closedBall.mp hz) (by dsimp [r]; linarith)
  have hA : AnalyticOnNhd ℂ f (closedBall c r) :=
    fun z hz ↦ (hball (hsub z hz)).1
  have hI : ∀ z ∈ closedBall c r, z ≠ c → f z ≠ f c :=
    fun z hz hzc ↦ (hball (hsub z hz)).2.1 hzc
  have hD : ∀ z ∈ ball c r, z ≠ c → deriv f z ≠ 0 :=
    fun z hz hzc ↦ (hball (hsub z (ball_subset_closedBall hz))).2.2.1 hzc
  obtain ⟨δ, hδ, hcard⟩ := TauCeti.localDegree_card hr hA hI hD
  let q : ℂ := f c + (δ / 2 : ℝ)
  have hqne : q ≠ f c := by
    simp [q, ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hqlt : ‖q - f c‖ < δ := by
    simp only [q, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  obtain ⟨hfinite, hncard, _hsimple⟩ := hcard q hqne hqlt
  let E : Set ℂ := {z ∈ ball c r | f z = q}
  have horderTop : analyticOrderAt (fun z ↦ f z - f c) c ≠ ⊤ :=
    TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero hr fun z hz hzc ↦
      sub_ne_zero.mpr (hI z (ball_subset_closedBall hz) hzc)
  have horderNe : analyticOrderAt (fun z ↦ f z - f c) c ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hf.sub analyticAt_const, sub_self (f c)⟩
  have horderPos : 0 < analyticOrderNatAt (fun z ↦ f z - f c) c := by
    have hcast :
        ((analyticOrderNatAt (fun z ↦ f z - f c) c : ℕ) : ℕ∞) =
          analyticOrderAt (fun z ↦ f z - f c) c :=
      Nat.cast_analyticOrderNatAt horderTop
    exact Nat.pos_of_ne_zero fun hk ↦ horderNe (by simpa [hk] using hcast.symm)
  have hEnonempty : E.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [show E.ncard = analyticOrderNatAt (fun z ↦ f z - f c) c by
      simpa only [E] using hncard]
    exact horderPos.ne'
  let y : E := ⟨Classical.choose hEnonempty, Classical.choose_spec hEnonempty⟩
  let φ : α → E := fun a ↦
    if ha : T a y.1 ∈ E then ⟨T a y.1, ha⟩ else y
  have hφsurj : Function.Surjective φ := by
    intro x
    have hyball : y.1 ∈ ball c ε := by
      exact lt_of_lt_of_le (mem_ball.mp y.2.1) (by dsimp [r]; linarith)
    have hxball : x.1 ∈ ball c ε := by
      exact lt_of_lt_of_le (mem_ball.mp x.2.1) (by dsimp [r]; linarith)
    have hyV := (hball hyball).2.2.2
    have hxV := (hball hxball).2.2.2
    obtain ⟨a, ha⟩ := hparam y.1 hyV x.1 hxV (y.2.2.trans x.2.2.symm)
    refine ⟨a, ?_⟩
    have hmem : T a y.1 ∈ E := ha.symm ▸ x.2
    apply Subtype.ext
    simp [φ, hmem, ha]
  have hEfinite : E.Finite := by simpa only [E] using hfinite
  letI : Fintype E := hEfinite.fintype
  have hle : Fintype.card E ≤ Fintype.card α :=
    Fintype.card_le_of_surjective φ hφsurj
  rw [Set.fintypeCard_eq_ncard,
    show E.ncard = analyticOrderNatAt (fun z ↦ f z - f c) c by
      simpa only [E] using hncard] at hle
  exact hle

/-- Exact orbit fibres identify every sufficiently small elliptic fibre with an element of the
finite stabilizer.  Simplicity off the elliptic orbit then bounds the analytic order by the
stabilizer cardinality. -/
theorem ellipticChartFunction_order_le_stabilizer_card
    {α : Type*} [Fintype α]
    (embed : α → Delta)
    (coordinate : UpperHalfPlane → ℂ)
    (hcoordinate : MDiff coordinate)
    (hinvariant : ∀ g z,
      coordinate (fuchsianSourceAction g • z) = coordinate z)
    (hfibres : ∀ z w,
      coordinate z = coordinate w ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w)
    (center other : UpperHalfPlane) (value otherValue : ℂ)
    (hcenter : coordinate center = value)
    (hother : coordinate other = otherValue)
    (hvalues : value ≠ otherValue)
    (hregular_of_ne : ∀ z,
      coordinate z ≠ value → coordinate z ≠ otherValue →
        FreeProductTorsion.IsFuchsianRegularPoint z)
    (hstabilizer : ∀ g : Delta,
      fuchsianSourceAction g • center = center ↔ ∃ a : α, g = embed a) :
    analyticOrderAt
        (fun w ↦ ellipticChartFunction coordinate center w - value) 0 ≠ ⊤ ∧
      analyticOrderNatAt
          (fun w ↦ ellipticChartFunction coordinate center w - value) 0 ≤
        Fintype.card α := by
  classical
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianSourceAction_properlyDiscontinuous
  let chart : ℂ → UpperHalfPlane := fun w ↦
    UpperHalfPlane.ofComplex (cayleyRawInverse center w)
  let G : ℂ → ℂ := ellipticChartFunction coordinate center
  obtain ⟨S, hSopen, hcenterS, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) center
  let radius : ℝ := dist value otherValue / 2
  have hradius : 0 < radius := by
    dsimp [radius]
    exact half_pos (dist_pos.mpr hvalues)
  let V : Set ℂ :=
    chart ⁻¹' S ∩ ball 0 1 ∩ G ⁻¹' ball value radius
  have hchart_zero : chart 0 = center := by
    simp [chart, cayleyRawInverse_zero]
  have hG_zero : G 0 = value := by
    simp [G, ellipticChartFunction, cayleyRawInverse_zero, hcenter]
  have hchart_cont_zero : ContinuousAt chart 0 := by
    simpa only [chart] using (cayleyRawChart_continuousAt (a := center) (by norm_num))
  have hG_cont_zero : ContinuousAt G 0 :=
    (ellipticChartFunction_analyticAt_zero hcoordinate center).continuousAt
  have hV : V ∈ nhds (0 : ℂ) := by
    apply inter_mem
    · exact inter_mem
        (hchart_cont_zero (by rw [hchart_zero]; exact hSopen.mem_nhds hcenterS))
        (isOpen_ball.mem_nhds (by simp))
    · exact hG_cont_zero (by
        rw [hG_zero]
        exact isOpen_ball.mem_nhds (by simpa using hradius))
  have hnot_other : ∀ w ∈ V, G w ≠ otherValue := by
    intro w hw heq
    have hlt : dist otherValue value < radius := by
      simpa only [V, Set.mem_inter_iff, Set.mem_preimage, mem_ball, heq] using hw.2
    rw [dist_comm otherValue value] at hlt
    dsimp [radius] at hlt
    have hdnonneg : 0 ≤ dist value otherValue := dist_nonneg
    linarith
  have hnot_center : ∀ w ∈ V, w ≠ 0 → G w ≠ value := by
    intro w hw hwzero heq
    have hwdisc : ‖w‖ < 1 := by
      simpa only [V, Set.mem_inter_iff, mem_ball, dist_zero_right] using hw.1.2
    have hcoord : coordinate (chart w) = coordinate center := by
      simpa only [G, ellipticChartFunction, chart, hcenter] using heq
    obtain ⟨g, hg⟩ := (hfibres (chart w) center).mp hcoord
    have hinter : (((g • ·) '' S) ∩ S).Nonempty := by
      refine ⟨center, ⟨chart w, hw.1.1, hg⟩, hcenterS⟩
    have hfix : fuchsianSourceAction g • center = center :=
      (htranslate g).mp hinter
    have hchart_eq : chart w = center := by
      calc
        chart w = fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • chart w) := by
          rw [map_inv, inv_smul_smul]
        _ = fuchsianSourceAction g⁻¹ • center := congrArg _ hg
        _ = fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • center) := congrArg _ hfix.symm
        _ = center := by rw [map_inv, inv_smul_smul]
    apply hwzero
    calc
      w = cayleyCoordinate center (chart w) := by
        symm
        exact cayleyCoordinate_rawInverse hwdisc
      _ = cayleyCoordinate center center := congrArg _ hchart_eq
      _ = 0 := cayleyCoordinate_center center
  have hisol : ∀ᶠ w in nhdsWithin (0 : ℂ) {0}ᶜ, G w ≠ G 0 := by
    have hVwithin : V ∈ nhdsWithin (0 : ℂ) {0}ᶜ := nhdsWithin_le_nhds hV
    filter_upwards [hVwithin, self_mem_nhdsWithin]
      with w hwV hw0
    rw [hG_zero]
    exact hnot_center w hwV (by simpa using hw0)
  have hderiv : ∀ᶠ w in nhdsWithin (0 : ℂ) {0}ᶜ, deriv G w ≠ 0 := by
    have hVwithin : V ∈ nhdsWithin (0 : ℂ) {0}ᶜ := nhdsWithin_le_nhds hV
    filter_upwards [hVwithin, self_mem_nhdsWithin]
      with w hwV hw0
    have hwdisc : w ∈ ball (0 : ℂ) 1 := hwV.1.2
    have hwnorm : ‖w‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hwdisc
    have hwne : w ≠ 0 := by simpa using hw0
    have hregular : FreeProductTorsion.IsFuchsianRegularPoint (chart w) :=
      hregular_of_ne (chart w)
        (by simpa only [G, ellipticChartFunction, chart] using
          hnot_center w hwV hwne)
        (by simpa only [G, ellipticChartFunction, chart] using
          hnot_other w hwV)
    have hne := deriv_comp_chart_ne_zero_of_regular coordinate hfibres
      (w := w) (chart := chart)
      (by simpa only [chart] using
        (cayleyRawChart_continuousAt (a := center) hwnorm))
      ⟨ball 0 1, isOpen_ball.mem_nhds hwdisc,
        by simpa only [chart] using cayleyRawChart_injOn_ball center⟩
      hregular
      (by
        change AnalyticAt ℂ (ellipticChartFunction coordinate center) w
        exact ellipticChartFunction_analyticAt_of_norm_lt_one hcoordinate hwnorm)
    change deriv (fun x ↦ coordinate
      (UpperHalfPlane.ofComplex (cayleyRawInverse center x))) w ≠ 0
    simpa only [chart, Function.comp_def] using hne
  let T : α → ℂ → ℂ := fun a w ↦
    cayleyCoordinate center (fuchsianSourceAction (embed a) • chart w)
  have hparam : ∃ W ∈ nhds (0 : ℂ), ∀ z ∈ W, ∀ w ∈ W,
      G z = G w → ∃ a : α, T a z = w := by
    refine ⟨V, hV, ?_⟩
    intro z hz w hw hzw
    obtain ⟨g, hg⟩ := (hfibres (chart z) (chart w)).mp (by
      simpa only [G, ellipticChartFunction, chart] using hzw)
    have hinter : (((g • ·) '' S) ∩ S).Nonempty :=
      ⟨chart w, ⟨chart z, hz.1.1, hg⟩, hw.1.1⟩
    have hfix : fuchsianSourceAction g • center = center :=
      (htranslate g).mp hinter
    obtain ⟨a, ha⟩ := (hstabilizer g).mp hfix
    refine ⟨a, ?_⟩
    have hwnorm : ‖w‖ < 1 := by
      simpa only [V, Set.mem_inter_iff, mem_ball, dist_zero_right] using hw.1.2
    calc
      T a z = cayleyCoordinate center
          (fuchsianSourceAction (embed a) • chart z) := rfl
      _ = cayleyCoordinate center (chart w) := by rw [← ha, hg]
      _ = w := cayleyCoordinate_rawInverse hwnorm
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hV
  have hfinite : analyticOrderAt (fun w ↦ G w - value) 0 ≠ ⊤ :=
    TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero hε fun w hw hwzero ↦
      sub_ne_zero.mpr (hnot_center w (hball (by simpa only [mem_ball] using hw)) hwzero)
  have hbound := analyticOrderNatAt_le_card_of_local_fibre_parametrization
    (f := G) (c := (0 : ℂ))
    (ellipticChartFunction_analyticAt_zero hcoordinate center)
    hisol hderiv T hparam
  exact ⟨by simpa only [G] using hfinite, by simpa only [hG_zero, G] using hbound⟩

theorem isFuchsianRegularPoint_of_coordinate_ne_ellipticValues
    (coordinate : UpperHalfPlane → ℂ)
    (hinvariant : ∀ g z,
      coordinate (fuchsianSourceAction g • z) = coordinate z)
    (hone : coordinate fuchsianOneFixedPoint = 0)
    (htwo : coordinate fuchsianTwoFixedPoint = 1)
    {z : UpperHalfPlane} (hz0 : coordinate z ≠ 0) (hz1 : coordinate z ≠ 1) :
    FreeProductTorsion.IsFuchsianRegularPoint z := by
  intro g
  constructor
  · intro hg
    apply hz0
    calc
      coordinate z = coordinate (fuchsianSourceAction g • z) :=
        (hinvariant g z).symm
      _ = coordinate fuchsianOneFixedPoint := congrArg coordinate hg
      _ = 0 := hone
  · intro hg
    apply hz1
    calc
      coordinate z = coordinate (fuchsianSourceAction g • z) :=
        (hinvariant g z).symm
      _ = coordinate fuchsianTwoFixedPoint := congrArg coordinate hg
      _ = 1 := htwo

/-- Exact order-three source branching follows automatically from exact orbit fibres. -/
noncomputable def automatic_branch_one
    (coordinate : UpperHalfPlane → ℂ)
    (hcoordinate : MDiff coordinate)
    (hinvariant : ∀ g z,
      coordinate (fuchsianSourceAction g • z) = coordinate z)
    (hfibres : ∀ z w,
      coordinate z = coordinate w ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w)
    (hone : coordinate fuchsianOneFixedPoint = 0)
    (htwo : coordinate fuchsianTwoFixedPoint = 1) :
    HasExactHolomorphicBranchAt coordinate fuchsianOneFixedPoint 0 3 := by
  let H : ℂ → ℂ := fun w ↦
    ellipticChartFunction coordinate fuchsianOneFixedPoint w - 0
  obtain ⟨hfinite, hbound⟩ := ellipticChartFunction_order_le_stabilizer_card
    (α := CyclicThree) Monoid.Coprod.inl coordinate hcoordinate hinvariant hfibres
    fuchsianOneFixedPoint fuchsianTwoFixedPoint 0 1 hone htwo (by norm_num)
    (fun z hz0 hz1 ↦
      isFuchsianRegularPoint_of_coordinate_ne_ellipticValues coordinate hinvariant
        hone htwo hz0 hz1)
    establishedFuchsianOneStabilizerExact
  change analyticOrderAt H 0 ≠ ⊤ at hfinite
  change analyticOrderNatAt H 0 ≤ Fintype.card CyclicThree at hbound
  have hH : AnalyticAt ℂ H 0 :=
    (ellipticChartFunction_analyticAt_zero hcoordinate fuchsianOneFixedPoint).sub
      analyticAt_const
  have hzero : H 0 = 0 := by
    simp [H, ellipticChartFunction, cayleyRawInverse_zero, hone]
  have hrotate :
      (fun w ↦ H (orderThreeMultiplier * w)) =ᶠ[nhds (0 : ℂ)] H := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball 0 1 by simp)]
      with w hw
    have hwnorm : ‖w‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hw
    change coordinate (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianOneFixedPoint (orderThreeMultiplier * w))) - 0 =
      coordinate (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianOneFixedPoint w)) - 0
    rw [cayleyRawChart_orderThree_rotate hwnorm]
    exact congrArg (fun q : ℂ ↦ q - 0)
      (hinvariant g₁
        (UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w)))
  have hbound' : analyticOrderNatAt H 0 ≤ 3 := by
    simpa using hbound
  have horder : analyticOrderAt H 0 = ((3 : ℕ) : ℕ∞) := by
    have hnat := Reflection.scalarCornerLocalDegree_orderThree
      hH hfinite hzero hrotate hbound'
    exact (Nat.cast_analyticOrderNatAt hfinite).symm.trans (by simp [hnat])
  exact hasExactHolomorphicBranchAt_of_cayley_order hcoordinate
    fuchsianOneFixedPoint 0 3 (by norm_num)
    (by
      intro h
      have hx := congrFun h fuchsianTwoFixedPoint
      rw [htwo] at hx
      norm_num at hx)
    (by simpa only [H] using horder)

/-- Exact order-four source branching follows automatically from exact orbit fibres. -/
noncomputable def automatic_branch_two
    (coordinate : UpperHalfPlane → ℂ)
    (hcoordinate : MDiff coordinate)
    (hinvariant : ∀ g z,
      coordinate (fuchsianSourceAction g • z) = coordinate z)
    (hfibres : ∀ z w,
      coordinate z = coordinate w ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w)
    (hone : coordinate fuchsianOneFixedPoint = 0)
    (htwo : coordinate fuchsianTwoFixedPoint = 1) :
    HasExactHolomorphicBranchAt coordinate fuchsianTwoFixedPoint 1 4 := by
  let H : ℂ → ℂ := fun w ↦
    ellipticChartFunction coordinate fuchsianTwoFixedPoint w - 1
  obtain ⟨hfinite, hbound⟩ := ellipticChartFunction_order_le_stabilizer_card
    (α := CyclicFour) Monoid.Coprod.inr coordinate hcoordinate hinvariant hfibres
    fuchsianTwoFixedPoint fuchsianOneFixedPoint 1 0 htwo hone (by norm_num)
    (fun z hz1 hz0 ↦
      isFuchsianRegularPoint_of_coordinate_ne_ellipticValues coordinate hinvariant
        hone htwo hz0 hz1)
    establishedFuchsianTwoStabilizerExact
  change analyticOrderAt H 0 ≠ ⊤ at hfinite
  change analyticOrderNatAt H 0 ≤ Fintype.card CyclicFour at hbound
  have hH : AnalyticAt ℂ H 0 :=
    (ellipticChartFunction_analyticAt_zero hcoordinate fuchsianTwoFixedPoint).sub
      analyticAt_const
  have hzero : H 0 = 0 := by
    simp [H, ellipticChartFunction, cayleyRawInverse_zero, htwo]
  have hrotate :
      (fun w ↦ H (orderFourMultiplier * w)) =ᶠ[nhds (0 : ℂ)] H := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball 0 1 by simp)]
      with w hw
    have hwnorm : ‖w‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hw
    change coordinate (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianTwoFixedPoint (orderFourMultiplier * w))) - 1 =
      coordinate (UpperHalfPlane.ofComplex
        (cayleyRawInverse fuchsianTwoFixedPoint w)) - 1
    rw [cayleyRawChart_orderFour_rotate hwnorm]
    exact congrArg (fun q : ℂ ↦ q - 1)
      (hinvariant g₂
        (UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w)))
  have hbound' : analyticOrderNatAt H 0 ≤ 4 := by
    simpa using hbound
  have horder : analyticOrderAt H 0 = ((4 : ℕ) : ℕ∞) := by
    have hnat := Reflection.scalarCornerLocalDegree_orderFour
      hH hfinite hzero hrotate hbound'
    exact (Nat.cast_analyticOrderNatAt hfinite).symm.trans (by simp [hnat])
  exact hasExactHolomorphicBranchAt_of_cayley_order hcoordinate
    fuchsianTwoFixedPoint 1 4 (by norm_num)
    (by
      intro h
      have hx := congrFun h fuchsianOneFixedPoint
      rw [hone] at hx
      norm_num at hx)
    (by simpa only [H] using horder)


end SphereSixComplex.Periods.SourceAutomaticBranch
