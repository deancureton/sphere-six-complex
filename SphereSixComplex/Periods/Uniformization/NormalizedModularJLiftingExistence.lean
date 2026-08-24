module

public import SphereSixComplex.Periods.Uniformization.NormalizedModularJMarkedMonodromy
import all SphereSixComplex.Periods.Uniformization.NormalizedModularJMarkedMonodromy
public import SphereSixComplex.Periods.Uniformization.BranchedActionEquivariance
import all SphereSixComplex.Periods.Uniformization.BranchedActionEquivariance
public import SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent
import all SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent
public import SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSchwarzPick
import all SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSchwarzPick
public import SphereSixComplex.Periods.Uniformization.ModularEllipticAdjacency
import all SphereSixComplex.Periods.Uniformization.ModularEllipticAdjacency
public import SphereSixComplex.TriangleGroup.ModularParameter
import all SphereSixComplex.TriangleGroup.ModularParameter
public import SphereSixComplex.Periods.LocalOrbifoldCompatibility
import all SphereSixComplex.Periods.LocalOrbifoldCompatibility

@[expose] public section

/-!
# The normalized Fuchsian modular-J lift

This file supplies the analytic-order and marked-action assembly needed to turn a globally
holomorphic lift of the exact quotient-coordinate equation into the lift with the prescribed
two generator labels.  The remaining global normalization is isolated at the bottom, where the
Schwarz--Pick estimate is combined with the modular elliptic adjacency classification.
-/

noncomputable section

namespace SphereSixComplex.Periods.NormalizedModularJLiftingExistence

open Complex Filter Function Matrix Metric Set Topology UpperHalfPlane
open scoped Manifold MatrixGroups
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open LocalModularJSolutions
open SolutionGermDeckTransitivity
open NormalizedModularJGlobalLift
open NormalizedModularJMarkedMonodromy
open UpperHalfPlaneSchwarzPick
open ModularEllipticAdjacency
open TauCeti

/-! ## Intrinsic analytic order of an exact manifold branch -/

/-- The ambient-complex representative of the supplied branch uniformizer has nonzero
derivative.  This is extracted from the local inverse identities, so it is independent of the
particular manifold chart used in `IsLocalDiffeomorphAt`. -/
theorem branchUniformizer_comp_ofComplex_deriv_ne_zero
    {f : UpperHalfPlane → ℂ} {center : UpperHalfPlane}
    {value : ℂ} {order : ℕ}
    (h : HasExactHolomorphicBranchAt f center value order) :
    deriv (h.uniformizer ∘ UpperHalfPlane.ofComplex) (center : ℂ) ≠ 0 := by
  let u : ℂ → ℂ := h.uniformizer ∘ UpperHalfPlane.ofComplex
  let e : ℂ → ℂ := fun w ↦
    (h.uniformizer_isLocalDiffeomorph.localInverse w : ℂ)
  have hu : AnalyticAt ℂ u (center : ℂ) :=
    branchUniformizer_comp_ofComplex_analyticAt h
  have he : AnalyticAt ℂ e 0 := branchLocalInverse_coe_analyticAt h
  have he0 : e 0 = (center : ℂ) := by
    change (h.uniformizer_isLocalDiffeomorph.localInverse 0 : ℂ) = (center : ℂ)
    apply congrArg ((↑) : UpperHalfPlane → ℂ)
    have hleft := h.uniformizer_isLocalDiffeomorph.localInverse_left_inv
      h.uniformizer_isLocalDiffeomorph.localInverse_mem_target
    simpa [h.uniformizer_center] using hleft
  have hue : (u ∘ e) =ᶠ[nhds (0 : ℂ)] id := by
    have hright :
        h.uniformizer ∘ h.uniformizer_isLocalDiffeomorph.localInverse =ᶠ[
          nhds (0 : ℂ)] id := by
      simpa [h.uniformizer_center] using
        h.uniformizer_isLocalDiffeomorph.localInverse_eventuallyEq_right
    filter_upwards [hright] with w hw
    simpa [u, e, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hw
  have hchain : deriv (u ∘ e) 0 = deriv u (center : ℂ) * deriv e 0 := by
    have hc := ((he0 ▸ hu).differentiableAt.hasDerivAt.comp 0
      he.differentiableAt.hasDerivAt).deriv
    simpa [he0] using hc
  have hid : deriv (u ∘ e) 0 = 1 := by
    rw [Filter.EventuallyEq.deriv_eq hue]
    simp
  intro hz
  rw [hchain, hz, zero_mul] at hid
  exact zero_ne_one hid

/-- Exact branch order is intrinsic: in the ambient complex coordinate the centered branch has
the order recorded by `HasExactHolomorphicBranchAt`. -/
theorem exactBranch_ambient_analyticOrderAt
    {f : UpperHalfPlane → ℂ} {center : UpperHalfPlane}
    {value : ℂ} {order : ℕ}
    (h : HasExactHolomorphicBranchAt f center value order)
    (hf : MDiff f) :
    analyticOrderAt
        (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value)
        (center : ℂ) = order := by
  let F : ℂ → ℂ := fun w ↦ f (UpperHalfPlane.ofComplex w) - value
  let u : ℂ → ℂ := h.uniformizer ∘ UpperHalfPlane.ofComplex
  let v : ℂ → ℂ := h.unit ∘ UpperHalfPlane.ofComplex
  have hcenter : UpperHalfPlane.ofComplex (center : ℂ) = center :=
    UpperHalfPlane.ofComplex_apply center
  have hFan : AnalyticAt ℂ F (center : ℂ) := by
    have hcomp : MDiff (fun z : UpperHalfPlane ↦ f z - value) :=
      hf.sub mdifferentiable_const
    exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomp center.im_pos
  have hu : AnalyticAt ℂ u (center : ℂ) :=
    branchUniformizer_comp_ofComplex_analyticAt h
  have hu0 : u (center : ℂ) = 0 := by
    simp [u, hcenter, h.uniformizer_center]
  have huderiv : deriv u (center : ℂ) ≠ 0 :=
    branchUniformizer_comp_ofComplex_deriv_ne_zero h
  have hv : AnalyticAt ℂ v (center : ℂ) := by
    let v' : ℂ → ℂ := h.complexUnit ∘ u
    have hv' : AnalyticAt ℂ v' (center : ℂ) := by
      apply (show AnalyticAt ℂ h.complexUnit (u (center : ℂ)) by
        rw [hu0]
        exact h.complexUnit_analyticAt hf).comp hu
    have hleft :=
      h.uniformizer_isLocalDiffeomorph.localInverse_eventuallyEq_left
    have hofTend' : Tendsto UpperHalfPlane.ofComplex
        (nhds (center : ℂ)) (nhds center) := by
      have hc := (UpperHalfPlane.mdifferentiableAt_ofComplex center.im_pos).continuousAt
      change Tendsto UpperHalfPlane.ofComplex (nhds (center : ℂ))
        (nhds (UpperHalfPlane.ofComplex (center : ℂ))) at hc
      simpa only [UpperHalfPlane.ofComplex_apply] using hc
    have hpull := hleft.comp_tendsto hofTend'
    apply hv'.congr
    filter_upwards [hpull] with w hw
    simp only [v', HasExactHolomorphicBranchAt.complexUnit, v, u,
      Function.comp_apply]
    have hw' : h.uniformizer_isLocalDiffeomorph.localInverse
        (h.uniformizer (UpperHalfPlane.ofComplex w)) = UpperHalfPlane.ofComplex w := by
      simpa only [Function.comp_apply, id_eq] using hw
    rw [hw']
  have hv0 : v (center : ℂ) ≠ 0 := by
    simpa [v, hcenter] using h.unit_ne_zero
  have hofTend : Tendsto UpperHalfPlane.ofComplex
      (nhds (center : ℂ)) (nhds center) := by
    have hc := (UpperHalfPlane.mdifferentiableAt_ofComplex center.im_pos).continuousAt
    change Tendsto UpperHalfPlane.ofComplex (nhds (center : ℂ))
      (nhds (UpperHalfPlane.ofComplex (center : ℂ))) at hc
    rw [hcenter] at hc
    exact hc
  have hfactor : F =ᶠ[nhds (center : ℂ)] u ^ order * v := by
    have hpull := hofTend h.factorization
    filter_upwards [hpull] with w hw
    simpa [F, u, v, Function.comp_apply] using hw
  have huOrder : analyticOrderAt u (center : ℂ) = 1 := by
    simpa [hu0] using hu.analyticOrderAt_sub_eq_one_of_deriv_ne_zero huderiv
  have hvOrder : analyticOrderAt v (center : ℂ) = 0 :=
    hv.analyticOrderAt_eq_zero.mpr hv0
  rw [analyticOrderAt_congr hfactor]
  have hpow := analyticOrderAt_pow hu order
  have hmul := analyticOrderAt_mul (hu.pow order) hv
  rw [hmul, hpow, huOrder, hvOrder]
  simp

/-! ## Ambient representatives and the two elliptic multipliers -/

/-- Ambient-complex representative of an upper-half-plane-valued map. -/
def upperHalfPlaneMapComplex (tau : UpperHalfPlane → UpperHalfPlane) : ℂ → ℂ :=
  fun w ↦ (tau (UpperHalfPlane.ofComplex w) : ℂ)

/-- Ambient-complex representative of the prescribed target modular action. -/
def targetActionComplex (g : Delta) : ℂ → ℂ :=
  fun w ↦ ((rhoTauReal g • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)

theorem upperHalfPlaneMapComplex_analyticAt
    {tau : UpperHalfPlane → UpperHalfPlane} (htau : MDiff tau)
    (z : UpperHalfPlane) :
    AnalyticAt ℂ (upperHalfPlaneMapComplex tau) (z : ℂ) :=
  GlobalModularDeckComparison.coe_comp_ofComplex_analyticOnNhd htau (z : ℂ) z.im_pos

theorem targetActionComplex_analyticAt (g : Delta) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticAt ℂ (targetActionComplex g) z := by
  have hact : MDiff (fun t : UpperHalfPlane ↦ rhoTauReal g • t) :=
    UpperHalfPlane.mdifferentiable_smul (by simp [rhoTauReal, modularToReal])
  have hcomplex : MDiff (fun t : UpperHalfPlane ↦
      ((rhoTauReal g • t : UpperHalfPlane) : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hact
  exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomplex hz

private theorem eventually_ofComplex_eq_on_upperHalfPlane (z : UpperHalfPlane) :
    (fun w : ℂ ↦ (UpperHalfPlane.ofComplex w : ℂ)) =ᶠ[nhds (z : ℂ)] id := by
  have hupper : UpperHalfPlane.upperHalfPlaneSet ∈ nhds (z : ℂ) :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos
  filter_upwards [hupper] with w hw
  simpa only [id_eq] using congrArg ((↑) : UpperHalfPlane → ℂ)
    (UpperHalfPlane.ofComplex_apply_of_im_pos hw)

theorem sourceActionComplex_gOne_deriv :
    deriv (sourceActionComplex g₁) (fuchsianOneFixedPoint : ℂ) =
      orderThreeMultiplier := by
  let R : ℂ → ℂ := (fun w ↦ w - 1) / id
  have heq : sourceActionComplex g₁ =ᶠ[
      nhds (fuchsianOneFixedPoint : ℂ)] R := by
    filter_upwards [eventually_ofComplex_eq_on_upperHalfPlane fuchsianOneFixedPoint]
      with w hw
    calc
      ((fuchsianSourceAction g₁ • UpperHalfPlane.ofComplex w :
          UpperHalfPlane) : ℂ) =
          ((UpperHalfPlane.ofComplex w : ℂ) - 1) /
            (UpperHalfPlane.ofComplex w : ℂ) :=
        fuchsianSourceAction_g₁_apply (UpperHalfPlane.ofComplex w)
      _ = R w := by simpa [R] using congrArg (fun q : ℂ ↦ (q - 1) / q) hw
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hne : (fuchsianOneFixedPoint : ℂ) ≠ 0 := fuchsianOneFixedPoint.ne_zero
  have hd := (((hasDerivAt_id (fuchsianOneFixedPoint : ℂ)).sub_const 1).div
    (hasDerivAt_id (fuchsianOneFixedPoint : ℂ)) hne).deriv
  have hdR : deriv R (fuchsianOneFixedPoint : ℂ) =
      (1 * (fuchsianOneFixedPoint : ℂ) -
        ((fuchsianOneFixedPoint : ℂ) - 1) * 1) /
          (fuchsianOneFixedPoint : ℂ) ^ 2 := by
    simpa [R] using hd
  rw [hdR]
  rw [show 1 * (fuchsianOneFixedPoint : ℂ) -
      ((fuchsianOneFixedPoint : ℂ) - 1) * 1 = 1 by ring]
  apply (div_eq_iff (pow_ne_zero 2 hne)).2
  apply Complex.ext <;>
    norm_num [fuchsianOneFixedPoint, orderThreeMultiplier, Complex.mul_re,
      Complex.mul_im, pow_two]
  all_goals
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hcube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
      rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, hs]
    ring_nf
    simp only [hs, hcube]
    ring

theorem targetActionComplex_gOne_deriv :
    deriv (targetActionComplex g₁) (ellipticThreeParameter : ℂ) =
      orderThreeMultiplier := by
  have heq : targetActionComplex g₁ =ᶠ[
      nhds (ellipticThreeParameter : ℂ)] sourceActionComplex g₁ := by
    filter_upwards [] with w
    unfold targetActionComplex sourceActionComplex
    rw [rhoTauReal_g₁, fuchsianSourceAction_g₁,
      fuchsianOnePerm_eq_targetOnePerm]
    rfl
  rw [Filter.EventuallyEq.deriv_eq heq, ← fuchsianOneFixedPoint_eq_ellipticThreeParameter]
  exact sourceActionComplex_gOne_deriv

theorem sourceActionComplex_gTwo_deriv :
    deriv (sourceActionComplex g₂) (fuchsianTwoFixedPoint : ℂ) =
      orderFourMultiplier := by
  let R : ℂ → ℂ := (fun _ ↦ -1) / (fun w ↦ w + (Real.sqrt 2 : ℂ))
  have heq : sourceActionComplex g₂ =ᶠ[
      nhds (fuchsianTwoFixedPoint : ℂ)] R := by
    filter_upwards [eventually_ofComplex_eq_on_upperHalfPlane fuchsianTwoFixedPoint]
      with w hw
    calc
      ((fuchsianSourceAction g₂ • UpperHalfPlane.ofComplex w :
          UpperHalfPlane) : ℂ) =
          -1 / ((UpperHalfPlane.ofComplex w : ℂ) + Real.sqrt 2) :=
        fuchsianSourceAction_g₂_apply (UpperHalfPlane.ofComplex w)
      _ = R w := by
        simpa [R] using congrArg (fun q : ℂ ↦ -1 / (q + Real.sqrt 2)) hw
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hne : (fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num [fuchsianTwoFixedPoint] at him
  have hd := ((hasDerivAt_const (x := (fuchsianTwoFixedPoint : ℂ)) (-1 : ℂ)).div
    ((hasDerivAt_id (fuchsianTwoFixedPoint : ℂ)).add_const (Real.sqrt 2 : ℂ))
      hne).deriv
  have hdR : deriv R (fuchsianTwoFixedPoint : ℂ) =
      (0 * ((fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2) - (-1) * 1) /
        ((fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2) ^ 2 := by
    simpa [R] using hd
  rw [hdR]
  norm_num only [zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
  apply (div_eq_iff (pow_ne_zero 2 hne)).2
  apply Complex.ext <;>
    norm_num [fuchsianTwoFixedPoint, orderFourMultiplier, Complex.mul_re,
      Complex.mul_im, pow_two]
  all_goals
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    ring_nf <;> norm_num [hs]

theorem targetActionComplex_gTwo_deriv :
    deriv (targetActionComplex g₂) (UpperHalfPlane.I : ℂ) = -1 := by
  let R : ℂ → ℂ := (fun _ ↦ -1) / id
  have heq : targetActionComplex g₂ =ᶠ[nhds (UpperHalfPlane.I : ℂ)] R := by
    filter_upwards [eventually_ofComplex_eq_on_upperHalfPlane UpperHalfPlane.I]
      with w hw
    change ((rhoTauReal g₂ • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) = R w
    rw [rhoTauReal_g₂_smul]
    simpa [R] using congrArg (fun q : ℂ ↦ -1 / q) hw
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hne : (UpperHalfPlane.I : ℂ) ≠ 0 := UpperHalfPlane.I.ne_zero
  have hd := ((hasDerivAt_const (x := (UpperHalfPlane.I : ℂ)) (-1 : ℂ)).div
    (hasDerivAt_id (UpperHalfPlane.I : ℂ)) hne).deriv
  rw [hd]
  norm_num [UpperHalfPlane.I, Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-! ## Analytic order of a lift between two exact branches -/

private theorem enat_eq_of_nsmul_eq_nat
    {x : ℕ∞} {m n k : ℕ} (hm : m ≠ 0) (hmk : m * k = n)
    (hx : m • x = n) : x = k := by
  have hxfin : x ≠ ⊤ := by
    intro htop
    rw [htop, nsmul_eq_mul] at hx
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    simp [hmpos.ne'] at hx
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hxfin
  apply ENat.natCast_inj.mpr
  rw [nsmul_eq_mul, ← ENat.natCast_mul] at hx
  have hdn : m * d = n := ENat.natCast_inj.mp hx
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) (hdn.trans hmk.symm)

/-- If a holomorphic upper-half-plane map solves the exact quotient equation and maps an exact
source branch center to an exact target branch center, then its target power coordinate has the
quotient of the two ramification orders. -/
theorem exactBranch_lift_analyticOrderAt
    (C : ExactFuchsianOrbifoldCoordinate)
    {target : UpperHalfPlane → ℂ}
    {a b : UpperHalfPlane} {value : ℂ} {n m k : ℕ}
    (hsource : HasExactHolomorphicBranchAt C.coordinate a value n)
    (htarget : HasExactHolomorphicBranchAt target b value m)
    (htargetMD : MDiff target)
    (tau : UpperHalfPlane → UpperHalfPlane) (htau : MDiff tau)
    (hEq : ∀ z, target (tau z) = C.coordinate z)
    (htauab : tau a = b)
    (hm : m ≠ 0) (hmk : m * k = n) :
    ∃ r > 0, ∃ phi : ℂ → ℂ,
      AnalyticAt ℂ phi (b : ℂ) ∧ phi (b : ℂ) = 0 ∧
      deriv phi (b : ℂ) ≠ 0 ∧
      analyticOrderAt (phi ∘ upperHalfPlaneMapComplex tau) (a : ℂ) = k ∧
      (∀ z ∈ ball (b : ℂ) r,
        target (UpperHalfPlane.ofComplex z) - value = phi z ^ m) := by
  let targetF : ℂ → ℂ :=
    fun z ↦ target (UpperHalfPlane.ofComplex z) - value
  have htargetAn : AnalyticAt ℂ targetF (b : ℂ) := by
    have hMD : MDiff (fun z : UpperHalfPlane ↦ target z - value) :=
      htargetMD.sub mdifferentiable_const
    exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hMD b.im_pos
  have htargetOrder : analyticOrderAt targetF (b : ℂ) = m :=
    exactBranch_ambient_analyticOrderAt htarget htargetMD
  obtain ⟨r, hr, phi, hphiDiff, -, hphi0, hphiDeriv, hchart⟩ :=
    exists_powerChart_of_analyticOrderAt htargetAn htargetOrder hm
  have hphiAn : AnalyticAt ℂ phi (b : ℂ) :=
    hphiDiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  let T : ℂ → ℂ := phi ∘ upperHalfPlaneMapComplex tau
  have htauAn : AnalyticAt ℂ (upperHalfPlaneMapComplex tau) (a : ℂ) :=
    upperHalfPlaneMapComplex_analyticAt htau a
  have htauValue : upperHalfPlaneMapComplex tau (a : ℂ) = (b : ℂ) := by
    simp [upperHalfPlaneMapComplex, UpperHalfPlane.ofComplex_apply, htauab]
  have hTAn : AnalyticAt ℂ T (a : ℂ) := by
    exact (htauValue ▸ hphiAn).comp htauAn
  have htauTend : Tendsto (upperHalfPlaneMapComplex tau)
      (nhds (a : ℂ)) (nhds (b : ℂ)) := by
    have hc := htauAn.continuousAt
    change Tendsto (upperHalfPlaneMapComplex tau) (nhds (a : ℂ))
      (nhds (upperHalfPlaneMapComplex tau (a : ℂ))) at hc
    rw [htauValue] at hc
    exact hc
  have htauBall : ∀ᶠ z in nhds (a : ℂ),
      upperHalfPlaneMapComplex tau z ∈ ball (b : ℂ) r :=
    htauTend (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hupper : UpperHalfPlane.upperHalfPlaneSet ∈ nhds (a : ℂ) :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos
  let sourceF : ℂ → ℂ :=
    fun z ↦ C.coordinate (UpperHalfPlane.ofComplex z) - value
  have hpowerEq : T ^ m =ᶠ[nhds (a : ℂ)] sourceF := by
    filter_upwards [htauBall, hupper] with z hzball hzupper
    have hc := hchart (upperHalfPlaneMapComplex tau z) hzball
    change (phi (upperHalfPlaneMapComplex tau z)) ^ m = sourceF z
    rw [← hc]
    simp only [targetF, upperHalfPlaneMapComplex, sourceF]
    rw [UpperHalfPlane.ofComplex_apply]
    exact congrArg (fun q : ℂ ↦ q - value)
      (hEq (UpperHalfPlane.ofComplex z))
  have hsourceOrder : analyticOrderAt sourceF (a : ℂ) = n :=
    exactBranch_ambient_analyticOrderAt hsource C.coordinate_holomorphic
  have horderMultiple : m • analyticOrderAt T (a : ℂ) = n := by
    calc
      m • analyticOrderAt T (a : ℂ) = analyticOrderAt (T ^ m) (a : ℂ) :=
        (analyticOrderAt_pow hTAn m).symm
      _ = analyticOrderAt sourceF (a : ℂ) := analyticOrderAt_congr hpowerEq
      _ = n := hsourceOrder
  refine ⟨r, hr, phi, hphiAn, hphi0, hphiDeriv,
    enat_eq_of_nsmul_eq_nat hm hmk horderMultiple, hchart⟩

/-! ## The two marked elliptic germs -/

private theorem normalizedCoordinate_action_comparison
    (C : ExactFuchsianOrbifoldCoordinate)
    (tau : UpperHalfPlane → UpperHalfPlane)
    (hEq : ∀ z, normalizedModularJCoordinate (tau z) = C.coordinate z)
    (g : Delta) (z : ℂ) :
    normalizedModularJCoordinate
        (UpperHalfPlane.ofComplex
          (upperHalfPlaneMapComplex tau (sourceActionComplex g z))) =
      normalizedModularJCoordinate
        (UpperHalfPlane.ofComplex
          (targetActionComplex g (upperHalfPlaneMapComplex tau z))) := by
  simp only [upperHalfPlaneMapComplex, sourceActionComplex, targetActionComplex,
    UpperHalfPlane.ofComplex_apply]
  calc
    normalizedModularJCoordinate
        (tau (fuchsianSourceAction g • UpperHalfPlane.ofComplex z)) =
        C.coordinate (fuchsianSourceAction g • UpperHalfPlane.ofComplex z) :=
      hEq _
    _ = C.coordinate (UpperHalfPlane.ofComplex z) :=
      C.coordinate_invariant g _
    _ = normalizedModularJCoordinate (tau (UpperHalfPlane.ofComplex z)) :=
      (hEq _).symm
    _ = normalizedModularJCoordinate
        (rhoTauReal g • tau (UpperHalfPlane.ofComplex z)) := by
      exact (normalizedModularJCoordinate_invariant (rhoTau g)
        (tau (UpperHalfPlane.ofComplex z))).symm

/-- Once a global quotient lift sends the source order-three center to the canonical modular
order-three center, the first prescribed generator identity holds as a germ. -/
theorem orderThree_generator_germ_of_center_value
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate)
    (tau : UpperHalfPlane → UpperHalfPlane) (htau : MDiff tau)
    (hEq : ∀ z, normalizedModularJCoordinate (tau z) = C.coordinate z)
    (hvalue : tau fuchsianOneFixedPoint = ellipticThreeParameter) :
    (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₁ • UpperHalfPlane.ofComplex w) : ℂ))
      =ᶠ[nhds (fuchsianOneFixedPoint : ℂ)]
    (fun w : ℂ ↦
        ((rhoTauReal g₁ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)) := by
  obtain ⟨r, hr, phi, hphiAn, hphi0, hphiDeriv, hTorder, hchart⟩ :=
    exactBranch_lift_analyticOrderAt C C.branch_one J.branch_three
      normalizedModularJCoordinate_holomorphic tau htau hEq hvalue
      (by norm_num) (by norm_num : 3 * 1 = 3)
  let A : ℂ → ℂ := sourceActionComplex g₁
  let B : ℂ → ℂ := targetActionComplex g₁
  let T : ℂ → ℂ := upperHalfPlaneMapComplex tau
  have hAAn : AnalyticAt ℂ A (fuchsianOneFixedPoint : ℂ) :=
    sourceActionComplex_analyticAt g₁ fuchsianOneFixedPoint.im_pos
  have hAFix : A (fuchsianOneFixedPoint : ℂ) =
      (fuchsianOneFixedPoint : ℂ) := by
    unfold A sourceActionComplex
    rw [UpperHalfPlane.ofComplex_apply]
    exact congrArg ((↑) : UpperHalfPlane → ℂ) fuchsianOneFixedPoint_fixed
  have hADeriv : deriv A (fuchsianOneFixedPoint : ℂ) = orderThreeMultiplier :=
    sourceActionComplex_gOne_deriv
  have hADeriv0 : deriv A (fuchsianOneFixedPoint : ℂ) ≠ 0 := by
    rw [hADeriv]
    exact norm_pos_iff.mp (by rw [norm_orderThreeMultiplier]; norm_num)
  have hBAn : AnalyticAt ℂ B (ellipticThreeParameter : ℂ) :=
    targetActionComplex_analyticAt g₁ ellipticThreeParameter.im_pos
  have hBFix : B (ellipticThreeParameter : ℂ) =
      (ellipticThreeParameter : ℂ) := by
    unfold B targetActionComplex
    rw [UpperHalfPlane.ofComplex_apply]
    apply congrArg ((↑) : UpperHalfPlane → ℂ)
    exact (rhoTauReal_gOne_fixed_iff ellipticThreeParameter).2 rfl
  have hBDeriv : deriv B (ellipticThreeParameter : ℂ) = orderThreeMultiplier :=
    targetActionComplex_gOne_deriv
  have hBDeriv0 : deriv B (ellipticThreeParameter : ℂ) ≠ 0 := by
    rw [hBDeriv]
    exact norm_pos_iff.mp (by rw [norm_orderThreeMultiplier]; norm_num)
  have hTAn : AnalyticAt ℂ T (fuchsianOneFixedPoint : ℂ) :=
    upperHalfPlaneMapComplex_analyticAt htau fuchsianOneFixedPoint
  have hTValue : T (fuchsianOneFixedPoint : ℂ) =
      (ellipticThreeParameter : ℂ) := by
    simp [T, upperHalfPlaneMapComplex, UpperHalfPlane.ofComplex_apply, hvalue]
  have hleftAn : AnalyticAt ℂ (T ∘ A) (fuchsianOneFixedPoint : ℂ) :=
    (hAFix ▸ hTAn).comp hAAn
  have hrightAn : AnalyticAt ℂ (B ∘ T) (fuchsianOneFixedPoint : ℂ) :=
    (hTValue ▸ hBAn).comp hTAn
  have hleftValue : (T ∘ A) (fuchsianOneFixedPoint : ℂ) =
      (ellipticThreeParameter : ℂ) := by simp [Function.comp_apply, hAFix, hTValue]
  have hrightValue : (B ∘ T) (fuchsianOneFixedPoint : ℂ) =
      (ellipticThreeParameter : ℂ) := by simp [Function.comp_apply, hTValue, hBFix]
  have hleftBall : ∀ᶠ z in nhds (fuchsianOneFixedPoint : ℂ),
      (T ∘ A) z ∈ ball (ellipticThreeParameter : ℂ) r := by
    have hc := hleftAn.continuousAt
    change Tendsto (T ∘ A) (nhds (fuchsianOneFixedPoint : ℂ))
      (nhds ((T ∘ A) (fuchsianOneFixedPoint : ℂ))) at hc
    rw [hleftValue] at hc
    exact hc (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hrightBall : ∀ᶠ z in nhds (fuchsianOneFixedPoint : ℂ),
      (B ∘ T) z ∈ ball (ellipticThreeParameter : ℂ) r := by
    have hc := hrightAn.continuousAt
    change Tendsto (B ∘ T) (nhds (fuchsianOneFixedPoint : ℂ))
      (nhds ((B ∘ T) (fuchsianOneFixedPoint : ℂ))) at hc
    rw [hrightValue] at hc
    exact hc (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hpow : (fun z ↦ phi (T (A z)) ^ 3) =ᶠ[
      nhds (fuchsianOneFixedPoint : ℂ)] fun z ↦ phi (B (T z)) ^ 3 := by
    filter_upwards [hleftBall, hrightBall] with z hzL hzR
    have hL := hchart ((T ∘ A) z) hzL
    have hR := hchart ((B ∘ T) z) hzR
    simp only [Function.comp_apply] at hL hR
    rw [← hL, ← hR]
    exact congrArg (fun q : ℂ ↦ q - 0)
      (normalizedCoordinate_action_comparison C tau hEq g₁ z)
  have hlocal := TauCeti.eventuallyEq_of_branched_power_action
    hAAn hAFix hADeriv hADeriv0 hBAn hBFix hBDeriv hBDeriv0
    hTAn hTValue hphiAn hphi0 hphiDeriv hTorder
    (by simp) (by norm_num : (3 : ℕ) ≠ 0) hpow
  simpa [A, B, T, upperHalfPlaneMapComplex, sourceActionComplex,
    targetActionComplex, UpperHalfPlane.ofComplex_apply] using hlocal

/-- Once a global quotient lift sends the source order-four center to the canonical modular
order-two center, the second prescribed generator identity holds as a germ.  The lift has local
degree two, which converts the source multiplier `-i` to the target multiplier `-1`. -/
theorem orderFourTwo_generator_germ_of_center_value
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate)
    (tau : UpperHalfPlane → UpperHalfPlane) (htau : MDiff tau)
    (hEq : ∀ z, normalizedModularJCoordinate (tau z) = C.coordinate z)
    (hvalue : tau fuchsianTwoFixedPoint = UpperHalfPlane.I) :
    (fun w : ℂ ↦
        (tau (fuchsianSourceAction g₂ • UpperHalfPlane.ofComplex w) : ℂ))
      =ᶠ[nhds (fuchsianTwoFixedPoint : ℂ)]
    (fun w : ℂ ↦
        ((rhoTauReal g₂ • tau (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)) := by
  obtain ⟨r, hr, phi, hphiAn, hphi0, hphiDeriv, hTorder, hchart⟩ :=
    exactBranch_lift_analyticOrderAt C C.branch_two J.branch_two
      normalizedModularJCoordinate_holomorphic tau htau hEq hvalue
      (by norm_num) (by norm_num : 2 * 2 = 4)
  let A : ℂ → ℂ := sourceActionComplex g₂
  let B : ℂ → ℂ := targetActionComplex g₂
  let T : ℂ → ℂ := upperHalfPlaneMapComplex tau
  have hAAn : AnalyticAt ℂ A (fuchsianTwoFixedPoint : ℂ) :=
    sourceActionComplex_analyticAt g₂ fuchsianTwoFixedPoint.im_pos
  have hAFix : A (fuchsianTwoFixedPoint : ℂ) =
      (fuchsianTwoFixedPoint : ℂ) := by
    unfold A sourceActionComplex
    rw [UpperHalfPlane.ofComplex_apply]
    exact congrArg ((↑) : UpperHalfPlane → ℂ) fuchsianTwoFixedPoint_fixed
  have hADeriv : deriv A (fuchsianTwoFixedPoint : ℂ) = orderFourMultiplier :=
    sourceActionComplex_gTwo_deriv
  have hADeriv0 : deriv A (fuchsianTwoFixedPoint : ℂ) ≠ 0 := by
    rw [hADeriv]
    exact norm_pos_iff.mp (by rw [norm_orderFourMultiplier]; norm_num)
  have hBAn : AnalyticAt ℂ B (UpperHalfPlane.I : ℂ) :=
    targetActionComplex_analyticAt g₂ UpperHalfPlane.I.im_pos
  have hBFix : B (UpperHalfPlane.I : ℂ) = (UpperHalfPlane.I : ℂ) := by
    unfold B targetActionComplex
    rw [UpperHalfPlane.ofComplex_apply]
    exact congrArg ((↑) : UpperHalfPlane → ℂ)
      ((rhoTauReal_gTwo_fixed_iff UpperHalfPlane.I).2 rfl)
  have hBDeriv : deriv B (UpperHalfPlane.I : ℂ) = -1 :=
    targetActionComplex_gTwo_deriv
  have hBDeriv0 : deriv B (UpperHalfPlane.I : ℂ) ≠ 0 := by
    rw [hBDeriv]
    norm_num
  have hTAn : AnalyticAt ℂ T (fuchsianTwoFixedPoint : ℂ) :=
    upperHalfPlaneMapComplex_analyticAt htau fuchsianTwoFixedPoint
  have hTValue : T (fuchsianTwoFixedPoint : ℂ) = (UpperHalfPlane.I : ℂ) := by
    simp [T, upperHalfPlaneMapComplex, UpperHalfPlane.ofComplex_apply, hvalue]
  have hleftAn : AnalyticAt ℂ (T ∘ A) (fuchsianTwoFixedPoint : ℂ) :=
    (hAFix ▸ hTAn).comp hAAn
  have hrightAn : AnalyticAt ℂ (B ∘ T) (fuchsianTwoFixedPoint : ℂ) :=
    (hTValue ▸ hBAn).comp hTAn
  have hleftValue : (T ∘ A) (fuchsianTwoFixedPoint : ℂ) =
      (UpperHalfPlane.I : ℂ) := by simp [Function.comp_apply, hAFix, hTValue]
  have hrightValue : (B ∘ T) (fuchsianTwoFixedPoint : ℂ) =
      (UpperHalfPlane.I : ℂ) := by
    rw [Function.comp_apply, hTValue]
    exact hBFix
  have hleftBall : ∀ᶠ z in nhds (fuchsianTwoFixedPoint : ℂ),
      (T ∘ A) z ∈ ball (UpperHalfPlane.I : ℂ) r := by
    have hc := hleftAn.continuousAt
    change Tendsto (T ∘ A) (nhds (fuchsianTwoFixedPoint : ℂ))
      (nhds ((T ∘ A) (fuchsianTwoFixedPoint : ℂ))) at hc
    rw [hleftValue] at hc
    exact hc (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hrightBall : ∀ᶠ z in nhds (fuchsianTwoFixedPoint : ℂ),
      (B ∘ T) z ∈ ball (UpperHalfPlane.I : ℂ) r := by
    have hc := hrightAn.continuousAt
    change Tendsto (B ∘ T) (nhds (fuchsianTwoFixedPoint : ℂ))
      (nhds ((B ∘ T) (fuchsianTwoFixedPoint : ℂ))) at hc
    rw [hrightValue] at hc
    exact hc (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hpow : (fun z ↦ phi (T (A z)) ^ 2) =ᶠ[
      nhds (fuchsianTwoFixedPoint : ℂ)] fun z ↦ phi (B (T z)) ^ 2 := by
    filter_upwards [hleftBall, hrightBall] with z hzL hzR
    have hL := hchart ((T ∘ A) z) hzL
    have hR := hchart ((B ∘ T) z) hzR
    simp only [Function.comp_apply] at hL hR
    rw [← hL, ← hR]
    exact congrArg (fun q : ℂ ↦ q - 1)
      (normalizedCoordinate_action_comparison C tau hEq g₂ z)
  have hlocal := TauCeti.eventuallyEq_of_branched_power_action
    hAAn hAFix hADeriv hADeriv0 hBAn hBFix hBDeriv hBDeriv0
    hTAn hTValue hphiAn hphi0 hphiDeriv hTorder
    (by norm_num [orderFourMultiplier, pow_two])
    (by norm_num : (2 : ℕ) ≠ 0) hpow
  simpa [A, B, T, upperHalfPlaneMapComplex, sourceActionComplex,
    targetActionComplex, UpperHalfPlane.ofComplex_apply] using hlocal

/-! ## Global two-point normalization and final assembly -/

/-- A modular postcomposition preserves holomorphicity of an upper-half-plane map. -/
private theorem mdiff_modularDeck_comp
    (g : Delta) {tau : UpperHalfPlane → UpperHalfPlane} (htau : MDiff tau) :
    MDiff (fun z ↦ modularDeckHomeomorph g (tau z)) := by
  have hdeck : MDiff (fun z : UpperHalfPlane ↦ rhoTauReal g • z) :=
    UpperHalfPlane.mdifferentiable_smul (by simp [rhoTauReal, modularToReal])
  exact hdeck.comp htau

/-- Every exact global quotient lift can be modularly normalized at both elliptic centers.
Schwarz--Pick and the integer adjacency classification reduce the residual order-three
stabilizer ambiguity to its three powers. -/
theorem exists_global_lift_with_canonical_elliptic_values
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ tau : UpperHalfPlane → UpperHalfPlane,
      MDiff tau ∧
      (∀ z, normalizedModularJCoordinate (tau z) = C.coordinate z) ∧
      tau fuchsianOneFixedPoint = ellipticThreeParameter ∧
      tau fuchsianTwoFixedPoint = UpperHalfPlane.I := by
  obtain ⟨tau0, htau0, hEq0⟩ := exists_global_lift J C
  have hfiberOne : normalizedModularJCoordinate (tau0 fuchsianOneFixedPoint) =
      normalizedModularJCoordinate ellipticThreeParameter := by
    rw [hEq0, C.coordinate_at_one, J.coordinate_at_three]
  obtain ⟨d, hd⟩ := exists_delta_modularDeck_eq J hfiberOne
  let tau1 : UpperHalfPlane → UpperHalfPlane :=
    fun z ↦ modularDeckHomeomorph d (tau0 z)
  have htau1 : MDiff tau1 := mdiff_modularDeck_comp d htau0
  have hEq1 : ∀ z, normalizedModularJCoordinate (tau1 z) = C.coordinate z := by
    intro z
    rw [show tau1 z = modularDeckHomeomorph d (tau0 z) by rfl,
      normalizedModularJCoordinate_modularDeck, hEq0]
  have htau1One : tau1 fuchsianOneFixedPoint = ellipticThreeParameter := hd
  have hfiberTwo : normalizedModularJCoordinate UpperHalfPlane.I =
      normalizedModularJCoordinate (tau1 fuchsianTwoFixedPoint) := by
    rw [J.coordinate_at_two, hEq1, C.coordinate_at_two]
  obtain ⟨g, hg⟩ := (J.coordinate_eq_iff_orbit UpperHalfPlane.I
    (tau1 fuchsianTwoFixedPoint)).mp hfiberTwo
  have hnorm := norm_halfPlaneToDiscAt_map_le tau1 htau1
    fuchsianOneFixedPoint ellipticThreeParameter fuchsianTwoFixedPoint htau1One
  have hnorm' :
      ‖halfPlaneToDiscAt ellipticThreeParameter
          (((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ))‖ ≤
        ‖halfPlaneToDiscAt ellipticThreeParameter
          (fuchsianTwoFixedPoint : ℂ)‖ := by
    rw [hg]
    simpa only [fuchsianOneFixedPoint_eq_ellipticThreeParameter] using hnorm
  have hnormSq :
      normSq (halfPlaneToDiscAt ellipticThreeParameter
          (((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ))) ≤
        normSq (halfPlaneToDiscAt ellipticThreeParameter
          (fuchsianTwoFixedPoint : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (halfPlaneToDiscAt ellipticThreeParameter
      (((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I :
        UpperHalfPlane) : ℂ))),
      norm_nonneg (halfPlaneToDiscAt ellipticThreeParameter
        (fuchsianTwoFixedPoint : ℂ))]
  have hadj := modular_I_adjacent_under_orderThree g hnormSq
  have hfixOne : rhoTauReal g₁ • ellipticThreeParameter =
      ellipticThreeParameter :=
    (rhoTauReal_gOne_fixed_iff ellipticThreeParameter).2 rfl
  obtain ⟨e, heTwo, heOne⟩ : ∃ e : Delta,
      rhoTauReal e • tau1 fuchsianTwoFixedPoint = UpperHalfPlane.I ∧
      rhoTauReal e • ellipticThreeParameter = ellipticThreeParameter := by
    rcases hadj with hzero | hone | htwo
    · refine ⟨1, ?_, ?_⟩
      · simpa [hg] using hzero
      · simp
    · refine ⟨g₁, ?_, hfixOne⟩
      simpa [hg] using hone
    · refine ⟨g₁ ^ 2, ?_, ?_⟩
      · simpa [hg] using htwo
      · rw [map_pow, pow_two, mul_smul, hfixOne, hfixOne]
  let tau : UpperHalfPlane → UpperHalfPlane :=
    fun z ↦ modularDeckHomeomorph e (tau1 z)
  have htau : MDiff tau := mdiff_modularDeck_comp e htau1
  have hEq : ∀ z, normalizedModularJCoordinate (tau z) = C.coordinate z := by
    intro z
    rw [show tau z = modularDeckHomeomorph e (tau1 z) by rfl,
      normalizedModularJCoordinate_modularDeck, hEq1]
  have htauOne : tau fuchsianOneFixedPoint = ellipticThreeParameter := by
    change rhoTauReal e • tau1 fuchsianOneFixedPoint = ellipticThreeParameter
    rw [htau1One]
    exact heOne
  have htauTwo : tau fuchsianTwoFixedPoint = UpperHalfPlane.I := by
    exact heTwo
  exact ⟨tau, htau, hEq, htauOne, htauTwo⟩

/-- Kernel-checked elimination of the normalized Fuchsian modular-J lifting axiom. -/
theorem normalizedFuchsianModularJLiftingExistence :
    SphereSixComplex.Periods.NormalizedFuchsianModularJLiftingExistence := by
  intro J C
  obtain ⟨tau, htau, hEq, honeValue, htwoValue⟩ :=
    exists_global_lift_with_canonical_elliptic_values J C
  have hone := orderThree_generator_germ_of_center_value
    J C tau htau hEq honeValue
  have htwo := orderFourTwo_generator_germ_of_center_value
    J C tau htau hEq htwoValue
  have hJ : ∀ z, normalizedJ (tau z) = 1728 * C.coordinate z := by
    intro z
    have h := hEq z
    rw [normalizedModularJCoordinate] at h
    linear_combination 1728 * h
  exact nonempty_normalizedLift_of_local_generator_germs C tau htau hJ
    fuchsianOneFixedPoint fuchsianTwoFixedPoint hone htwo


end SphereSixComplex.Periods.NormalizedModularJLiftingExistence
