module

public import SphereSixComplex.Periods.Uniformization.ChartedReflectionInjective
import all SphereSixComplex.Periods.Uniformization.ChartedReflectionInjective
public import SphereSixComplex.Periods.Uniformization.TriangleReflections
import all SphereSixComplex.Periods.Uniformization.TriangleReflections
public import SphereSixComplex.Geometry.EllipticLocalCoordinates
import all SphereSixComplex.Geometry.EllipticLocalCoordinates

@[expose] public section

/-!
# Finite reflection around an analytic corner

This file separates the two genuinely different parts of reflection around a rational-angle
corner.

* `gluedReflectionPatches` glues finitely (in fact, arbitrarily) many compatible holomorphic
  reflected patches.  If their union is a neighbourhood of the vertex, the glued map is analytic
  at the vertex.
* `cornerRotationForcesLeadingPower` turns the rotation identity obtained by composing the two
  side reflections into an exact equation for the leading power of the analytic germ.

The second statement exposes one necessary geometric input: an upper bound on the local degree.
Rotation equivariance alone determines the degree only modulo the source rotation order.  In a
true conformal wedge map the bound follows from one-to-one correspondence of a fundamental source
wedge with the target wedge.  Keeping that bound explicit prevents an invalid use at a branched
corner.
-/

open Complex Filter Set Topology

noncomputable section

namespace SphereSixComplex.Periods.Reflection

open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.TriangleReflections

variable {ι : Type*}

/-! The side-reflection identities produce the required holomorphic generator identities. -/

/-- Intertwining the right and circular reflections implies equivariance for the common
order-three generator. -/
theorem equivariantOne_of_side_reflections (τ : UpperHalfPlane → UpperHalfPlane)
    (hright : ∀ z, τ (sourceRightUHP z) = targetRightUHP (τ z))
    (hcircle : ∀ z, τ (sourceCircleUHP z) = targetCircleUHP (τ z))
    (z : UpperHalfPlane) :
    τ (fuchsianSourceAction g₁ • z) = rhoTauReal g₁ • τ z := by
  rw [← sourceRight_sourceCircle, hright, hcircle, targetRight_targetCircle]

/-- Intertwining the circular and left reflections implies equivariance for the source
order-four / target order-two generator. -/
theorem equivariantTwo_of_side_reflections (τ : UpperHalfPlane → UpperHalfPlane)
    (hcircle : ∀ z, τ (sourceCircleUHP z) = targetCircleUHP (τ z))
    (hleft : ∀ z, τ (sourceLeftUHP z) = targetLeftUHP (τ z))
    (z : UpperHalfPlane) :
    τ (fuchsianSourceAction g₂ • z) = rhoTauReal g₂ • τ z := by
  rw [← sourceCircle_sourceLeft, hcircle, hleft, targetCircle_targetLeft]

/-- Glue compatible local reflected branches by choosing any branch whose domain contains the
point.  Compatibility makes the choice irrelevant on the union of the domains. -/
def gluedReflectionPatches (U : ι → Set ℂ) (F : ι → ℂ → ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact if hz : ∃ i, z ∈ U i then F (Classical.choose hz) z else 0

theorem gluedReflectionPatches_eq (U : ι → Set ℂ) (F : ι → ℂ → ℂ)
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j))
    (i : ι) {z : ℂ} (hz : z ∈ U i) :
    gluedReflectionPatches U F z = F i z := by
  classical
  unfold gluedReflectionPatches
  split
  · rename_i hex
    exact hcompat (Classical.choose hex) i ⟨Classical.choose_spec hex, hz⟩
  · rename_i hnone
    exact (hnone ⟨i, hz⟩).elim

/-- The glued function extends any distinguished original branch. -/
theorem eqOn_gluedReflectionPatches_of_eqOn (U : ι → Set ℂ) (F : ι → ℂ → ℂ)
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j))
    (i : ι) {A : Set ℂ} {f : ℂ → ℂ} (hA : A ⊆ U i) (hFi : EqOn (F i) f A) :
    EqOn (gluedReflectionPatches U F) f A := by
  intro z hz
  exact (gluedReflectionPatches_eq U F hcompat i (hA hz)).trans (hFi hz)

/-- Compatible holomorphic reflection patches glue to a holomorphic map on their union. -/
theorem differentiableOn_gluedReflectionPatches
    (U : ι → Set ℂ) (F : ι → ℂ → ℂ)
    (hU : ∀ i, IsOpen (U i))
    (hF : ∀ i, DifferentiableOn ℂ (F i) (U i))
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)) :
    DifferentiableOn ℂ (gluedReflectionPatches U F) (⋃ i, U i) := by
  apply DifferentiableOn.iUnion_of_isOpen _ hU
  intro i
  exact (hF i).congr fun z hz => gluedReflectionPatches_eq U F hcompat i hz

/-- If compatible reflected patches cover a neighbourhood of the corner, their glued map is
analytic at that corner. -/
theorem analyticAt_gluedReflectionPatches
    (U : ι → Set ℂ) (F : ι → ℂ → ℂ)
    (hU : ∀ i, IsOpen (U i))
    (hF : ∀ i, DifferentiableOn ℂ (F i) (U i))
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j))
    {v : ℂ} (hcover : (⋃ i, U i) ∈ 𝓝 v) :
    AnalyticAt ℂ (gluedReflectionPatches U F) v :=
  (differentiableOn_gluedReflectionPatches U F hU hF hcompat).analyticAt hcover

/-- A cyclic family of reflection patches gives the expected rotation identity for the glued
germ.  In a wedge, `next` advances one sector, while `λ` and `μ` are the source and target
rotations obtained by composing the two side reflections. -/
theorem eventuallyEq_gluedReflectionPatches_rotation
    (U : ι → Set ℂ) (F : ι → ℂ → ℂ)
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j))
    (next : ι → ι) (sourceRot targetRot : ℂ)
    (hrotate_mem : ∀ i z, z ∈ U i → sourceRot * z ∈ U (next i))
    (hrotate : ∀ i z, z ∈ U i →
      F (next i) (sourceRot * z) = targetRot * F i z)
    (hcover : (⋃ i, U i) ∈ 𝓝 (0 : ℂ)) :
    (fun z => gluedReflectionPatches U F (sourceRot * z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => targetRot * gluedReflectionPatches U F z) := by
  filter_upwards [hcover] with z hz
  simp only [mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  calc
    gluedReflectionPatches U F (sourceRot * z) = F (next i) (sourceRot * z) :=
      gluedReflectionPatches_eq U F hcompat (next i) (hrotate_mem i z hi)
    _ = targetRot * F i z := hrotate i z hi
    _ = targetRot * gluedReflectionPatches U F z := by
      rw [gluedReflectionPatches_eq U F hcompat i hi]

/-- Rotation equivariance determines the leading power of a finite analytic germ.

If `G(λz) = μG(z)` near the corner, then the first nonzero Taylor term has exponent `k` satisfying
`λ^k = μ`.  This is the algebraic core of the rational-angle corner calculation. -/
theorem cornerRotationForcesLeadingPower {G : ℂ → ℂ} {sourceRot targetRot : ℂ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (_hsourceRot : sourceRot ≠ 0)
    (hrotate : (fun z => G (sourceRot * z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => targetRot * G z)) :
    sourceRot ^ analyticOrderNatAt G 0 = targetRot := by
  let k := analyticOrderNatAt G 0
  obtain ⟨g, hg, hg0, hfactor⟩ := hG.analyticOrderAt_ne_top.mp hfinite
  have hsourceRot_cont : ContinuousAt (fun z : ℂ => sourceRot * z) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℂ => sourceRot) 0).mul continuousAt_id
  have hsourceRot_tend : Tendsto (fun z : ℂ => sourceRot * z) (𝓝 0) (𝓝 0) := by
    change Tendsto (fun z : ℂ => sourceRot * z) (𝓝 0) (𝓝 (sourceRot * 0)) at hsourceRot_cont
    simpa only [mul_zero] using hsourceRot_cont
  have hgcomp : ContinuousAt (fun z : ℂ => g (sourceRot * z)) 0 := by
    change ContinuousAt (g ∘ fun z : ℂ => sourceRot * z) 0
    exact hg.continuousAt.comp_of_eq hsourceRot_cont (mul_zero sourceRot)
  have hfactorRot := hfactor.comp_tendsto hsourceRot_tend
  have hcancel : (fun z : ℂ => sourceRot ^ k * g (sourceRot * z)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => targetRot * g z) := by
    filter_upwards [hrotate.filter_mono nhdsWithin_le_nhds,
      hfactorRot.filter_mono nhdsWithin_le_nhds,
      hfactor.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hrot hzfac hfac hz
    have hz0 : z ≠ 0 := by simpa using hz
    have heq : (sourceRot * z) ^ k * g (sourceRot * z) =
        targetRot * (z ^ k * g z) := by
      calc
        (sourceRot * z) ^ k * g (sourceRot * z) = G (sourceRot * z) := by
          simpa only [Function.comp_apply, k, sub_zero, smul_eq_mul] using hzfac.symm
        _ = targetRot * G z := hrot
        _ = targetRot * (z ^ k * g z) := by
          rw [hfac]
          simp only [k, sub_zero, smul_eq_mul]
    have hcommon : z ^ k * (sourceRot ^ k * g (sourceRot * z)) =
        z ^ k * (targetRot * g z) := by
      rw [mul_pow] at heq
      calc
        z ^ k * (sourceRot ^ k * g (sourceRot * z)) =
            sourceRot ^ k * z ^ k * g (sourceRot * z) := by ring
        _ = targetRot * (z ^ k * g z) := heq
        _ = z ^ k * (targetRot * g z) := by ring
    exact mul_left_cancel₀ (pow_ne_zero k hz0) hcommon
  have hleft_cont : ContinuousAt (fun z : ℂ => sourceRot ^ k * g (sourceRot * z)) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℂ => sourceRot ^ k) 0).mul hgcomp
  have hleft : Tendsto (fun z : ℂ => sourceRot ^ k * g (sourceRot * z)) (𝓝[≠] 0)
      (𝓝 (sourceRot ^ k * g 0)) := by
    change Tendsto (fun z : ℂ => sourceRot ^ k * g (sourceRot * z)) (𝓝 0)
      (𝓝 (sourceRot ^ k * g (sourceRot * 0))) at hleft_cont
    simpa only [mul_zero] using hleft_cont.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun z : ℂ => targetRot * g z) (𝓝[≠] 0)
      (𝓝 (targetRot * g 0)) :=
    (((continuousAt_const : ContinuousAt (fun _ : ℂ => targetRot) 0).mul
      hg.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have hlead : sourceRot ^ k * g 0 = targetRot * g 0 :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hcancel
  exact mul_right_cancel₀ hg0 hlead

/-- Exact local degree once the fundamental-wedge geometry supplies the degree bound and the
finite rotation has a unique resonant exponent in that range. -/
theorem cornerLocalDegree_eq_of_unique_resonance {G : ℂ → ℂ}
    {sourceRot targetRot : ℂ} {m r : ℕ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (hzero : G 0 = 0) (hsourceRot : sourceRot ≠ 0)
    (hrotate : (fun z => G (sourceRot * z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => targetRot * G z))
    (hdegree_le : analyticOrderNatAt G 0 ≤ m)
    (hresonance : ∀ k : ℕ, 0 < k → k ≤ m → sourceRot ^ k = targetRot → k = r) :
    analyticOrderNatAt G 0 = r := by
  apply hresonance (analyticOrderNatAt G 0)
  · have hne : analyticOrderAt G 0 ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hG, hzero⟩
    have hcast : ((analyticOrderNatAt G 0 : ℕ) : ℕ∞) = analyticOrderAt G 0 :=
      Nat.cast_analyticOrderNatAt hfinite
    exact Nat.pos_of_ne_zero fun hk => hne (by simpa [hk] using hcast.symm)
  · exact hdegree_le
  · exact cornerRotationForcesLeadingPower hG hfinite hsourceRot hrotate

/-- Convert an exact analytic order into Tau Ceti's quantitative local-degree statement. -/
theorem exists_localDegree_eq {G : ℂ → ℂ} {r : ℕ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (hzero : G 0 = 0) (hdegree : analyticOrderNatAt G 0 = r) :
    ∃ ρ > 0, AnalyticOnNhd ℂ G (Metric.closedBall 0 ρ) ∧
      ∃ δ > 0, ∀ w : ℂ, ‖w - G 0‖ < δ →
        (∑ᶠ z ∈ Metric.ball 0 ρ, analyticOrderNatAt (fun ζ => G ζ - w) z) = r := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hG.analyticOrderAt_ne_top.mp hfinite
  have hisol : ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z ≠ G 0 := by
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
      with z hzfactor hgz hz0
    rw [hzero]
    rw [hzfactor]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hz0)) hgz
  obtain ⟨ρ, hρ, hanalytic, δ, hδ, hcount⟩ := TauCeti.exists_localDegree hG hisol
  refine ⟨ρ, hρ, hanalytic, δ, hδ, fun w hw => ?_⟩
  simpa only [hzero, sub_zero, hdegree] using hcount w hw

/-- A source wedge of angle `π/4` mapped to a target wedge of angle `π/2` has local degree two.

The source full-turn generator is multiplication by `-i`; the target order-two generator is
multiplication by `-1`.  The explicit degree bound `≤ 4` is the fundamental-wedge input. -/
theorem cornerLocalDegree_orderFour_to_orderTwo {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (hzero : G 0 = 0)
    (hrotate : (fun z => G (orderFourMultiplier * z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => -(G z)))
    (hdegree_le : analyticOrderNatAt G 0 ≤ 4) :
    analyticOrderNatAt G 0 = 2 := by
  apply cornerLocalDegree_eq_of_unique_resonance
    (sourceRot := orderFourMultiplier) (targetRot := (-1 : ℂ)) (m := 4) (r := 2)
    hG hfinite hzero
    (norm_pos_iff.mp (by rw [norm_orderFourMultiplier]; norm_num))
    (hrotate.trans (Filter.Eventually.of_forall fun z => (neg_one_mul (G z)).symm)) hdegree_le
  intro k hk hle hpow
  interval_cases k <;> norm_num [orderFourMultiplier, pow_succ] at hpow <;> norm_num
  all_goals
    have him := congrArg Complex.im hpow
    norm_num at him

/-- A scalar function on an order-three source wedge, real on both bounding arcs, has local degree
three after finite Schwarz reflection.  The target rotation is trivial because the target is a
half-plane for a scalar coordinate. -/
theorem scalarCornerLocalDegree_orderThree {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (hzero : G 0 = 0)
    (hrotate : (fun z => G (orderThreeMultiplier * z)) =ᶠ[𝓝 (0 : ℂ)] G)
    (hdegree_le : analyticOrderNatAt G 0 ≤ 3) :
    analyticOrderNatAt G 0 = 3 := by
  apply cornerLocalDegree_eq_of_unique_resonance
    (sourceRot := orderThreeMultiplier) (targetRot := (1 : ℂ)) (m := 3) (r := 3)
    hG hfinite hzero
    (norm_pos_iff.mp (by rw [norm_orderThreeMultiplier]; norm_num))
    (hrotate.trans (Filter.Eventually.of_forall fun z => (one_mul (G z)).symm)) hdegree_le
  intro k hk hle hpow
  interval_cases k
  · norm_num [orderThreeMultiplier] at hpow
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have him := congrArg Complex.im hpow
    norm_num [orderThreeMultiplier] at him
  · have him := congrArg Complex.im hpow
    norm_num [orderThreeMultiplier, Complex.mul_im, pow_two] at him
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · rfl

/-- A scalar function on an order-four source wedge, real on both bounding arcs, has local degree
four after finite Schwarz reflection. -/
theorem scalarCornerLocalDegree_orderFour {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hfinite : analyticOrderAt G 0 ≠ ⊤)
    (hzero : G 0 = 0)
    (hrotate : (fun z => G (orderFourMultiplier * z)) =ᶠ[𝓝 (0 : ℂ)] G)
    (hdegree_le : analyticOrderNatAt G 0 ≤ 4) :
    analyticOrderNatAt G 0 = 4 := by
  apply cornerLocalDegree_eq_of_unique_resonance
    (sourceRot := orderFourMultiplier) (targetRot := (1 : ℂ)) (m := 4) (r := 4)
    hG hfinite hzero
    (norm_pos_iff.mp (by rw [norm_orderFourMultiplier]; norm_num))
    (hrotate.trans (Filter.Eventually.of_forall fun z => (one_mul (G z)).symm)) hdegree_le
  intro k hk hle hpow
  interval_cases k <;> norm_num [orderFourMultiplier, pow_succ] at hpow <;> norm_num
  all_goals
    have him := congrArg Complex.im hpow
    norm_num at him


end SphereSixComplex.Periods.Reflection
