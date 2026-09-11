module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Arc
public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
import TauCeti.Analysis.Complex.Conformal.Reflection.Arc
import all TauCeti.Analysis.Complex.Conformal.Reflection.Arc
import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
import all TauCeti.Analysis.Complex.Conformal.Reflection.Injective
public import SphereSixComplex.Prerequisites.Periods.Uniformization.TriangleReflections
import all SphereSixComplex.Prerequisites.Periods.Uniformization.TriangleReflections
public import SphereSixComplex.Prerequisites.Geometry.FuchsianEllipticCoordinates
import all SphereSixComplex.Prerequisites.Geometry.FuchsianEllipticCoordinates

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
