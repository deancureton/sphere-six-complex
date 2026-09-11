module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarCircleReflection
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarCircleReflection
public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarFundamentalFibers
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarFundamentalFibers
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarSeedInjective
public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarRightReflectionInjective
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarRightReflectionInjective
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTriangleGeometry
import all SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTriangleGeometry
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
import all TauCeti.Analysis.Complex.Conformal.Continuation.Basic

@[expose] public section

/-!
# Local Schwarz-continuation cover of the doubled fundamental region

The three explicit scalar Schwarz extensions cover the closed source reflection triangle away
from its two finite vertices.  Reflecting the left and circular doubles across the right seam
covers the adjacent triangle.  Thus only the three finite vertices of the doubled oriented
fundamental region require finite corner atlases.

The final section packages compatible translated local patches into a genuine
`TauCeti.ContinuesInside` witness on the upper half-plane.
-/

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Periods.Reflection

/-- The left-side double transported to the outer vertical side of the right chamber. -/
def sourceFarRightDouble : Set ℂ := sourceRight ⁻¹' sourceLeftDouble

/-- The circular double transported to the circular side of the right chamber. -/
def sourceRightCircleDouble : Set ℂ := sourceRight ⁻¹' sourceCircleDouble



/-- The third finite vertex in the doubled orientation-preserving region. -/
def sourceFarRightVertex : UpperHalfPlane := sourceRightUHP fuchsianTwoFixedPoint

private theorem sourceLeft_fixed_of_re_eq_of_normSq_eq_one (z : UpperHalfPlane)
    (hre : z.re = -Real.sqrt 2 / 2) (hn : normSq (z : ℂ) = 1) :
    z = fuchsianTwoFixedPoint := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simpa [fuchsianTwoFixedPoint] using hre
  · change z.im = Real.sqrt 2 / 2
    change (z : ℂ).re = -Real.sqrt 2 / 2 at hre
    change (z : ℂ).im = Real.sqrt 2 / 2
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [normSq_apply, hre] at hn
    apply (sq_eq_sq₀ (show 0 ≤ (z : ℂ).im from z.im_pos.le)
      (div_nonneg hs (by norm_num))).mp
    nlinarith

private theorem sourceRight_fixed_of_re_eq_of_normSq_eq_one (z : UpperHalfPlane)
    (hre : z.re = 1 / 2) (hn : normSq (z : ℂ) = 1) :
    z = fuchsianOneFixedPoint := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simpa [fuchsianOneFixedPoint] using hre
  · change z.im = Real.sqrt 3 / 2
    change (z : ℂ).re = 1 / 2 at hre
    change (z : ℂ).im = Real.sqrt 3 / 2
    have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [normSq_apply, hre] at hn
    apply (sq_eq_sq₀ (show 0 ≤ (z : ℂ).im from z.im_pos.le)
      (div_nonneg hs (by norm_num))).mp
    nlinarith

private theorem mem_sourceLeftDouble_of_leftSide {z : ℂ}
    (hre : z.re = -Real.sqrt 2 / 2) (hi : 0 < z.im) (hn : 1 < normSq z) :
    z ∈ sourceLeftDouble := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have href : sourceLeft z = z := by
    apply Complex.ext <;> simp [sourceLeft, hre] <;> ring
  exact ⟨by linarith, by linarith, hi, hn, by simpa [href] using hn⟩

private theorem mem_sourceRightDouble_of_rightSide {z : ℂ}
    (hre : z.re = 1 / 2) (hi : 0 < z.im) (hn : 1 < normSq z) :
    z ∈ sourceRightDouble := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have href : sourceRight z = z := by
    apply Complex.ext <;> simp [sourceRight, hre] <;> norm_num
  exact ⟨by linarith, by linarith, hi, hn, by simpa [href] using hn⟩

/-- The three explicit Schwarz doubles cover the closed source triangle except at its two finite
elliptic vertices. -/
theorem fundamentalTriangle_mem_scalar_local_cover (z : UpperHalfPlane)
    (hz : z ∈ fundamentalTriangle) :
    (z : ℂ) ∈ sourceRightDouble ∨
      (z : ℂ) ∈ sourceLeftDouble ∨
      (z : ℂ) ∈ sourceCircleDouble ∨
      z = fuchsianOneFixedPoint ∨ z = fuchsianTwoFixedPoint := by
  rcases hz with ⟨hl, hr, hn⟩
  rcases hn.lt_or_eq with hnlt | hneq
  · by_cases hleft : z.re = -Real.sqrt 2 / 2
    · exact Or.inr (Or.inl
        (mem_sourceLeftDouble_of_leftSide hleft z.im_pos hnlt))
    · have hl' : -Real.sqrt 2 / 2 < z.re := lt_of_le_of_ne hl (Ne.symm hleft)
      by_cases hright : z.re = 1 / 2
      · exact Or.inl (mem_sourceRightDouble_of_rightSide hright z.im_pos hnlt)
      · have hr' : z.re < 1 / 2 := lt_of_le_of_ne hr hright
        exact Or.inl (sourceOpenChamber_subset_sourceRightDouble
          ⟨hl', hr', z.im_pos, hnlt⟩)
  · have hn' : normSq (z : ℂ) = 1 := hneq.symm
    by_cases hleft : z.re = -Real.sqrt 2 / 2
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (sourceLeft_fixed_of_re_eq_of_normSq_eq_one z hleft hn'))))
    · have hl' : -Real.sqrt 2 / 2 < z.re := lt_of_le_of_ne hl (Ne.symm hleft)
      by_cases hright : z.re = 1 / 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (sourceRight_fixed_of_re_eq_of_normSq_eq_one z hright hn'))))
      · have hr' : z.re < 1 / 2 := lt_of_le_of_ne hr hright
        exact Or.inr (Or.inr (Or.inl ⟨z.im_pos, hl', hr', by
          simpa [hn'] using hl', by simpa [hn'] using hr'⟩))

private theorem sourceRightUHP_mem_fundamentalTriangle_of_mem_right
    {z : UpperHalfPlane} (hz : z ∈ rightFundamentalTriangle) :
    sourceRightUHP z ∈ fundamentalTriangle := by
  rcases hz with ⟨hl, hr, hn⟩
  change 1 / 2 ≤ (z : ℂ).re at hl
  change (z : ℂ).re ≤ 1 + Real.sqrt 2 / 2 at hr
  refine ⟨?_, ?_, ?_⟩
  · change -Real.sqrt 2 / 2 ≤ (sourceRight (z : ℂ)).re
    rw [sourceRight_re]
    linarith
  · change (sourceRight (z : ℂ)).re ≤ 1 / 2
    rw [sourceRight_re]
    linarith
  · change 1 ≤ normSq (sourceRight (z : ℂ))
    have heq : normSq (sourceRight (z : ℂ)) = normSq (1 - (z : ℂ)) := by
      simp [sourceRight, normSq_apply]
    rwa [heq]

private theorem sourceRightUHP_involutive (z : UpperHalfPlane) :
    sourceRightUHP (sourceRightUHP z) = z := by
  apply UpperHalfPlane.coe_injective
  exact sourceRight_involutive (z : ℂ)

/-- The five regular side doubles cover the doubled oriented fundamental region except at its
three finite vertices. -/
theorem orientedFundamentalRegion_mem_scalar_local_cover (z : UpperHalfPlane)
    (hz : z ∈ orientedFundamentalRegion) :
    (z : ℂ) ∈ sourceRightDouble ∨
      (z : ℂ) ∈ sourceLeftDouble ∨
      (z : ℂ) ∈ sourceCircleDouble ∨
      (z : ℂ) ∈ sourceFarRightDouble ∨
      (z : ℂ) ∈ sourceRightCircleDouble ∨
      z = fuchsianOneFixedPoint ∨ z = fuchsianTwoFixedPoint ∨
      z = sourceFarRightVertex := by
  rcases hz with hz | hz
  · rcases fundamentalTriangle_mem_scalar_local_cover z hz with
        hright | hleft | hcircle | hone | htwo
    · exact Or.inl hright
    · exact Or.inr (Or.inl hleft)
    · exact Or.inr (Or.inr (Or.inl hcircle))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hone)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htwo))))))
  · let w : UpperHalfPlane := sourceRightUHP z
    have hw := fundamentalTriangle_mem_scalar_local_cover w
      (sourceRightUHP_mem_fundamentalTriangle_of_mem_right hz)
    rcases hw with hright | hleft | hcircle | hone | htwo
    · left
      have := sourceRightDouble_mapsTo hright
      simpa [w, sourceRight_involutive] using this
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [sourceFarRightDouble, w] using hleft))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [sourceRightCircleDouble, w] using hcircle)))))
    · have hzEq : z = fuchsianOneFixedPoint := by
        calc
          z = sourceRightUHP w := (sourceRightUHP_involutive z).symm
          _ = sourceRightUHP fuchsianOneFixedPoint := congrArg sourceRightUHP hone
          _ = fuchsianOneFixedPoint := by
            apply UpperHalfPlane.coe_injective
            apply Complex.ext <;>
              norm_num [sourceRightUHP, sourceRight, fuchsianOneFixedPoint]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hzEq)))))
    · have hzEq : z = sourceFarRightVertex := by
        calc
          z = sourceRightUHP w := (sourceRightUHP_involutive z).symm
          _ = sourceRightUHP fuchsianTwoFixedPoint := congrArg sourceRightUHP htwo
          _ = sourceFarRightVertex := rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hzEq))))))

/-! ## Concrete regular patches -/














/-! ## Finite corner atlases -/


/-! ## Global translated-patch interface -/




end SphereSixComplex.Periods.SourceChamberTopology
