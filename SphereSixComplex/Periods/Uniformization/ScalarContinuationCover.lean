module

public import SphereSixComplex.Periods.Uniformization.ScalarCircleReflection
import all SphereSixComplex.Periods.Uniformization.ScalarCircleReflection
public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalFibres
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalFibres
public import SphereSixComplex.Periods.Uniformization.ScalarSeedInjective
import all SphereSixComplex.Periods.Uniformization.ScalarSeedInjective
public import SphereSixComplex.Periods.Uniformization.ScalarRightReflectionInjective
import all SphereSixComplex.Periods.Uniformization.ScalarRightReflectionInjective
public import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
import all SphereSixComplex.TriangleGroup.FuchsianTriangleCover
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

theorem sourceFarRightDouble_isOpen : IsOpen sourceFarRightDouble := by
  apply sourceLeftDouble_isOpen.preimage
  unfold sourceRight
  fun_prop

theorem sourceRightCircleDouble_isOpen : IsOpen sourceRightCircleDouble := by
  apply sourceCircleDouble_isOpen.preimage
  unfold sourceRight
  fun_prop

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

/-- Transport a scalar holomorphic patch across the right seam. -/
def rightReflectedScalarMap (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (F (sourceRight z))

theorem differentiableOn_rightReflectedScalarMap {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (rightReflectedScalarMap F) (sourceRight ⁻¹' U) := by
  intro z hz
  have hFat : DifferentiableAt ℂ F (sourceRight z) :=
    (hF _ hz).differentiableAt (hU.mem_nhds hz)
  let H : ℂ → ℂ := fun u => F (1 - u)
  have hHat : DifferentiableAt ℂ H ((starRingEnd ℂ) z) := by
    apply hFat.comp ((starRingEnd ℂ) z)
    · fun_prop
  have hc := hHat.conj_conj
  change DifferentiableWithinAt ℂ
    (fun y : ℂ => (starRingEnd ℂ) (F (1 - (starRingEnd ℂ) y)))
    (sourceRight ⁻¹' U) z
  simpa only [Function.comp_def, H, starRingEnd_self_apply] using
    hc.differentiableWithinAt

def sourceScalarFarRightDoubleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  rightReflectedScalarMap (sourceScalarLeftDoubleMap S)

def sourceScalarRightCircleDoubleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  rightReflectedScalarMap (sourceScalarCircleDoubleMap S)

theorem sourceScalarFarRightDoubleMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarFarRightDoubleMap S) sourceFarRightDouble := by
  exact differentiableOn_rightReflectedScalarMap sourceLeftDouble_isOpen
    (sourceScalarLeftDoubleMap_differentiableOn S)

theorem sourceScalarRightCircleDoubleMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarRightCircleDoubleMap S) sourceRightCircleDouble := by
  exact differentiableOn_rightReflectedScalarMap sourceCircleDouble_isOpen
    (sourceScalarCircleDoubleMap_differentiableOn S)

/-- The regular right-side continuation, packaged as Tau Ceti's biholomorphic local chart. -/
noncomputable def sourceScalarRightDoublePartialHomeomorph
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : OpenPartialHomeomorph ℂ ℂ :=
  TauCeti.DifferentiableOn.toOpenPartialHomeomorph
    (sourceScalarRightDoubleMap_differentiableOn S) sourceRightDouble_isOpen
    (sourceScalarRightDoubleMap_injOn S)

@[simp]
theorem sourceScalarRightDoublePartialHomeomorph_source
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    (sourceScalarRightDoublePartialHomeomorph S).source = sourceRightDouble := by
  simpa only [sourceScalarRightDoublePartialHomeomorph] using
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph_source
      (sourceScalarRightDoubleMap_differentiableOn S) sourceRightDouble_isOpen
      (sourceScalarRightDoubleMap_injOn S)

@[simp]
theorem sourceScalarRightDoublePartialHomeomorph_apply
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : ℂ) :
    sourceScalarRightDoublePartialHomeomorph S z = sourceScalarRightDoubleMap S z := by
  simpa only [sourceScalarRightDoublePartialHomeomorph] using
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph_apply
      (sourceScalarRightDoubleMap_differentiableOn S) sourceRightDouble_isOpen
      (sourceScalarRightDoubleMap_injOn S) z

theorem sourceScalarRightDoublePartialHomeomorph_conformalAt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) :
    ConformalAt (sourceScalarRightDoublePartialHomeomorph S) z := by
  simpa only [sourceScalarRightDoublePartialHomeomorph] using
    TauCeti.DifferentiableOn.conformalAt_toOpenPartialHomeomorph
      (sourceScalarRightDoubleMap_differentiableOn S) sourceRightDouble_isOpen
      (sourceScalarRightDoubleMap_injOn S) hz

/-- The union of the five explicit regular Schwarz patches. -/
def scalarRegularLocalCover : Set ℂ :=
  sourceRightDouble ∪ (sourceLeftDouble ∪ (sourceCircleDouble ∪
    (sourceFarRightDouble ∪ sourceRightCircleDouble)))

theorem scalarRegularLocalCover_isOpen : IsOpen scalarRegularLocalCover :=
  sourceRightDouble_isOpen.union (sourceLeftDouble_isOpen.union
    (sourceCircleDouble_isOpen.union
      (sourceFarRightDouble_isOpen.union sourceRightCircleDouble_isOpen)))

theorem orientedFundamentalRegion_mem_regular_or_vertex (z : UpperHalfPlane)
    (hz : z ∈ orientedFundamentalRegion) :
    (z : ℂ) ∈ scalarRegularLocalCover ∨
      z = fuchsianOneFixedPoint ∨ z = fuchsianTwoFixedPoint ∨
      z = sourceFarRightVertex := by
  rcases orientedFundamentalRegion_mem_scalar_local_cover z hz with
    hright | hleft | hcircle | hfarRight | hrightCircle | hone | htwo | hfarVertex
  · exact Or.inl (by simp only [scalarRegularLocalCover, mem_union]; exact Or.inl hright)
  · exact Or.inl (by simp only [scalarRegularLocalCover, mem_union]; exact Or.inr (Or.inl hleft))
  · exact Or.inl (by
      simp only [scalarRegularLocalCover, mem_union]
      exact Or.inr (Or.inr (Or.inl hcircle)))
  · exact Or.inl (by
      simp only [scalarRegularLocalCover, mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inl hfarRight))))
  · exact Or.inl (by
      simp only [scalarRegularLocalCover, mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr hrightCircle))))
  · exact Or.inr (Or.inl hone)
  · exact Or.inr (Or.inr (Or.inl htwo))
  · exact Or.inr (Or.inr (Or.inr hfarVertex))

/-! ## Finite corner atlases -/

/-- Compatible holomorphic sectors covering a neighbourhood of a finite corner. -/
structure ScalarCornerPatchData (n : ℕ) (v : ℂ) where
  U : Fin n → Set ℂ
  F : Fin n → ℂ → ℂ
  isOpen : ∀ i, IsOpen (U i)
  differentiableOn : ∀ i, DifferentiableOn ℂ (F i) (U i)
  compatible : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)
  cover : (⋃ i, U i) ∈ 𝓝 v

namespace ScalarCornerPatchData

variable {n : ℕ} {v : ℂ} (P : ScalarCornerPatchData n v)

def glued : ℂ → ℂ := gluedReflectionPatches P.U P.F

theorem analyticAt_glued : AnalyticAt ℂ P.glued v :=
  analyticAt_gluedReflectionPatches P.U P.F P.isOpen P.differentiableOn
    P.compatible P.cover

theorem center_mem_union : v ∈ ⋃ i, P.U i := mem_of_mem_nhds P.cover

end ScalarCornerPatchData

/-- Six reflected sectors meet at the order-three point; eight meet at each order-four point. -/
structure ScalarOrientedCornerAtlases where
  orderThree : ScalarCornerPatchData 6 (fuchsianOneFixedPoint : ℂ)
  orderFourLeft : ScalarCornerPatchData 8 (fuchsianTwoFixedPoint : ℂ)
  orderFourRight : ScalarCornerPatchData 8 (sourceFarRightVertex : ℂ)

namespace ScalarOrientedCornerAtlases

variable (A : ScalarOrientedCornerAtlases)

def carrier : Set ℂ :=
  scalarRegularLocalCover ∪ ((⋃ i, A.orderThree.U i) ∪
    ((⋃ i, A.orderFourLeft.U i) ∪ (⋃ i, A.orderFourRight.U i)))

theorem carrier_isOpen : IsOpen A.carrier := by
  exact scalarRegularLocalCover_isOpen.union
    ((isOpen_iUnion fun i => A.orderThree.isOpen i).union
      ((isOpen_iUnion fun i => A.orderFourLeft.isOpen i).union
        (isOpen_iUnion fun i => A.orderFourRight.isOpen i)))

/-- Once the finite reflection sectors are supplied, the resulting open set covers every actual
point of the closed doubled fundamental region (the ideal cusp is not a point of `ℍ`). -/
theorem orientedFundamentalRegion_subset_carrier :
    ∀ z : UpperHalfPlane, z ∈ orientedFundamentalRegion → (z : ℂ) ∈ A.carrier := by
  intro z hz
  rcases orientedFundamentalRegion_mem_regular_or_vertex z hz with hreg | hthree | hleft | hright
  · exact Or.inl hreg
  · subst z
    exact Or.inr (Or.inl A.orderThree.center_mem_union)
  · subst z
    exact Or.inr (Or.inr (Or.inl A.orderFourLeft.center_mem_union))
  · subst z
    exact Or.inr (Or.inr (Or.inr A.orderFourRight.center_mem_union))

theorem orderThree_analyticAt :
    AnalyticAt ℂ A.orderThree.glued (fuchsianOneFixedPoint : ℂ) :=
  A.orderThree.analyticAt_glued

theorem orderFourLeft_analyticAt :
    AnalyticAt ℂ A.orderFourLeft.glued (fuchsianTwoFixedPoint : ℂ) :=
  A.orderFourLeft.analyticAt_glued

theorem orderFourRight_analyticAt :
    AnalyticAt ℂ A.orderFourRight.glued (sourceFarRightVertex : ℂ) :=
  A.orderFourRight.analyticAt_glued

end ScalarOrientedCornerAtlases

/-! ## Global translated-patch interface -/

def sourceUpperHalfPlaneSet : Set ℂ := {z | 0 < z.im}

theorem sourceUpperHalfPlaneSet_isOpen : IsOpen sourceUpperHalfPlaneSet :=
  isOpen_lt continuous_const Complex.continuous_im

/-- The data left after translating the regular and finite-corner patches by the Fuchsian group:
open holomorphic patches, pairwise analytic-continuation compatibility, and coverage of `ℍ`. -/
structure ScalarTranslatedReflectionAtlas (I : Type*) where
  U : I → Set ℂ
  F : I → ℂ → ℂ
  isOpen : ∀ i, IsOpen (U i)
  differentiableOn : ∀ i, DifferentiableOn ℂ (F i) (U i)
  compatible : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)
  cover : (⋃ i, U i) = sourceUpperHalfPlaneSet

namespace ScalarTranslatedReflectionAtlas

variable {I : Type*} (A : ScalarTranslatedReflectionAtlas I)

def global : ℂ → ℂ := gluedReflectionPatches A.U A.F

theorem global_differentiableOn :
    DifferentiableOn ℂ A.global sourceUpperHalfPlaneSet := by
  rw [← A.cover]
  exact differentiableOn_gluedReflectionPatches A.U A.F A.isOpen A.differentiableOn
    A.compatible

/-- Compatible translated Schwarz patches give an actual Tau Ceti continuation throughout the
upper half-plane. -/
theorem global_continuesInside (z₀ : ℂ) :
    TauCeti.ContinuesInside A.global sourceUpperHalfPlaneSet z₀ :=
  TauCeti.ContinuesInside.of_differentiableOn sourceUpperHalfPlaneSet_isOpen
    A.global_differentiableOn

/-- If one translated patch represents the original chamber seed near the base point, the
original scalar germ itself continues throughout the upper half-plane. -/
theorem seed_continuesInside
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (base : I) (z₀ : ℂ)
    (hbase : A.U base ∈ 𝓝 z₀)
    (hseed : EqOn (A.F base) (sourceScalarTriangleMap S) (A.U base)) :
    TauCeti.ContinuesInside (sourceScalarTriangleMap S) sourceUpperHalfPlaneSet z₀ := by
  apply (A.global_continuesInside z₀).congr
  filter_upwards [hbase] with z hz
  exact (gluedReflectionPatches_eq A.U A.F A.compatible base hz).trans (hseed hz)

/-- Agreement of the continued branch with the explicit right double on the doubled fundamental
region makes the global scalar coordinate surjective.  The entire range calculation is supplied
by `sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion`. -/
theorem global_surjective_of_eqOn_orientedFundamentalRegion
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hfund : ∀ z : UpperHalfPlane, z ∈ orientedFundamentalRegion →
      A.global (z : ℂ) = sourceScalarRightDoubleMap S (z : ℂ)) :
    Function.Surjective (fun z : UpperHalfPlane => A.global (z : ℂ)) := by
  intro q
  obtain ⟨z, hz, hq⟩ :=
    sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion S q
  exact ⟨z, (hfund z hz).trans hq⟩

/-- Agreement on the doubled fundamental region also transports its exact fibre separation to the
continued global branch. -/
theorem global_fundamental_fibres_of_eqOn_orientedFundamentalRegion
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hfund : ∀ z : UpperHalfPlane, z ∈ orientedFundamentalRegion →
      A.global (z : ℂ) = sourceScalarRightDoubleMap S (z : ℂ))
    {z w : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hzw : A.global (z : ℂ) = A.global (w : ℂ)) :
    ∃ g : Delta, fuchsianSourceAction g • z = w := by
  apply sourceScalarRightDoubleMap_fundamental_fibres S hz hw
  rw [← hfund z hz, ← hfund w hw]
  exact hzw


end ScalarTranslatedReflectionAtlas

end SphereSixComplex.Periods.SourceChamberTopology
