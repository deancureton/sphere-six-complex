module

public import SphereSixComplex.Paper.Geometry.GlobalDeckQuotient
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianProperActionCore
import all SphereSixComplex.Paper.Geometry.GlobalDeckQuotient
import all SphereSixComplex.Paper.Geometry.GlobalTorusFamily
import all SphereSixComplex.Prerequisites.TriangleGroup.FreeProductTorsion

/-!
# Proper discontinuity and freeness on the regular Fuchsian locus

For a properly discontinuous group action, Mathlib's compact-set criterion makes every point
stabilizer finite.  Consequently every element fixing a point has finite order.  Combining this
with the triangle-group torsion classification proves that the explicit Fuchsian action is free
after removing its two elliptic orbits.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianProperFreeness

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup


/-- A triangle uniformization's source action restricted to the regular base used by the global
torus family. -/
@[expose, instance_reducible] public noncomputable def regularSourceMulAction
    (U : TriangleUniformization) : MulAction Delta (RegularBase (U := U)) where
  smul g z := regularSourceEquiv g z
  one_smul z := by
    apply Subtype.ext
    change U.sourceAction 1 • z.1 = z.1
    simp
  mul_smul g h z := by
    apply Subtype.ext
    change U.sourceAction (g * h) • z.1 = U.sourceAction g • (U.sourceAction h • z.1)
    rw [map_mul, mul_smul]


/-- The project's compact-set source hypothesis supplies Mathlib's standard class for the
explicit Fuchsian action whenever the two source representations agree. -/
public theorem fuchsianProperlyDiscontinuous_of_source
    {U : TriangleUniformization} (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := fuchsianSourceMulAction
    ProperlyDiscontinuousSMul Delta UpperHalfPlane := by
  let _ := fuchsianSourceMulAction
  constructor
  intro K L hK hL
  change Set.Finite {g : Delta |
    (((fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) '' K) ∩ L).Nonempty}
  simpa only [← hsource] using hproper hK hL

/-- Proper discontinuity makes the existing global-family regular source action free when its
source representation is the explicit Fuchsian one. -/
public theorem regularSource_isCancelSMul_of_fuchsian
    {U : TriangleUniformization} (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularSourceMulAction U
    IsCancelSMul Delta (RegularBase (U := U)) := by
  let _ := regularSourceMulAction U
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g z hfixed
  have hzOne : U.zOne = fuchsianOneFixedPoint := by
    apply (FreeProductTorsion.fuchsianSourceAction_gOne_fixed_iff U.zOne).mp
    simpa only [← hsource] using U.zOne_fixed
  have hzTwo : U.zTwo = fuchsianTwoFixedPoint := by
    apply (FreeProductTorsion.fuchsianSourceAction_gTwo_fixed_iff U.zTwo).mp
    simpa only [← hsource] using U.zTwo_fixed
  have hz : FreeProductTorsion.IsFuchsianRegularPoint z.1 := by
    simpa only [FreeProductTorsion.IsFuchsianRegularPoint, IsRegularBasePoint, hsource,
      hzOne, hzTwo] using z.2
  apply fuchsian_fixed_regular_eq_one
    (fuchsianProperlyDiscontinuous_of_source hsource hproper) hz
  have hfixedVal := congrArg Subtype.val hfixed
  change U.sourceAction g • z.1 = z.1 at hfixedVal
  simpa only [hsource] using hfixedVal




end SphereSixComplex.TriangleGroup.FuchsianProperFreeness
