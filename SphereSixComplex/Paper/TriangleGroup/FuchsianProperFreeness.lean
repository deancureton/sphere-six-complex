module

public import SphereSixComplex.Paper.Geometry.GlobalDeckQuotient
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianProperActionCore
public import Mathlib.Topology.Algebra.ConstMulAction
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

/-- The action attached to an arbitrary triangle-uniformization source. -/
@[expose, instance_reducible] public noncomputable def triangleSourceMulAction
    (U : TriangleUniformization) : MulAction Delta UpperHalfPlane where
  smul g z := (U.sourceAction g) z
  one_smul z := by
    change (U.sourceAction 1) z = z
    rw [map_one]
    rfl
  mul_smul g h z := by
    change (U.sourceAction (g * h)) z = (U.sourceAction g) ((U.sourceAction h) z)
    rw [map_mul]
    rfl

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
associated source action. -/
public theorem sourceActionProperlyDiscontinuous_to_instance
    {U : TriangleUniformization} (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := triangleSourceMulAction U
    ProperlyDiscontinuousSMul Delta UpperHalfPlane := by
  let _ := triangleSourceMulAction U
  constructor
  intro K L hK hL
  change Set.Finite {g : Delta |
    (((fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' K) ∩ L).Nonempty}
  exact hproper hK hL

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

/-- The regular lifted deck action on the vector-bundle cover used before taking lattice
quotients. -/
@[expose, instance_reducible] public noncomputable def regularLiftedDeckAction
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    MulAction Delta
      (RegularBase (U := U) × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace) where
  smul := regularDeckMap F
  one_smul := regularDeckMap_one F
  mul_smul := regularDeckMap_mul F

/-- The regular lifted deck action is free by projection to the regular source base. -/
public theorem regularLiftedDeckAction_isCancelSMul_of_fuchsian
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularLiftedDeckAction F
    IsCancelSMul Delta
      (RegularBase (U := U) × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace) := by
  let _ := regularLiftedDeckAction F
  let _ : MulAction Delta (RegularBase (U := U)) := regularSourceMulAction U
  let _ : IsCancelSMul Delta (RegularBase (U := U)) :=
    regularSource_isCancelSMul_of_fuchsian hsource hproper
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g p hfixed
  apply IsCancelSMul.eq_one_of_smul (P := RegularBase (U := U)) (x := p.1)
  exact congrArg Prod.fst hfixed

/-- The source compact-set criterion also lifts to the regular vector-bundle deck action. -/
public theorem regularLiftedDeckAction_properlyDiscontinuous_of_source
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularLiftedDeckAction F
    ProperlyDiscontinuousSMul Delta
      (RegularBase (U := U) × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace) := by
  let _ := regularLiftedDeckAction F
  constructor
  intro K L hK hL
  let baseProjection :
      RegularBase (U := U) × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace →
        UpperHalfPlane := fun p ↦ p.1.1
  have hcontinuous : Continuous baseProjection := continuous_subtype_val.comp continuous_fst
  have hKbase : IsCompact (baseProjection '' K) := hK.image hcontinuous
  have hLbase : IsCompact (baseProjection '' L) := hL.image hcontinuous
  apply (hproper hKbase hLbase).subset
  intro g hg
  rcases hg with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  refine ⟨q.1.1, ?_, ⟨q, hqL, rfl⟩⟩
  refine ⟨p.1.1, ⟨p, hpK, rfl⟩, ?_⟩
  change U.sourceAction g • p.1.1 = q.1.1
  exact congrArg (fun r ↦ r.1.1) hpq

end SphereSixComplex.TriangleGroup.FuchsianProperFreeness
