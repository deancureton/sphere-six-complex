module

public import SphereSixComplex.Paper.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Paper.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentation

/-!
# Mapping-torus adapters for the three paper collars

The analytic collar files already provide the actual cusp transport and the two actual affine
elliptic fibre generators.  What they do not yet provide is a global angular fundamental domain
whose two ends are identified by those maps.  This file isolates exactly that remaining
clutching-presentation input.

The general comparison with `CircleMappingTorus` is proved from quotient topology.  No homology
of a paper collar and no map in the paper's Mayer--Vietoris sequence is assumed here.
-/

@[expose] public section

noncomputable section

open Topology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry

open Matrix
open AnalyticTorusFamily ComplexTorus EllipticActualActionTopology EllipticFamilySpecialization
open EllipticFixedPointCriterion
open EllipticLogarithmicGaugeDescent EllipticPuncturedCollarGaugeHomeomorph
open EllipticVaryingFamilyQuotient
open EquivariantQuotientHomeomorph
open FamilyEquivariance GlobalTorusFamily
open SphereSixComplex.LatticeData SphereSixComplex.Periods SphereSixComplex.TriangleGroup

/-- A continuous permutation of order three is a self-homeomorphism. -/
public noncomputable def orderThreeHomeomorphOfContinuousPerm
    {X : Type} [TopologicalSpace X] (e : Equiv.Perm X) (he : Continuous e)
    (hp : e ^ 3 = 1) : X ≃ₜ X := by
  have hi : e.symm = e ^ 2 := by
    change e⁻¹ = e ^ 2
    calc
      e⁻¹ = e⁻¹ * 1 := by simp
      _ = e⁻¹ * e ^ 3 := by rw [hp]
      _ = e ^ 2 := by group
  refine { toEquiv := e, continuous_toFun := he, continuous_invFun := ?_ }
  change Continuous (e.symm : X → X)
  rw [hi]
  exact continuous_equiv_pow e he 2

/-- A continuous permutation of order four is a self-homeomorphism. -/
public noncomputable def orderFourHomeomorphOfContinuousPerm
    {X : Type} [TopologicalSpace X] (e : Equiv.Perm X) (he : Continuous e)
    (hp : e ^ 4 = 1) : X ≃ₜ X := by
  have hi : e.symm = e ^ 3 := by
    change e⁻¹ = e ^ 3
    calc
      e⁻¹ = e⁻¹ * 1 := by simp
      _ = e⁻¹ * e ^ 4 := by rw [hp]
      _ = e ^ 3 := by group
  refine { toEquiv := e, continuous_toFun := he, continuous_invFun := ?_ }
  change Continuous (e.symm : X → X)
  rw [hi]
  exact continuous_equiv_pow e he 3

/-- The actual translated order-three affine generator, now packaged as a homeomorphism. -/
public noncomputable def orderThreeAffineClutchingHomeomorph
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    AdditiveTorus (parameterMap F U.zOne).1 ≃ₜ
      AdditiveTorus (parameterMap F U.zOne).1 :=
  orderThreeHomeomorphOfContinuousPerm
    (orderThreeActionData F).fiberGenerator
    (orderThreeFiberGenerator_continuous F)
    (orderThreeActionData F).fiberGenerator_pow

/-- The actual translated order-four affine generator, now packaged as a homeomorphism. -/
public noncomputable def orderFourAffineClutchingHomeomorph
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    AdditiveTorus (parameterMap F U.zTwo).1 ≃ₜ
      AdditiveTorus (parameterMap F U.zTwo).1 :=
  orderFourHomeomorphOfContinuousPerm
    (orderFourActionData F).fiberGenerator
    (orderFourFiberGenerator_continuous F)
    (orderFourActionData F).fiberGenerator_pow

public theorem orderThreeAffineClutchingHomeomorph_apply
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (x : AdditiveTorus (parameterMap F U.zOne).1) :
    orderThreeAffineClutchingHomeomorph F x =
      (orderThreeDescendedAffineTorusAutomorphism F).map x := by
  change (orderThreeActionData F).fiberGenerator x =
    orderThreeFiberAutomorphism F x +
      orderThreeTranslation (parameterMap F U.zOne).1
  rfl

public theorem orderFourAffineClutchingHomeomorph_apply
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (x : AdditiveTorus (parameterMap F U.zTwo).1) :
    orderFourAffineClutchingHomeomorph F x =
      (orderFourDescendedAffineTorusAutomorphism F).map x := by
  change (orderFourActionData F).fiberGenerator x =
    orderFourFiberAutomorphism F x +
      orderFourTranslation (parameterMap F U.zTwo).1
  rfl




end Geometry

end SphereSixComplex
