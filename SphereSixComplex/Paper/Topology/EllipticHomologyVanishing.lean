module

public import SphereSixComplex.Paper.Topology.EllipticHomologyGenerators
public import SphereSixComplex.Paper.Topology.EllipticDegreeTwoRelations
public import SphereSixComplex.Paper.Topology.EllipticProjectedFourthSweeps
public import SphereSixComplex.Paper.Topology.StarFourthTranslationGenerators

@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData
open EllipticFilling EllipticReducedFiberMappingTorus
open Topology.EllipticSpecializedNormalizedCoverSweep Topology.FiniteCoverPerfectPairing
open EllipticHomologyGeneratorAlignment

public theorem ellipticInterior_homologyTwo_eq_zero_of_fixedSweeps
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (hThree : integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        ((integralSingularHomologyEquiv 2
          (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          (-orderThreeFixedLoopSweep), 0)) = 0)
    (hFour : integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        (0, (integralSingularHomologyEquiv 2
          (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          orderFourFixedLoopSweep)) = 0) :
    integralSingularHomologyMap 2 A.ellipticInteriorInclusion = 0 := by
  let g := integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
  let p := g.comp (reducedFibersToUnion R.twoDiscCover 2)
  let f₃ := p.comp (AddMonoidHom.inl _ _)
  let f₄ := p.comp (AddMonoidHom.inr _ _)
  have hCommon (i) : f₃ (orderThreeProjectedDegreeTwoGenerator A.periods i) =
      f₄ (orderFourProjectedDegreeTwoGenerator A.periods i) :=
    congrArg g (projected_generators_eq R.twoDiscCover R.homologyAlignment.degreeTwo i)
  have hRelation := Topology.EllipticDegreeTwoRelations.orderThree_map_zero_eq_two_smul_one
    A.periods f₃ (EllipticProjectedFourthSweeps.projected_toStar_eq_zero 4 R rfl)
      (EllipticProjectedFourthSweeps.projected_toStar_eq_zero 5 R rfl)
  obtain ⟨h₃, h₄⟩ := Topology.EllipticHomologyGenerators.homologyTwo_maps_eq_zero
    A.periods f₃ f₄ hThree hFour (hCommon 0) (hCommon 3) hRelation
  apply ellipticInterior_homologyTwo_eq_zero_of_sides R
  intro x
  let y := R.twoDiscCover.sideHomologyEquiv 2 x
  have hz : p y = 0 := by
    calc
      _ = f₃ y.1 + f₄ y.2 := by
        change p y = p (y.1, 0) + p (0, y.2)
        rw [← map_add]
        congr 1
        exact Prod.ext (add_zero _).symm (zero_add _).symm
      _ = 0 := by simp only [h₃, h₄, AddMonoidHom.zero_apply, add_zero]
  change g ((IntegralMayerVietoris.sumMap _ _ 2)
    ((R.twoDiscCover.sideHomologyEquiv 2).symm
      ((R.twoDiscCover.sideHomologyEquiv 2) x))) = 0 at hz
  rw [AddEquiv.symm_apply_apply] at hz
  exact hz

public theorem ellipticInterior_homologyTwo_eq_zero
    {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    integralSingularHomologyMap 2 A.ellipticInteriorInclusion = 0 :=
  ellipticInterior_homologyTwo_eq_zero_of_fixedSweeps R
    (orderThree_fixedLoopSweep_toStar_eq_zero R)
    (orderFour_fixedLoopSweep_toStar_eq_zero R)

end SphereSixComplex.Geometry.AnalyticData
