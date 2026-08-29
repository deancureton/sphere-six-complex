module

public import SphereSixComplex.Topology.EstablishedPaperSectionSevenAffineRegularLiftCompletion
public import SphereSixComplex.Topology.EstablishedPaperSectionSevenCuspCompletion
public import SphereSixComplex.Topology.EstablishedRecognition
public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsProof

/-!
# Comparator trusted-axiom imports

This module is the shared import boundary for the established declarations permitted by
Comparator. Its generated catalog below gives their exact signatures in one place for human
review. It contains no theorem statement or proof and does not import `Challenge` or `Solution`.
-/

/- BEGIN GENERATED AXIOM CATALOG
This block is generated from scripts/allowed-axioms.txt by Lean's pretty-printer.
It is the single human-review surface for every permitted constant and its exact type.
Do not edit it by hand; run ./scripts/update-axiom-catalog.sh --write.

# Constants the final theorem is allowed to depend on.
#
# Checked by ./scripts/check-axioms.sh. Project axioms are isolated established results with
# precise geometric, analytic, or classical-topological statements; their source docstrings
# record the corresponding trust boundary.
#
# Intended retained project trust kernel (7 constants):
# establishedHomologyToHomotopySixSphere, establishedSmoothPoincareSixStandardModel,
# establishedCompactSmoothOrientedManifoldHomologyTheory, integralCWCellularChainModel,
# isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup,
# FiniteCoverModelSix.establishedEulerMultiplicativity, and
# establishedOrbifoldAffineLineTorsorCuspBoundedSection.
# Every other project constant below is a temporary proof obligation to eliminate.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Classical recognition of the standard smooth six-sphere.
axiom SphereSixComplex.establishedHomologyToHomotopySixSphere : ∀ {X : Type} [inst : TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [inst_3 : ChartedSpace SphereSixComplex.RealModel X],
  SphereSixComplex.HomologyToHomotopySixSphereObligation X
axiom SphereSixComplex.establishedSmoothPoincareSixStandardModel : SphereSixComplex.SmoothPoincareSixStandardModel

# Established general topology and homology.
axiom SphereSixComplex.establishedCompactSmoothOrientedManifoldHomologyTheory : (d : ℕ) →
  (E X : Type) →
    [inst : NormedAddCommGroup E] →
      [inst_1 : NormedSpace ℝ E] →
        [FiniteDimensional ℝ E] →
          [inst_3 : TopologicalSpace X] →
            [inst_4 : ChartedSpace E X] →
              [T2Space X] →
                [SecondCountableTopology X] →
                  IsManifold (modelWithCornersSelf ℝ E) 1 X →
                    SphereSixComplex.SmoothAtlasOrientation d E X →
                      CompactSpace X → SphereSixComplex.IntegralPoincareUCTData d X
axiom SphereSixComplex.EstablishedCellularHomology.integralCWCellularChainModel : (Y : Type) →
  [inst : TopologicalSpace Y] →
    [T2Space Y] → [inst_2 : Topology.CWComplex Set.univ] → SphereSixComplex.IntegralCWCellularChainModel Y
axiom SphereSixComplex.EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup.{u_1} : ∀
  {B : Type u_1} [inst : TopologicalSpace B] (D : Set B) (b : B) (hb : b ∈ D),
  TauCeti.IsAspherical B b →
    TauCeti.IsAspherical ↑D ⟨b, hb⟩ →
      Function.Bijective
          ⇑(FundamentalGroup.mapOfEq (SphereSixComplex.topologicalSubsetInclusionMap D)
              (have this := rfl;
              this)) →
        ∀ (hCW : Topology.RelCWComplex Set.univ D), SphereSixComplex.IsHomotopyEquivalenceInclusion D
axiom SphereSixComplex.StandardTorusHomology.standardFourTorusNaturalRecalibration_nonempty : Nonempty
  SphereSixComplex.StandardTorusHomology.StandardFourTorusNaturalRecalibration
axiom SphereSixComplex.FiniteCoverModelSix.establishedEulerMultiplicativity : ∀ {X : Type} [inst : TopologicalSpace X]
  (M : SphereSixComplex.FiniteCoverModelSix X),
  let x := M.coverTopology;
  SphereSixComplex.integralHomologyEulerCharacteristicSix M.Cover =
    ↑M.degree * SphereSixComplex.integralHomologyEulerCharacteristicSix X
axiom SphereSixComplex.Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection : ∀
  (P : SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem),
  P.HasAcyclicProjectiveLineFrame → Nonempty P.CuspBoundedEllipticOneCorrection
axiom SphereSixComplex.Topology.FiniteCoverPerfectPairing.establishedEllipticDegreeTwoDualPullbackFiniteData : ∀
  {U : SphereSixComplex.Periods.TriangleUniformization} (F : SphereSixComplex.Periods.PeriodFunctions U),
  Nonempty (SphereSixComplex.Topology.FiniteCoverPerfectPairing.EllipticDegreeTwoDualPullbackFiniteData F)
axiom SphereSixComplex.Topology.AffineFiniteCyclicTorusCW.orderThreeFourAffineGeneratorFiniteCWModels : SphereSixComplex.Topology.AffineFiniteCyclicTorusCW.OrderThreeFourAffineGeneratorFiniteCWModels
axiom SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.establishedAffineCyclicHOnePresentationLift_bijective : {m :
    ℕ} →
  [inst : NeZero m] →
    {p : SphereSixComplex.Periods.Parameters} →
      {D :
          SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.RadialEllipticActionData m
            (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)} →
        (P : SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.AffineCyclicCentralFiberPresentationData m p D) →
          SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.AffineCyclicHOnePresentationLiftWitness
            P

# Established analytic and toric models from the paper.
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberFiniteCellularRealization : {E :
    SphereSixComplex.Periods.EstablishedFuchsianModularParameter} →
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E} →
    {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D} →
      {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model} →
        (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M) →
          (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W) →
            SphereSixComplex.StandardA2ToricCentralFiberFiniteCellularRealization
              ↑(SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData.quotientCentralFiber
                  W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.establishedFiniteGeneratorSpecializationMatrix : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.FiniteGeneratorSpecializationMatrix
    A
axiom SphereSixComplex.Geometry.PaperAnalyticData.establishedActualEllipticCentralBasisNaturality : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  Nonempty (A.ActualEllipticCentralBasisNaturality A.actualCuspCentralNaturality)
axiom SphereSixComplex.Geometry.GlobalTorusFamily.establishedPuncturedGlobalFamilyAffineFundamentalGroup : {P :
    SphereSixComplex.Periods.FuchsianModularParameter} →
  (F : SphereSixComplex.Periods.PeriodFunctions P.toTriangleUniformization) →
    SphereSixComplex.Geometry.GlobalTorusFamily.PuncturedGlobalFamilyAffineFundamentalGroup F
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData), A.SectionSevenAffineOverlapBandCompatibility
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.actualCuspFiberEllipticFiniteCoordinateIdentities : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
  (W :
    SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspWangBandCompatibility
      (SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenAffineRadialCompletionInput.homologyAlignment R)),
  SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.ActualCuspFiberEllipticFiniteCoordinateIdentities
    R W
axiom SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.EstablishedActualCuspWangOpenCoverChainRealization.fullFibreSliceComparison : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput),
  SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.ActualCuspWangFullFibreSliceComparison
    R
axiom SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.polarHoneycombPhaseSpreadingGeometry : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  (N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D)
  (M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model) (r : ℝ),
  0 < r →
    Nonempty
      { P //
        SphereSixComplex.Geometry.CuspStraighteningRetraction.PolarPhaseRadialCompatibility N M r P ∧
          SphereSixComplex.Geometry.CuspStraighteningRetraction.PolarPhaseGeometricCore M r P }
END GENERATED AXIOM CATALOG -/
