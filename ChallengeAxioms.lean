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
# Intended retained project trust kernel (6 constants): smooth integral-homology-sphere
# recognition, compact smooth oriented manifold homology, integral cellular chains, relative
# Whitehead, finite-cover cellular lifting, and orbifold affine-torsor analytic descent.
# Every other project constant below is a temporary proof obligation to eliminate.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Classical recognition of the standard smooth six-sphere.
axiom SphereSixComplex.establishedSmoothIntegralHomologySixSphereRecognition : ∀ {X : Type} [inst : TopologicalSpace X]
  [T2Space X] [SecondCountableTopology X] [inst_3 : ChartedSpace SphereSixComplex.RealModel X],
  SphereSixComplex.SmoothSixSphereRecognitionObligation X

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
axiom SphereSixComplex.EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_relativeCWComplex_of_bijective_homotopyGroups.{u_1} : ∀
  {B : Type u_1} [inst : TopologicalSpace B] (D : Set B) (b : B) (hb : b ∈ D),
  PathConnectedSpace B →
    PathConnectedSpace ↑D →
      Function.Bijective
          ⇑(FundamentalGroup.mapOfEq (SphereSixComplex.topologicalSubsetInclusionMap D)
              (have this := rfl;
              this)) →
        (∀ (n : ℕ),
            Function.Bijective
              (HomotopyGroup.map (SphereSixComplex.topologicalSubsetInclusionMap D)
                (have this := rfl;
                this))) →
          ∀ (hCW : Topology.RelCWComplex Set.univ D), SphereSixComplex.IsHomotopyEquivalenceInclusion D
axiom SphereSixComplex.FiniteCoverModelSix.establishedEulerMultiplicativity : ∀ {X : Type} [inst : TopologicalSpace X]
  (M : SphereSixComplex.FiniteCoverModelSix X),
  let x := M.coverTopology;
  SphereSixComplex.integralHomologyEulerCharacteristicSix M.Cover =
    ↑M.degree * SphereSixComplex.integralHomologyEulerCharacteristicSix X
axiom SphereSixComplex.Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection : ∀
  (P : SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem),
  P.HasAcyclicProjectiveLineFrame → Nonempty P.CuspBoundedEllipticOneCorrection
axiom SphereSixComplex.Topology.FiniteCoverPerfectPairing.establishedEllipticDegreeTwoHomologyBasisFiniteData : ∀
  {U : SphereSixComplex.Periods.TriangleUniformization} (F : SphereSixComplex.Periods.PeriodFunctions U),
  Nonempty (SphereSixComplex.Topology.FiniteCoverPerfectPairing.EllipticDegreeTwoHomologyBasisFiniteData F)
axiom SphereSixComplex.Topology.AffineFiniteCyclicTorusCW.establishedEllipticReducedCentralFiberFiniteCWModels : ∀
  {U : SphereSixComplex.Periods.TriangleUniformization} (F : SphereSixComplex.Periods.PeriodFunctions U),
  Nonempty
    (SphereSixComplex.FiniteCWModelSix
        ↑(SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.OrderThreeReducedCentralFiber F) ×
      SphereSixComplex.FiniteCWModelSix
        ↑(SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.OrderFourReducedCentralFiber F))
axiom SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.establishedAffineCyclicDeckHurewiczComparison : {m :
    ℕ} →
  [inst : NeZero m] →
    {p : SphereSixComplex.Periods.Parameters} →
      {D :
          SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.RadialEllipticActionData m
            (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)} →
        (P : SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.AffineCyclicCentralFiberPresentationData m p D) →
          SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.AffineCyclicDeckHurewiczComparison
            P

# Established analytic and toric models from the paper.
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralOrbitCellAtlas : {E :
    SphereSixComplex.Periods.EstablishedFuchsianModularParameter} →
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E} →
    {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D} →
      {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model} →
        (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M) →
          SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
            (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralOrbitQuotient W)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberIndependentIncidenceResidual : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model}
  (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M)
  (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W),
  let x := SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W;
  let x := inferInstance;
  SphereSixComplex.StandardA2ToricCentralFiberIndependentIncidenceResidual
    (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellAtlas W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.establishedFiniteFiberGeneratorSpecializationMatrix : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.FiniteFiberGeneratorSpecializationMatrix
    A
axiom SphereSixComplex.Geometry.PaperAnalyticData.establishedActualEllipticMarkedFillingExtensionAtBaseNaturality : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  Nonempty (A.ActualEllipticMarkedFillingExtensionAtBaseNaturality A.actualCuspCentralNaturality)
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData), A.SectionSevenAffineOverlapBandCompatibility
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateCalculation : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput),
  SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.ActualCuspFiberEllipticMarkedCoordinateCalculation
    R (SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.pulledBackBoundaryBasisBridge R)
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput),
  SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.CuspPulledBackMarkedInvariantBasisData
    R
axiom SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  (N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D)
  (M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model) (r : ℝ),
  0 < r →
    Nonempty
      { Q // SphereSixComplex.Geometry.CuspStraighteningRetraction.PolarPhaseGeometricCore M r Q.toPolarHoneycombData }
END GENERATED AXIOM CATALOG -/
