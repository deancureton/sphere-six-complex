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
axiom SphereSixComplex.establishedFiniteCoverCellularLiftSix : ∀ {E X : Type} [inst : TopologicalSpace E]
  [inst_1 : TopologicalSpace X] (projection : C(E, X)),
  IsCoveringMap ⇑projection →
    ∀ (degree : ℕ),
      (∀ (x : X), Nat.card { y // projection y = x } = degree) →
        ∀ (base : SphereSixComplex.FiniteCWModelSix X),
          ∃ cover, ∀ (n : ℕ), cover.cellCount n = degree * base.cellCount n
axiom SphereSixComplex.Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection : ∀
  (P : SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem),
  P.HasAcyclicProjectiveLineFrame → Nonempty P.CuspBoundedEllipticOneCorrection
axiom SphereSixComplex.Topology.FiniteCoverPerfectPairing.establishedEllipticDegreeTwoDualPullbackFiniteData : ∀
  {U : SphereSixComplex.Periods.TriangleUniformization} (F : SphereSixComplex.Periods.PeriodFunctions U),
  Nonempty (SphereSixComplex.Topology.FiniteCoverPerfectPairing.EllipticDegreeTwoDualPullbackFiniteData F)
axiom SphereSixComplex.Topology.AffineFiniteCyclicTorusCW.finiteCWModelSix_of_fullRankTorusCover : {X : Type} →
  [inst : TopologicalSpace X] →
    [T2Space X] →
      (p : SphereSixComplex.Periods.Parameters) →
        SphereSixComplex.Geometry.ComplexTorus.FullRank p →
          (projection : C(SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p, X)) →
            IsCoveringMap ⇑projection → Function.Surjective ⇑projection → SphereSixComplex.FiniteCWModelSix X
axiom SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.establishedAffineCyclicUniversalCoverHOneIdentification : {m :
    ℕ} →
  [inst : NeZero m] →
    {p : SphereSixComplex.Periods.Parameters} →
      {D :
          SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.RadialEllipticActionData m
            (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)} →
        (P : SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.AffineCyclicCentralFiberPresentationData m p D) →
          SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.AffineCyclicUniversalCoverHOneIdentification
            P

# Established analytic and toric models from the paper.
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellAtlas : {E :
    SphereSixComplex.Periods.EstablishedFuchsianModularParameter} →
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E} →
    {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D} →
      {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model} →
        (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M) →
          (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W) →
            let x := SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W;
            let x := inferInstance;
            SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
              ↑(SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData.quotientCentralFiber
                  W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberIncidenceResidual : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model}
  (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M)
  (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W),
  let x := SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W;
  let x := inferInstance;
  SphereSixComplex.StandardA2ToricCentralFiberIncidenceResidual
    (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellAtlas W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.establishedFiniteFiberGeneratorSpecializationMatrix : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.FiniteFiberGeneratorSpecializationMatrix
    A
axiom SphereSixComplex.Geometry.PaperAnalyticData.establishedActualEllipticMarkedFillingExtensionNaturality : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  Nonempty (A.ActualEllipticMarkedFillingExtensionNaturality A.actualCuspCentralNaturality)
axiom SphereSixComplex.Topology.TwicePuncturedComplex.freeTwoGeneratorLift_injective_of_open_union.{u_1} : ∀
  {X : Type u_1} [inst : TopologicalSpace X] (U V : Set X) (base : X),
  IsOpen U →
    IsOpen V →
      U ∪ V = Set.univ →
        ∀ (hbaseU : base ∈ U) (hbaseV : base ∈ V),
          IsPathConnected U →
            IsPathConnected V →
              ContractibleSpace ↑(U ∩ V) →
                ∀ (u : FundamentalGroup ↑U ⟨base, hbaseU⟩) (v : FundamentalGroup ↑V ⟨base, hbaseV⟩),
                  (Function.Bijective fun n => u ^ n) →
                    (Function.Bijective fun n => v ^ n) →
                      Function.Injective
                        ⇑(FreeGroup.lift fun i =>
                            if i = 0 then
                              (FundamentalGroup.map
                                  (SphereSixComplex.Topology.PaperVanKampenFourPieceCover.subsetInclusion U)
                                  ⟨base, hbaseU⟩)
                                u
                            else
                              (FundamentalGroup.map
                                  (SphereSixComplex.Topology.PaperVanKampenFourPieceCover.subsetInclusion V)
                                  ⟨base, hbaseV⟩)
                                v)
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData), A.SectionSevenAffineOverlapBandCompatibility
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateCalculation : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
  (W :
    SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspWangBandCompatibility
      (SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenAffineRadialCompletionInput.homologyAlignment R)),
  SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.ActualCuspFiberEllipticMarkedCoordinateCalculation
    R W
axiom SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.EstablishedActualCuspWangOpenCoverChainRealization.fullFibreSliceComparison : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput),
  SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.ActualCuspWangFullFibreSliceComparison
    R
axiom SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  (N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D)
  (M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model) (r : ℝ),
  0 < r →
    Nonempty
      { P //
        (∀ (j : Fin 2),
            P.positiveTwist (Pi.single j 1) =
              SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.normalizedCuspPositiveTwist N
                (Pi.single j 1)) ∧
          SphereSixComplex.Geometry.CuspStraighteningRetraction.PolarPhaseGeometricCore M r P }
END GENERATED AXIOM CATALOG -/
