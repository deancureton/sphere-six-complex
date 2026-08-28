module

public import SphereSixComplex.Topology.EstablishedPaperSectionSevenAffineRegularLiftCompletion
public import SphereSixComplex.Topology.EstablishedPaperSectionSevenCuspCompletion
public import SphereSixComplex.Topology.EstablishedRecognition

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
axiom SphereSixComplex.EstablishedFiniteCWTopology.additiveTorusFourTorusCellModel : (p :
    SphereSixComplex.Periods.Parameters) →
  SphereSixComplex.Geometry.ComplexTorus.FullRank p →
    SphereSixComplex.FourTorusCellModel (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)
axiom SphereSixComplex.EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup.{u_1} : ∀
  {B : Type u_1} [inst : TopologicalSpace B] (D : Set B) (b : B) (hb : b ∈ D),
  TauCeti.IsAspherical B b →
    TauCeti.IsAspherical ↑D ⟨b, hb⟩ →
      Function.Bijective
          ⇑(FundamentalGroup.mapOfEq (SphereSixComplex.topologicalSubsetInclusionMap D)
              (have this := rfl;
              this)) →
        ∀ (hCW : Topology.RelCWComplex Set.univ D), SphereSixComplex.IsHomotopyEquivalenceInclusion D
axiom SphereSixComplex.EstablishedTorusBundleTopology.centralFamilyBundleRealization : (A :
    SphereSixComplex.Geometry.PaperAnalyticData) →
  SphereSixComplex.AdditiveFourTorusBundleRealization ↑A.openEmbeddingStarData.central
axiom SphereSixComplex.EstablishedTorusBundleTopology.collarBundleRealization : (A :
    SphereSixComplex.Geometry.PaperAnalyticData) →
  (i : Fin 3) → SphereSixComplex.AdditiveFourTorusBundleRealization ↑(A.openEmbeddingStarData.collarSource i)
axiom SphereSixComplex.EstablishedTorusHomology.additiveTorusHomologyBasis_naturality : ∀
  (p : SphereSixComplex.Periods.Parameters) (hfull : SphereSixComplex.Geometry.ComplexTorus.FullRank p)
  (D : SphereSixComplex.DescendedAffineTorusAutomorphism p),
  let B := SphereSixComplex.EstablishedTorusHomology.additiveTorusHomologyBasis p hfull;
  (∀
      (x :
        SphereSixComplex.IntegralSingularHomology 1
          (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)),
      B.degreeOne ((SphereSixComplex.integralSingularHomologyMap 1 D.map) x) = D.latticeMap (B.degreeOne x)) ∧
    ∀
      (x :
        SphereSixComplex.IntegralSingularHomology 2
          (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)),
      B.degreeTwo ((SphereSixComplex.integralSingularHomologyMap 2 D.map) x) =
        (SphereSixComplex.exteriorSquareMap D.latticeMap) (B.degreeTwo x)
axiom SphereSixComplex.FiniteCWBundleModelSix.establishedEulerMultiplicativity : ∀ {X : Type}
  [inst : TopologicalSpace X] (M : SphereSixComplex.FiniteCWBundleModelSix X),
  let x := M.baseTopology;
  let x_1 := M.fiberTopology;
  SphereSixComplex.integralHomologyEulerCharacteristicSix X =
    SphereSixComplex.integralHomologyEulerCharacteristicSix M.Base *
      SphereSixComplex.integralHomologyEulerCharacteristicSix M.Fiber
axiom SphereSixComplex.FiniteCoverModelSix.establishedEulerMultiplicativity : ∀ {X : Type} [inst : TopologicalSpace X]
  (M : SphereSixComplex.FiniteCoverModelSix X),
  let x := M.coverTopology;
  SphereSixComplex.integralHomologyEulerCharacteristicSix M.Cover =
    ↑M.degree * SphereSixComplex.integralHomologyEulerCharacteristicSix X
axiom SphereSixComplex.Periods.establishedOrbifoldAffineLineTorsorCuspBoundedSection : ∀
  (P : SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem),
  P.HasAcyclicProjectiveLineFrame → P.HasCuspBoundedEquivariantSection
axiom SphereSixComplex.Topology.FiniteCoverPerfectPairing.establishedEllipticDegreeTwoPullbackRealizations : ∀
  {U : SphereSixComplex.Periods.TriangleUniformization} (F : SphereSixComplex.Periods.PeriodFunctions U),
  Nonempty
    (SphereSixComplex.Topology.PaperFiniteCyclicQuotientDegreeTwoComparison.OrderThreeReducedCentralFiberDegreeTwoRealization
        F ×
      SphereSixComplex.Topology.PaperFiniteCyclicQuotientDegreeTwoComparison.OrderFourReducedCentralFiberDegreeTwoRealization
        F)
axiom SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.orderFourReducedCentralFiberFiniteCWModelSix : (A :
    SphereSixComplex.Geometry.PaperAnalyticData) →
  SphereSixComplex.FiniteCWModelSix
    ↑(SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.OrderFourReducedCentralFiber A.periods)
axiom SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels.orderThreeReducedCentralFiberFiniteCWModelSix : (A :
    SphereSixComplex.Geometry.PaperAnalyticData) →
  SphereSixComplex.FiniteCWModelSix
    ↑(SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.OrderThreeReducedCentralFiber A.periods)
axiom SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOnePresentation : {m :
    ℕ} →
  [inst : NeZero m] →
    {p : SphereSixComplex.Periods.Parameters} →
      {D :
          SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction.RadialEllipticActionData m
            (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)} →
        (P : SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.AffineCyclicCentralFiberPresentationData m p D) →
          SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology.ReducedCentralFiberHOnePresentation
            P

# Established analytic and toric models from the paper.
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCWDecomposition : {E :
    SphereSixComplex.Periods.EstablishedFuchsianModularParameter} →
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E} →
    {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D} →
      {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model} →
        (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M) →
          (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W) →
            SphereSixComplex.StandardA2ToricCentralFiberCWDecomposition
              ↑(SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData.quotientCentralFiber
                  W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellularIncidence : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model}
  (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M)
  (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W),
  let C :=
    SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCWDecomposition W R;
  C.CellularIncidenceData
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.degreeOne : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData)
  (x : SphereSixComplex.IntegralSingularHomology 1 ↑(A.openEmbeddingStarData.collarSource 0)),
  (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData)
      ((SphereSixComplex.integralSingularHomologyMap 1
          { toFun := SphereSixComplex.Geometry.CuspPuncturedCollarBridge.puncturedLocalCuspToFilling A.starCuspWitness,
            continuous_toFun :=
              SphereSixComplex.Geometry.CuspPuncturedCollarBridge.puncturedLocalCuspToFilling_continuous
                A.starCuspWitness })
        x) =
    fun i => A.actualCuspRadialClutchingData.geometricHomologyOneEquiv x (Fin.castAdd 1 i)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.degreeTwo : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData)
  (x : SphereSixComplex.IntegralSingularHomology 2 ↑(A.openEmbeddingStarData.collarSource 0)),
  (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData)
      ((SphereSixComplex.integralSingularHomologyMap 2
          { toFun := SphereSixComplex.Geometry.CuspPuncturedCollarBridge.puncturedLocalCuspToFilling A.starCuspWitness,
            continuous_toFun :=
              SphereSixComplex.Geometry.CuspPuncturedCollarBridge.puncturedLocalCuspToFilling_continuous
                A.starCuspWitness })
        x) =
    fun i => A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv x (Fin.castAdd 2 i)
axiom SphereSixComplex.Geometry.PaperAnalyticData.establishedActualEllipticCentralNaturality : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  Nonempty (A.ActualEllipticCentralNaturality A.actualCuspCentralNaturality)
axiom SphereSixComplex.Geometry.GlobalTorusFamily.establishedPuncturedGlobalFamilyAffineFundamentalGroup : {P :
    SphereSixComplex.Periods.FuchsianModularParameter} →
  (F : SphereSixComplex.Periods.PeriodFunctions P.toTriangleUniformization) →
    SphereSixComplex.Geometry.GlobalTorusFamily.PuncturedGlobalFamilyAffineFundamentalGroup F
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenAffineRegularLiftTopology.overlapBandCompatibility : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData), A.SectionSevenAffineOverlapBandCompatibility
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.actualCuspFiberEllipticCoordinateIdentities : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
  (W :
    SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspWangBandCompatibility
      (SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenAffineRadialCompletionInput.homologyAlignment R)),
  SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.ActualCuspFiberEllipticCoordinateIdentities
    R W
axiom SphereSixComplex.Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData.EstablishedActualCuspWangOpenCoverChainRealization.realization : {A :
    SphereSixComplex.Geometry.PaperAnalyticData} →
  (R : A.SectionSevenAffineRadialCompletionInput) → R.twoDiscCover.ActualCuspWangOpenCoverChainRealization
axiom SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.model : Nonempty
  SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model
axiom SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established.polarHoneycombPhaseSpreadingPackage : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  (N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D)
  (M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model) (r : ℝ),
  0 < r →
    Nonempty
      ((P : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.PolarHoneycombData M r) ×
        SphereSixComplex.Geometry.CuspStraighteningRetraction.FrozenLocalCuspPhaseSpreadingData N M r P)
END GENERATED AXIOM CATALOG -/
