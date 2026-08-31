module

public import SphereSixComplex.Topology.EstablishedPaperSectionSevenAffineRegularLiftCompletion
public import SphereSixComplex.Topology.EstablishedPaperSectionSevenCuspCompletion
public import SphereSixComplex.Topology.EstablishedClassicalRecognitionFoundations
public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Topology.PaperActualEllipticRelatorNormalClosure

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
# Intended retained project trust kernel: the four smooth-recognition inputs below plus a small
# set of exact, unspecialized classical theorems. Every paper-specific project constant in this
# transitional allowlist remains a proof obligation.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Classical recognition of the standard smooth six-sphere.
axiom SphereSixComplex.establishedHigherHurewiczSixGenerator : ∀ (X : Type) [inst : TopologicalSpace X]
  [SimplyConnectedSpace X],
  (∀ (n : ℕ), 0 < n → n < 6 → Subsingleton (SphereSixComplex.IntegralSingularHomology n X)) →
    Nonempty (SphereSixComplex.IntegralSingularHomology 6 X ≃+ ℤ) →
      SphereSixComplex.HasTopDimensionalSphericalGenerator X
axiom SphereSixComplex.establishedCompactSmoothSixManifoldClassicalCWType : ∀ (X : Type) [inst : TopologicalSpace X]
  [T2Space X] [SecondCountableTopology X] [inst_3 : ChartedSpace SphereSixComplex.RealModel X]
  [IsManifold (modelWithCornersSelf ℝ SphereSixComplex.RealModel) (↑⊤) X] [CompactSpace X],
  SphereSixComplex.HasClassicalCWType X
axiom SphereSixComplex.establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead : ∀ (X Y : Type)
  [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y],
  SphereSixComplex.ClassicalCWIntegralHomologyWhiteheadProperty X Y
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
axiom SphereSixComplex.EstablishedCellularHomology.integralCWCellularHomologyModel : (Y : Type) →
  [inst : TopologicalSpace Y] →
    [T2Space Y] → [inst_2 : Topology.CWComplex Set.univ] → SphereSixComplex.IntegralCWCellularHomologyModel Y
axiom SphereSixComplex.Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection : ∀
  (P : SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem),
  P.HasAcyclicProjectiveLineFrame → Nonempty P.CuspBoundedEllipticOneCorrection

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
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData), A.SectionSevenAffineOverlapBandCompatibility
axiom SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual : ∀
  {A : SphereSixComplex.Geometry.PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput),
  SphereSixComplex.Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.ActualCuspFiberEllipticMarkedCoordinateResidual
    R
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

# Remaining connector-invariant elliptic comparison.
axiom SphereSixComplex.Geometry.PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  Nonempty (A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality)
END GENERATED AXIOM CATALOG -/
