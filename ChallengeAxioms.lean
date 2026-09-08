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

# Constants in the current final-theorem trust closure.
#
# In addition to Lean's three standard logical axioms, the closure contains retained
# source-independent classical blackboxes and transitional construction-specific axioms.
# The cellular, Poincare-duality, UCT, and smooth-triangulation assumptions have general statements;
# analytic descent is now proved from mathlib. Every
# declaration in a transitional section remains a proof obligation; renaming or moving one does
# not eliminate it.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Retained classical recognition blackboxes.
axiom SphereSixComplex.classicalHigherHurewiczTheory : ∃ H, SphereSixComplex.HigherHurewiczIsomorphismProperty H
axiom SphereSixComplex.simplyConnectedHomologicalWhitehead : ∀ (X Y : Type) [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y],
  SphereSixComplex.HasClassicalCWType X →
    SphereSixComplex.HasClassicalCWType Y →
      ∀ (f : C(X, Y)), SphereSixComplex.IsIntegralHomologyEquivalence f → ∃ e, e.toFun = f
axiom SphereSixComplex.establishedSmoothPoincareSixStandardModel : SphereSixComplex.SmoothPoincareSixStandardModel

# Cellular comparison is normalized on skeletal cycles; disk orientations through degree two are proved.
axiom SphereSixComplex.classicalIntegralPoincareDuality : ∀ (d : ℕ) (E X : Type) [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [inst_3 : TopologicalSpace X] [inst_4 : ChartedSpace E X]
  [T2Space X] [SecondCountableTopology X],
  IsManifold (modelWithCornersSelf ℝ E) 1 X →
    ∀ (hOrientation : SphereSixComplex.SmoothAtlasOrientation d E X),
      CompactSpace X →
        ∀ (k : Fin (d + 1)),
          Nonempty
            (SphereSixComplex.IntegralSingularCohomology (↑k) X ≃+ SphereSixComplex.IntegralSingularHomology (d - ↑k) X)
axiom SphereSixComplex.classicalIntegralSingularCohomologyUCT : SphereSixComplex.IntegralSingularCohomologyUCT
axiom SphereSixComplex.compactCOneManifoldFiniteCWModelAtDimension : (E X : Type) →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      [FiniteDimensional ℝ E] →
        [inst_3 : TopologicalSpace X] →
          [inst_4 : ChartedSpace E X] →
            [T2Space X] →
              [SecondCountableTopology X] →
                IsManifold (modelWithCornersSelf ℝ E) 1 X →
                  CompactSpace X → SphereSixComplex.FiniteCWModelOfDimension (Module.finrank ℝ E) X
axiom SphereSixComplex.integralCWCellularHomologyFoundation : SphereSixComplex.IntegralCWCellularHomologyFoundation

# Retained general geometric topology; source statements are reviewed in AXIOM-ELIMINATION-PLAN.md.
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
axiom SphereSixComplex.classicalBrownCollaring.{u_1} : ∀ {X : Type u_1} [inst : TopologicalSpace X]
  [TopologicalSpace.MetrizableSpace X] (B : Set X),
  SphereSixComplex.LocallyCollared B → Nonempty (SphereSixComplex.OpenTopologicalCollar X B)
axiom SphereSixComplex.establishedSecondCountableCOneManifoldWithCornersRelativeCW.{u} : (n : ℕ) →
  (X : Type u) →
    [inst : TopologicalSpace X] →
      [T2Space X] →
        [SecondCountableTopology X] →
          [inst_3 : ChartedSpace (EuclideanQuadrant n) X] →
            [IsManifold (modelWithCornersEuclideanQuadrant n) 1 X] →
              Topology.RelCWComplex Set.univ (ModelWithCorners.boundary X)

# Transitional paper-specific geometry and topology.
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberHigherIncidenceResidual : ∀
  {E : SphereSixComplex.Periods.EstablishedFuchsianModularParameter}
  {D : SphereSixComplex.Periods.FuchsianPeriodLocalData E}
  {N : SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model}
  (W : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness N M)
  (R : SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData W),
  let x := SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W;
  let x := inferInstance;
  SphereSixComplex.StandardA2ToricCentralFiberHigherIncidenceResidual
    (SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellAtlas W R)
axiom SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.establishedFiniteFiberGeneratorSpecializationMatrix : ∀
  (A : SphereSixComplex.Geometry.PaperAnalyticData),
  SphereSixComplex.Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization.FiniteFiberGeneratorSpecializationMatrix
    A
END GENERATED AXIOM CATALOG -/
