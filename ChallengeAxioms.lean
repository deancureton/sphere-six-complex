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
# Lean's three standard logical axioms and ten general classical results.
# Exact contracts and sources are reviewed in TRUST-BOUNDARY.md.
# No construction-specific axioms remain.

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

# Retained general geometric topology; source statements are reviewed in TRUST-BOUNDARY.md.
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
END GENERATED AXIOM CATALOG -/
