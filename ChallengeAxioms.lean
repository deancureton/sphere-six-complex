module

public import SphereSixComplex.Elliptic.Band.OverlapCompletion
public import SphereSixComplex.Cusp.Homology.AttachmentHomology
public import SphereSixComplex.Prerequisites.Topology.Sphere.ClassicalRecognition

/-!
# Comparator trusted-axiom imports

This module is the shared import boundary for the established declarations permitted by
Comparator. Its generated catalog below gives their exact signatures in one place for human
review. The shared imports also preserve the instances used to elaborate the challenge statements.
It contains no theorem statement or proof and does not import `Challenge` or `Solution`.
-/

/- BEGIN GENERATED AXIOM CATALOG
This block is generated from scripts/allowed-axioms.txt by Lean's pretty-printer.
It displays every permitted constant and its type, including existential binder types.
Read the definitions of the mathematical objects alongside these signatures.
Do not edit it by hand; run ./scripts/update-axiom-catalog.sh --write.

# Constants in the current final-theorem trust closure.
#
# Lean's three standard logical axioms and four general classical results.
# Exact contracts and sources are reviewed in TRUST-BOUNDARY.md.
# No construction-specific axioms remain.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Retained classical recognition blackboxes.
axiom SphereSixComplex.Hurewicz.exists_map : ∃ (H : SphereSixComplex.Hurewicz.Map),
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : Type) [inst : TopologicalSpace X] [PathConnectedSpace X] (x : X),
    (∀ (k : ℕ), 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k X x)) → Function.Bijective ⇑(H.hom n X x)
axiom SphereSixComplex.CWType.homological_whitehead : ∀ (X Y : Type) [inst : TopologicalSpace X]
  [inst_1 : TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y],
  SphereSixComplex.HasCWType X →
    SphereSixComplex.HasCWType Y →
      ∀ (f : C(X, Y)),
        SphereSixComplex.IsIntegralHomologyEquivalence f → ∃ (e : ContinuousMap.HomotopyEquiv X Y), e.toFun = f
axiom SphereSixComplex.SmoothSixSphere.poincare : ∀ (M : Type) [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace SphereSixComplex.RealModel M]
  [IsManifold (modelWithCornersSelf ℝ SphereSixComplex.RealModel) (↑⊤) M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M],
  Nonempty (ContinuousMap.HomotopyEquiv M SphereSixComplex.SixSphere) →
    Nonempty
      (Diffeomorph (modelWithCornersSelf ℝ SphereSixComplex.RealModel)
        (modelWithCornersSelf ℝ SphereSixComplex.RealModel) M SphereSixComplex.SixSphere ↑⊤)

# Retained smooth triangulation result.
axiom SphereSixComplex.SmoothManifold.finiteCWModel : (E X : Type) →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      [FiniteDimensional ℝ E] →
        [inst_3 : TopologicalSpace X] →
          [inst_4 : ChartedSpace E X] →
            [T2Space X] →
              [SecondCountableTopology X] →
                IsManifold (modelWithCornersSelf ℝ E) 1 X →
                  CompactSpace X → SphereSixComplex.CWType.FiniteModelOfDimension (Module.finrank ℝ E) X
END GENERATED AXIOM CATALOG -/
