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
# Exact contract and sources are reviewed in TRUST-BOUNDARY.md.
# No construction-specific axioms remain.

# Lean's standard logical axioms.
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α

# Smooth classification of homotopy six-spheres.
axiom SphereSixComplex.SmoothSixSphere.poincare : ∀ (M : Type) [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace SphereSixComplex.RealModel M]
  [IsManifold (modelWithCornersSelf ℝ SphereSixComplex.RealModel) (↑⊤) M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M],
  Nonempty (ContinuousMap.HomotopyEquiv M SphereSixComplex.SixSphere) →
    Nonempty
      (Diffeomorph (modelWithCornersSelf ℝ SphereSixComplex.RealModel)
        (modelWithCornersSelf ℝ SphereSixComplex.RealModel) M SphereSixComplex.SixSphere ↑⊤)
END GENERATED AXIOM CATALOG -/
