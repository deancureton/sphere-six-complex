module

public import SphereSixComplex.Periods.ExactFuchsianInvariantHolomorphicDescent
public import SphereSixComplex.Periods.HolomorphicAffineTorsorHOneSplitting

/-!
# Cech splitting of invariant source cocycles

Holomorphic descent turns a source function invariant under the two finite Fuchsian generators
into an entire quotient coefficient.  The proved `O(-1)` and `O` Cech vanishings then split the
corresponding projective-line affine torsor.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup
open HolomorphicAffineTorsorHOne

/-- The projective-line affine torsor defined by a generator-invariant holomorphic source
coefficient. -/
@[expose] public noncomputable def
    ExactFuchsianOrbifoldCoordinate.invariantSourceProjectiveLineTorsor
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : MDiff f)
    (h₁ : SourceFunctionInvariant f g₁)
    (h₂ : SourceFunctionInvariant f g₂)
    (frame : AcyclicProjectiveLineFrame) :
    ProjectiveLineAffineTorsor frame.transition where
  cocycle := C.descendGeneratorInvariantContinuous f hf.continuous h₁ h₂
  cocycle_holomorphic := holomorphicOnPuncturedPlane_of_mdiff _
    (C.mdifferentiable_descendGeneratorInvariantContinuous f hf h₁ h₂)

/-- Every projective-line torsor obtained by exact holomorphic invariant descent has a
holomorphic Cech splitting in either of the two frame types used by the construction. -/
public theorem ExactFuchsianOrbifoldCoordinate.nonempty_invariantSourceCechSplitting
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : MDiff f)
    (h₁ : SourceFunctionInvariant f g₁)
    (h₂ : SourceFunctionInvariant f g₂)
    (frame : AcyclicProjectiveLineFrame) :
    Nonempty (C.invariantSourceProjectiveLineTorsor f hf h₁ h₂ frame).Splitting :=
  (C.invariantSourceProjectiveLineTorsor f hf h₁ h₂ frame).nonempty_splitting_of_hOne_vanishes
    frame.hOne_vanishes

end SphereSixComplex.Periods
