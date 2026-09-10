module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorCuspBoundedCousinCorrection
public import SphereSixComplex.Prerequisites.Periods.ProjectiveLineAffineTorsor

/-!
# Holomorphic affine torsors and two-chart Cech `H^1`

For a line bundle trivialized on two open sets, an affine torsor is represented by a
one-cocycle on the overlap.  It has a global section exactly when that cocycle is a Cech
coboundary.  This file records that general reduction and specializes it to the standard cover
of the projective line.

The analytic Laurent decomposition in `EstablishedProjectiveLineCohomology` already proves the
needed vanishings for `O(-1)` and `O`.  Consequently no new analytic axiom is introduced here.
The remaining input for the orbifold descent problem is isolated as
`CuspCorrectionCechReduction`: it must construct the projective-line cocycle and turn a splitting
of that cocycle into the required equivariant, cusp-bounded correction.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods



namespace OrbifoldAffineLineTorsorDescentProblem

open HolomorphicAffineTorsorHOne

/-- The exact project-specific comparison still needed after the classical projective-line
`H^1` calculation.  It identifies the Cousin datum of an orbifold affine-torsor problem and
turns any holomorphic Cech splitting into the required equivariant, cusp-bounded correction. -/
public structure CuspCorrectionCechReduction
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  frame : AcyclicProjectiveLineFrame
  torsor : ProjectiveLineAffineTorsor frame.transition
  correctionOfSplitting : torsor.Splitting → P.CuspBoundedEllipticOneCorrection

/-- Once the project-specific comparison with a projective-line Cech torsor is available, the
proved `H^1` vanishing supplies the desired cusp-bounded correction. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_of_cechReduction
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (R : P.CuspCorrectionCechReduction) :
    Nonempty P.CuspBoundedEllipticOneCorrection := by
  obtain ⟨splitting⟩ :=
    R.torsor.nonempty_splitting_of_hOne_vanishes R.frame.hOne_vanishes
  exact ⟨R.correctionOfSplitting splitting⟩

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods
