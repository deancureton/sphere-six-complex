module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorCuspBoundedCousinCorrection

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

namespace HolomorphicAffineTorsorHOne

/-- The two-chart Cech differential for a holomorphic line bundle with the given transition
function, written in the zero-chart frame. -/
@[expose] public def projectiveLineCechDifferential
    (transition fZero fInfinity : ℂ → ℂ) (z : ℂ) : ℂ :=
  fZero z - transition z * fInfinity (z⁻¹)

/-- Vanishing of first Cech cohomology for the standard two-chart presentation of a holomorphic
line bundle on the projective line. -/
@[expose] public def ProjectiveLineCechHOneVanishes (transition : ℂ → ℂ) : Prop :=
  ∀ c : ℂ → ℂ, HolomorphicOnPuncturedPlane c →
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
        ∀ z, z ≠ 0 →
          c z = projectiveLineCechDifferential transition fZero fInfinity z

/-- A holomorphic affine-line torsor represented on the standard two-chart cover. -/
public structure ProjectiveLineAffineTorsor (transition : ℂ → ℂ) where
  cocycle : ℂ → ℂ
  cocycle_holomorphic : HolomorphicOnPuncturedPlane cocycle

/-- A holomorphic splitting of a two-chart affine torsor. -/
public structure ProjectiveLineAffineTorsor.Splitting
    {transition : ℂ → ℂ} (T : ProjectiveLineAffineTorsor transition) where
  sectionZero : ℂ → ℂ
  sectionInfinity : ℂ → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : MDiff sectionInfinity
  coboundary : ∀ z, z ≠ 0 →
    T.cocycle z =
      projectiveLineCechDifferential transition sectionZero sectionInfinity z

/-- If first Cech cohomology vanishes, every holomorphic affine torsor for that two-chart line
bundle has a holomorphic splitting. -/
public theorem ProjectiveLineAffineTorsor.nonempty_splitting_of_hOne_vanishes
    {transition : ℂ → ℂ} (T : ProjectiveLineAffineTorsor transition)
    (hvanish : ProjectiveLineCechHOneVanishes transition) :
    Nonempty T.Splitting := by
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    hvanish T.cocycle T.cocycle_holomorphic
  exact ⟨⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩⟩

/-- The transition function of `O(-1)` on the standard cover of the projective line. -/
@[expose] public def negOneTransition (z : ℂ) : ℂ :=
  z⁻¹

/-- The transition function of the structure sheaf on the standard cover of the projective
line. -/
@[expose] public def zeroTransition (_ : ℂ) : ℂ :=
  1

/-- The proved analytic Laurent decomposition is the vanishing of first Cech cohomology for
`O(-1)` on the projective line. -/
public theorem projectiveLineCechHOneVanishes_negOne :
    ProjectiveLineCechHOneVanishes negOneTransition := by
  intro c hc
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechNegOne c hc
  exact ⟨fZero, fInfinity, hfZero, hfInfinity, by
    intro z hz
    simpa [projectiveLineCechDifferential, negOneTransition] using hsplit z hz⟩

/-- The proved analytic Laurent decomposition is the vanishing of first Cech cohomology for
the structure sheaf on the projective line. -/
public theorem projectiveLineCechHOneVanishes_zero :
    ProjectiveLineCechHOneVanishes zeroTransition := by
  intro c hc
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechZero c hc
  exact ⟨fZero, fInfinity, hfZero, hfInfinity, by
    intro z hz
    simpa [projectiveLineCechDifferential, zeroTransition] using hsplit z hz⟩

/-- The two line bundles used by the affine-torsor construction. -/
public inductive AcyclicProjectiveLineFrame where
  | negOne
  | zero

/-- The standard transition function belonging to an acyclic frame. -/
@[expose] public def AcyclicProjectiveLineFrame.transition :
    AcyclicProjectiveLineFrame → ℂ → ℂ
  | .negOne => negOneTransition
  | .zero => zeroTransition

/-- Both frame types used by the construction have vanishing first Cech cohomology. -/
public theorem AcyclicProjectiveLineFrame.hOne_vanishes
    (frame : AcyclicProjectiveLineFrame) :
    ProjectiveLineCechHOneVanishes frame.transition := by
  cases frame with
  | negOne => exact projectiveLineCechHOneVanishes_negOne
  | zero => exact projectiveLineCechHOneVanishes_zero

end HolomorphicAffineTorsorHOne

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
