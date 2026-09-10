module

public import SphereSixComplex.Prerequisites.Periods.EstablishedProjectiveLineCohomology

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
    exists_cech_coboundary_neg_one c hc
  exact ⟨fZero, fInfinity, hfZero, hfInfinity, by
    intro z hz
    simpa [projectiveLineCechDifferential, negOneTransition] using hsplit z hz⟩

/-- The proved analytic Laurent decomposition is the vanishing of first Cech cohomology for
the structure sheaf on the projective line. -/
public theorem projectiveLineCechHOneVanishes_zero :
    ProjectiveLineCechHOneVanishes zeroTransition := by
  intro c hc
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    exists_cech_coboundary_zero c hc
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

end SphereSixComplex.Periods
