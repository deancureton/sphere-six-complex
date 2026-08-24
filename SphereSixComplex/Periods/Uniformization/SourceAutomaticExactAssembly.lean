module

public import SphereSixComplex.Periods.Uniformization.SourceAutomaticBranch
import all SphereSixComplex.Periods.Uniformization.SourceAutomaticBranch
public import SphereSixComplex.Periods.Uniformization.ScalarExactCusp
import all SphereSixComplex.Periods.Uniformization.ScalarExactCusp
public import SphereSixComplex.Periods.Uniformization.ScalarCuspSeedFibres
import all SphereSixComplex.Periods.Uniformization.ScalarCuspSeedFibres
public import SphereSixComplex.Periods.Uniformization.ScalarGlobalAssembly
import all SphereSixComplex.Periods.Uniformization.ScalarGlobalAssembly

@[expose] public section

/-!
# Minimal exact-source assembly

For a global holomorphic scalar with exact orbit fibres, all affine quotient data except the
completed cusp is automatic.  Openness is the complex open-mapping theorem; proper discontinuity
gives the regular local homeomorphism; and the finite elliptic stabilizers force ramification
orders three and four.
-/

open Complex Filter Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceAutomaticExactAssembly

open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.ExactSourceAssembly
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.Periods.SourceChamberTopology

/-- The genuinely global data needed before completing the source cusp. -/
structure AutomaticSourceScalarCore where
  scalar : ℂ → ℂ
  scalar_holomorphic : DifferentiableOn ℂ scalar scalarUpperHalfPlane
  scalar_invariant : ∀ g z,
    scalar ((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ) = scalar (z : ℂ)
  scalar_surjective : Function.Surjective (fun z : UpperHalfPlane ↦ scalar (z : ℂ))
  scalar_eq_iff_orbit : ∀ z w : UpperHalfPlane,
    scalar (z : ℂ) = scalar (w : ℂ) ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w
  scalar_at_one : scalar fuchsianOneFixedPoint = 0
  scalar_at_two : scalar fuchsianTwoFixedPoint = 1

namespace AutomaticSourceScalarCore

variable (K : AutomaticSourceScalarCore)

def coordinate (z : UpperHalfPlane) : ℂ := K.scalar (z : ℂ)

theorem coordinate_holomorphic : MDiff K.coordinate := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact K.scalar_holomorphic.congr fun z hz ↦ by
    simp only [coordinate, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem coordinate_isOpenMap : IsOpenMap K.coordinate := by
  apply isOpenMap_upperHalfPlane_of_differentiableOn_of_ne K.scalar
    K.scalar_holomorphic fuchsianOneFixedPoint fuchsianTwoFixedPoint
  rw [K.scalar_at_one, K.scalar_at_two]
  norm_num

theorem coordinate_regular_localHomeomorph :
    IsLocalHomeomorph (sourceRegularValueSet.restrictPreimage K.coordinate) := by
  apply regular_localHomeomorph_of_exact_orbits K.coordinate
    K.coordinate_holomorphic.continuous K.coordinate_isOpenMap K.scalar_invariant
    K.scalar_eq_iff_orbit K.scalar_at_one K.scalar_at_two

noncomputable def toSourceCoordinateCoreExceptCusp : SourceCoordinateCoreExceptCusp where
  coordinate := K.coordinate
  coordinate_holomorphic := K.coordinate_holomorphic
  coordinate_invariant := K.scalar_invariant
  coordinate_surjective := K.scalar_surjective
  coordinate_isOpenMap := K.coordinate_isOpenMap
  coordinate_eq_iff_orbit := K.scalar_eq_iff_orbit
  coordinate_at_one := K.scalar_at_one
  coordinate_at_two := K.scalar_at_two
  regular_localHomeomorph := K.coordinate_regular_localHomeomorph
  branch_one := automatic_branch_one K.coordinate K.coordinate_holomorphic
    K.scalar_invariant K.scalar_eq_iff_orbit K.scalar_at_one K.scalar_at_two
  branch_two := automatic_branch_two K.coordinate K.coordinate_holomorphic
    K.scalar_invariant K.scalar_eq_iff_orbit K.scalar_at_one K.scalar_at_two

/-- Seed agreement plus the purely high-cusp fibre classification complete the exact source
orbifold.  All openness, ordinary covering, elliptic order, boundedness, and reciprocal decay
fields are supplied by the preceding automatic theorems. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_seed_of_high_fibres
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hseed : EqOn K.scalar (sourceScalarTriangleMap S) sourceOpenChamber)
    (hr_high_fibres : ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal
            K.toSourceCoordinateCoreExceptCusp.toFuchsianOrbifoldCoordinate z =
          fuchsianCoordinateReciprocal
            K.toSourceCoordinateCoreExceptCusp.toFuchsianOrbifoldCoordinate w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  apply K.toSourceCoordinateCoreExceptCusp
    |>.nonempty_exactFuchsianOrbifoldCoordinate_of_seed_of_high_fibres
      S K.scalar (fun _ ↦ rfl) K.scalar_holomorphic hseed
  exact hr_high_fibres

/-- A global exact-orbit scalar agreeing with the chamber seed automatically has the exact
completed cusp, so it gives the full source orbifold coordinate with no further hypotheses. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hseed : EqOn K.scalar (sourceScalarTriangleMap S) sourceOpenChamber) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  apply K.nonempty_exactFuchsianOrbifoldCoordinate_of_seed_of_high_fibres S hseed
  exact fuchsianCoordinateReciprocal_high_fibres_of_seed
    S K.toSourceCoordinateCoreExceptCusp.toFuchsianOrbifoldCoordinate K.scalar
    (fun _ ↦ rfl) K.scalar_holomorphic hseed


end AutomaticSourceScalarCore

end SphereSixComplex.Periods.SourceAutomaticExactAssembly
