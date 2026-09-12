module

public import SphereSixComplex.Paper.Periods.FuchsianModularLift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Complex.RemovableSingularity
import all SphereSixComplex.Paper.Periods.Functions

/-!
# Data for holomorphic affine torsor descent

The affine torsor over the exact `(3, 4, ∞)` orbifold quotient is specified by its cocycle,
finite-cycle consistency, local elliptic and cusp primitives, and homogeneous two-chart frame.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Exact local order of a homogeneous orbifold frame.  Order zero is allowed and records an
ordinary nonvanishing frame at the orbifold point. -/
public structure HasHolomorphicFrameOrderAt (f : UpperHalfPlane → ℂ)
    (center : UpperHalfPlane) (order : ℕ) where
  uniformizer : UpperHalfPlane → ℂ
  uniformizer_center : uniformizer center = 0
  uniformizer_isLocalDiffeomorph :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
      uniformizer center
  unit : UpperHalfPlane → ℂ
  unit_holomorphic : MDiffAt unit center
  unit_ne_zero : unit center ≠ 0
  factorization : ∀ᶠ z in nhds center, f z = uniformizer z ^ order * unit z

/-- Explicit analytic input for descent of a holomorphic affine-line torsor through the standard
two-chart compactification of an exact `(3, 4, ∞)` orbifold quotient. -/
public structure OrbifoldAffineDescentData where
  /-- The exact orbifold quotient coordinate on the source upper half-plane. -/
  quotient : ExactFuchsianOrbifoldCoordinate
  /-- The two affine generator substitutions on a fibre. -/
  affineOne : UpperHalfPlane → ℂ → ℂ
  affineTwo : UpperHalfPlane → ℂ → ℂ
  /-- The inverse-parabolic substitution on a fibre. -/
  affineCusp : UpperHalfPlane → ℂ → ℂ
  /-- Substitution preserves holomorphic sections. -/
  affineOne_holomorphic : ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ affineOne z (s z))
  affineTwo_holomorphic : ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ affineTwo z (s z))
  affineCusp_holomorphic : ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ affineCusp z (s z))
  /-- Linear parts of the two affine substitutions. -/
  linearOne : UpperHalfPlane → ℂ
  linearTwo : UpperHalfPlane → ℂ
  /-- Differences of affine sections transform by the asserted linear parts. -/
  affineOne_sub : ∀ z u v,
    affineOne z u - affineOne z v = linearOne z * (u - v)
  affineTwo_sub : ∀ z u v,
    affineTwo z u - affineTwo z v = linearTwo z * (u - v)
  /-- The two finite stabilizer relations close on every fibre. -/
  affineOne_cycle : ∀ z u,
    affineOne (fuchsianSourceAction (g₁ ^ 2) • z)
        (affineOne (fuchsianSourceAction g₁ • z) (affineOne z u)) = u
  affineTwo_cycle : ∀ z u,
    affineTwo (fuchsianSourceAction (g₂ ^ 3) • z)
        (affineTwo (fuchsianSourceAction (g₂ ^ 2) • z)
          (affineTwo (fuchsianSourceAction g₂ • z) (affineTwo z u))) = u
  /-- The parabolic substitution is inverse to the product of the two finite substitutions. -/
  product_cusp : ∀ z u,
    affineCusp (fuchsianSourceAction (g₁ * g₂) • z)
        (affineOne (fuchsianSourceAction g₂ • z) (affineTwo z u)) = u
  cusp_product : ∀ z u,
    affineOne (fuchsianSourceAction (g₂ * g₀) • z)
        (affineTwo (fuchsianSourceAction g₀ • z) (affineCusp z u)) = u
  /-- A homogeneous frame on the finite and infinity charts. -/
  frameZero : UpperHalfPlane → ℂ
  frameInfinity : UpperHalfPlane → ℂ
  frameZero_holomorphic : MDiff frameZero
  frameInfinity_holomorphic : ∀ z, quotient.coordinate z ≠ 0 →
    MDiffAt frameInfinity z
  frameZero_one : ∀ z,
    frameZero (fuchsianSourceAction g₁ • z) = linearOne z * frameZero z
  frameZero_two : ∀ z,
    frameZero (fuchsianSourceAction g₂ • z) = linearTwo z * frameZero z
  frameInfinity_one : ∀ z, quotient.coordinate z ≠ 0 →
    frameInfinity (fuchsianSourceAction g₁ • z) = linearOne z * frameInfinity z
  frameInfinity_two : ∀ z, quotient.coordinate z ≠ 0 →
    frameInfinity (fuchsianSourceAction g₂ • z) = linearTwo z * frameInfinity z
  /-- Exact finite-orbifold regularity of the pulled-back homogeneous frame. -/
  frameOrderOne : ℕ
  frameOrderTwo : ℕ
  frameZero_branch_one :
    HasHolomorphicFrameOrderAt frameZero fuchsianOneFixedPoint frameOrderOne
  frameZero_branch_two :
    HasHolomorphicFrameOrderAt frameZero fuchsianTwoFixedPoint frameOrderTwo
  frameZero_zero_iff : ∀ z, frameZero z = 0 ↔
    (0 < frameOrderOne ∧
      ∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z) ∨
    (0 < frameOrderTwo ∧
      ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z)
  /-- Transition coefficient from the finite frame to the infinity frame. -/
  frameTransition : ℂ → ℂ
  frameTransition_holomorphic : ∀ q, q ≠ 0 → MDiffAt frameTransition q
  frame_transition : ∀ z, quotient.coordinate z ≠ 0 →
    frameInfinity z = frameTransition (quotient.coordinate z) * frameZero z
  /-- Exact regularity of the infinity frame at the completed cusp. -/
  cuspFrameUnit : ℂ → ℂ
  cuspFrameRadius : ℝ
  cuspFrameRadius_pos : 0 < cuspFrameRadius
  cuspFrameUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspFrameRadius →
    MDiffAt cuspFrameUnit q
  cuspFrameUnit_zero_ne : cuspFrameUnit 0 ≠ 0
  /-- Sufficiently far into the cusp, the completed coordinate lies in a compact subdisc of the
  unit's domain.  This is germ data; the fixed closed horodisc need not fit in an arbitrarily
  small analytic neighbourhood of the completed point. -/
  inverse_coordinate_eventually_mem_closedBall :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      (quotient.coordinate z)⁻¹ ∈ Metric.closedBall 0 (cuspFrameRadius / 2)
  /-- The infinity frame is represented by the completed cusp unit sufficiently far into the
  cusp. -/
  frameInfinity_cusp_factorization_eventually :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      frameInfinity z = cuspFrameUnit ((quotient.coordinate z)⁻¹)
  /-- Explicit local primitives at the two finite orbifold points. -/
  ellipticOne : UpperHalfPlane → ℂ
  ellipticTwo : UpperHalfPlane → ℂ
  ellipticOne_holomorphic : MDiff ellipticOne
  ellipticTwo_holomorphic : MDiff ellipticTwo
  ellipticOne_equivariant : ∀ z,
    ellipticOne (fuchsianSourceAction g₁ • z) = affineOne z (ellipticOne z)
  ellipticTwo_equivariant : ∀ z,
    ellipticTwo (fuchsianSourceAction g₂ • z) = affineTwo z (ellipticTwo z)
  /-- An explicit regular local primitive at the completed cusp. -/
  cuspSection : UpperHalfPlane → ℂ
  cuspSection_holomorphic : MDiff cuspSection
  cuspSection_equivariant : ∀ z,
    cuspSection (fuchsianSourceAction g₀ • z) = affineCusp z (cuspSection z)
  cusp_coordinate_ne_zero : ∀ z, z ∈ fuchsianCuspRegion → quotient.coordinate z ≠ 0
  /-- The normalization in which regularity at the completed cusp is measured. -/
  cuspNormalize : UpperHalfPlane → ℂ → ℂ
  /-- Normalization is affine with linear part one in the fibre variable. -/
  cuspNormalize_sub : ∀ z u v,
    cuspNormalize z u - cuspNormalize z v = u - v
  /-- Normalization preserves holomorphic sections of the pulled-back affine bundle. -/
  cuspNormalize_holomorphic : ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ cuspNormalize z (s z))
  /-- Normalization conjugates inverse-parabolic affine transport to ordinary invariance. -/
  cuspNormalize_equivariant : ∀ z u,
    cuspNormalize (fuchsianSourceAction g₀ • z) (affineCusp z u) =
      cuspNormalize z u
  cuspSection_normalized_bounded :
    BoundedOn (fun z ↦ cuspNormalize z (cuspSection z)) fuchsianCuspRegion

end SphereSixComplex.Periods
