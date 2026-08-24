module

public import SphereSixComplex.Periods.EstablishedModularUniformization
public import SphereSixComplex.Periods.EstablishedProjectiveLineCohomology
import all SphereSixComplex.Periods.Functions

/-!
# Established local triviality for holomorphic affine torsors

This module states the general analytic descent theorem used for the additive period functions.
It applies to an arbitrary holomorphic affine-line torsor over the exact `(3, 4, ∞)` orbifold
quotient.  The input explicitly records the affine cocycle, its finite-cycle consistency, local
elliptic and cusp primitives, and a homogeneous two-chart frame.  In particular, it contains no
modular form, period function, or six-sphere construction.
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
public structure OrbifoldAffineLineTorsorDescentProblem where
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
  inverse_coordinate_mem_closedBall : ∀ z, z ∈ fuchsianCuspRegion →
    (quotient.coordinate z)⁻¹ ∈ Metric.closedBall 0 (cuspFrameRadius / 2)
  frameInfinity_cusp_factorization : ∀ z, z ∈ fuchsianCuspRegion →
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

namespace OrbifoldAffineLineTorsorDescentProblem

variable (P : OrbifoldAffineLineTorsorDescentProblem)

/-- Exact two-chart local sections produced by affine-torsor descent. -/
public structure TwoChartSections where
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 →
    MDiffAt sectionInfinity z
  sectionZero_one : ∀ z,
    sectionZero (fuchsianSourceAction g₁ • z) = P.affineOne z (sectionZero z)
  sectionZero_two : ∀ z,
    sectionZero (fuchsianSourceAction g₂ • z) = P.affineTwo z (sectionZero z)
  sectionInfinity_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₁ • z) = P.affineOne z (sectionInfinity z)
  sectionInfinity_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₂ • z) = P.affineTwo z (sectionInfinity z)
  overlapCocycle : ℂ → ℂ
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  section_mismatch : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionZero z - sectionInfinity z =
      overlapCocycle (P.quotient.coordinate z) * P.frameZero z
  sectionInfinity_normalized_cusp_bounded :
    BoundedOn (fun z ↦ P.cuspNormalize z (sectionInfinity z)) fuchsianCuspRegion

/-- The genuinely analytic local-triviality input on the two affine quotient charts.

Unlike `TwoChartSections`, cusp control is intrinsic: the infinity section is required to differ
boundedly from the supplied regular cusp primitive.  The repaired normalization laws turn this
into the normalized bound in the final output. -/
public structure ChartwiseAffineTrivialization where
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 →
    MDiffAt sectionInfinity z
  sectionZero_one : ∀ z,
    sectionZero (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionZero z)
  sectionZero_two : ∀ z,
    sectionZero (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionZero z)
  sectionInfinity_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionInfinity z)
  sectionInfinity_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionInfinity z)
  sectionInfinity_sub_cusp_bounded :
    BoundedOn (fun z ↦ sectionInfinity z - P.cuspSection z) fuchsianCuspRegion

/-- A homogeneous holomorphic section over the punctured finite-coordinate chart. -/
public structure HomogeneousPuncturedSourceSection where
  value : UpperHalfPlane → ℂ
  holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 → MDiffAt value z
  transform_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    value (fuchsianSourceAction g₁ • z) = P.linearOne z * value z
  transform_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    value (fuchsianSourceAction g₂ • z) = P.linearTwo z * value z

/-- A homogeneous source section descended through the quotient in the finite-chart frame. -/
public structure DescendedFrameCoefficient
    (H : P.HomogeneousPuncturedSourceSection) where
  coefficient : ℂ → ℂ
  coefficient_holomorphic : HolomorphicOnPuncturedPlane coefficient
  factorization : ∀ z, P.quotient.coordinate z ≠ 0 →
    H.value z = coefficient (P.quotient.coordinate z) * P.frameZero z

/-- The difference of two affine chart sections transforms homogeneously. -/
@[expose] public def ChartwiseAffineTrivialization.mismatch
    (S : P.ChartwiseAffineTrivialization) :
    P.HomogeneousPuncturedSourceSection where
  value := fun z ↦ S.sectionZero z - S.sectionInfinity z
  holomorphic := by
    intro z hz
    exact S.sectionZero_holomorphic.mdifferentiableAt.sub
      (S.sectionInfinity_holomorphic z hz)
  transform_one := by
    intro z hz
    rw [S.sectionZero_one, S.sectionInfinity_one z hz, P.affineOne_sub]
  transform_two := by
    intro z hz
    rw [S.sectionZero_two, S.sectionInfinity_two z hz, P.affineTwo_sub]

/-- The two substantive analytic inputs for one affine-torsor descent problem.  They are explicit
theorem premises rather than consequences silently inferred from topological covering data.
Only the quotient descent of the chart mismatch actually used by the construction is required. -/
public structure AnalyticDescentData where
  charts : P.ChartwiseAffineTrivialization
  mismatch_descent : P.DescendedFrameCoefficient charts.mismatch

private theorem boundedOn_add
    {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z + g z) s := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_add_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

/-- Intrinsic bounded difference from the regular cusp primitive implies the normalized bound. -/
public theorem ChartwiseAffineTrivialization.normalized_cusp_bounded
    (S : P.ChartwiseAffineTrivialization) :
    BoundedOn (fun z ↦ P.cuspNormalize z (S.sectionInfinity z))
      fuchsianCuspRegion := by
  have hsum :
      BoundedOn
        (fun z ↦ P.cuspNormalize z (P.cuspSection z) +
          (S.sectionInfinity z - P.cuspSection z))
        fuchsianCuspRegion :=
    boundedOn_add P.cuspSection_normalized_bounded S.sectionInfinity_sub_cusp_bounded
  obtain ⟨C, hC, hsum⟩ := hsum
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hsub := P.cuspNormalize_sub z (S.sectionInfinity z) (P.cuspSection z)
  change ‖P.cuspNormalize z (S.sectionInfinity z)‖ ≤ C
  rw [show P.cuspNormalize z (S.sectionInfinity z) =
      P.cuspNormalize z (P.cuspSection z) +
        (S.sectionInfinity z - P.cuspSection z) by
    linear_combination hsub]
  exact hsum z hz

/-- Assemble the final two-chart package from one explicit analytic descent certificate. -/
@[expose] public def AnalyticDescentData.toTwoChartSections
    (A : P.AnalyticDescentData) : P.TwoChartSections where
  sectionZero := A.charts.sectionZero
  sectionInfinity := A.charts.sectionInfinity
  sectionZero_holomorphic := A.charts.sectionZero_holomorphic
  sectionInfinity_holomorphic := A.charts.sectionInfinity_holomorphic
  sectionZero_one := A.charts.sectionZero_one
  sectionZero_two := A.charts.sectionZero_two
  sectionInfinity_one := A.charts.sectionInfinity_one
  sectionInfinity_two := A.charts.sectionInfinity_two
  overlapCocycle := A.mismatch_descent.coefficient
  overlapCocycle_holomorphic := A.mismatch_descent.coefficient_holomorphic
  section_mismatch := A.mismatch_descent.factorization
  sectionInfinity_normalized_cusp_bounded := A.charts.normalized_cusp_bounded

end OrbifoldAffineLineTorsorDescentProblem

/-- Assemble two-chart sections from the explicit analytic local-triviality and quotient-descent
certificates.

The original unrestricted assertion was false because `cuspNormalize` was unconstrained.  The
repaired problem records its affine, holomorphic, and parabolic compatibility laws, while the two
Cartan--B/Cousin obligations are exposed honestly as `AnalyticDescentData`. -/
public theorem establishedOrbifoldAffineLineTorsorTwoChartDescent
    (P : OrbifoldAffineLineTorsorDescentProblem) (A : P.AnalyticDescentData) :
    Nonempty P.TwoChartSections :=
  ⟨A.toTwoChartSections⟩

end SphereSixComplex.Periods
