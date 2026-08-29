module

public import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorAnalyticDescentProof

/-!
# The cusp-bounded Cousin correction for an affine torsor

The order-three local primitive in an affine-torsor descent problem reduces the remaining
analytic existence question to a linear Cousin equation.  This file records that exact
correction problem and proves that solving it is equivalent to producing the global affine
section used by analytic descent.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

namespace OrbifoldAffineLineTorsorDescentProblem

/-- A holomorphic homogeneous correction of the supplied order-three local primitive which
solves the order-four Cousin equation and has the required regularity at the cusp. -/
public structure CuspBoundedEllipticOneCorrection
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  correction : UpperHalfPlane → ℂ
  holomorphic : MDiff correction
  transform_one : ∀ z,
    correction (fuchsianSourceAction g₁ • z) = P.linearOne z * correction z
  transform_two : ∀ z,
    correction (fuchsianSourceAction g₂ • z) =
      P.linearTwo z * correction z +
        (P.affineTwo z (P.ellipticOne z) -
          P.ellipticOne (fuchsianSourceAction g₂ • z))
  cusp_bounded :
    BoundedOn (fun z ↦ P.ellipticOne z + correction z - P.cuspSection z)
      fuchsianCuspRegion

/-- Add the Cousin correction to the supplied order-three local primitive. -/
@[expose] public def CuspBoundedEllipticOneCorrection.globalSection
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (C : P.CuspBoundedEllipticOneCorrection) : UpperHalfPlane → ℂ :=
  fun z ↦ P.ellipticOne z + C.correction z

public theorem CuspBoundedEllipticOneCorrection.globalSection_holomorphic
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (C : P.CuspBoundedEllipticOneCorrection) :
    MDiff C.globalSection :=
  P.ellipticOne_holomorphic.add C.holomorphic

public theorem CuspBoundedEllipticOneCorrection.globalSection_one
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (C : P.CuspBoundedEllipticOneCorrection) (z : UpperHalfPlane) :
    C.globalSection (fuchsianSourceAction g₁ • z) =
      P.affineOne z (C.globalSection z) := by
  unfold globalSection
  rw [P.ellipticOne_equivariant, C.transform_one]
  have h := P.affineOne_sub z
    (P.ellipticOne z + C.correction z) (P.ellipticOne z)
  linear_combination -h

public theorem CuspBoundedEllipticOneCorrection.globalSection_two
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (C : P.CuspBoundedEllipticOneCorrection) (z : UpperHalfPlane) :
    C.globalSection (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (C.globalSection z) := by
  unfold globalSection
  rw [C.transform_two]
  have h := P.affineTwo_sub z
    (P.ellipticOne z + C.correction z) (P.ellipticOne z)
  linear_combination -h

public theorem CuspBoundedEllipticOneCorrection.globalSection_cusp_bounded
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (C : P.CuspBoundedEllipticOneCorrection) :
    BoundedOn (fun z ↦ C.globalSection z - P.cuspSection z) fuchsianCuspRegion :=
  C.cusp_bounded

/-- A solution of the linear Cousin correction problem produces the global affine section. -/
public theorem hasCuspBoundedEquivariantSection_of_correction
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (C : P.CuspBoundedEllipticOneCorrection) :
    P.HasCuspBoundedEquivariantSection :=
  ⟨C.globalSection, C.globalSection_holomorphic, C.globalSection_one,
    C.globalSection_two, C.globalSection_cusp_bounded⟩

/-- Subtracting the supplied order-three local primitive from a global affine section gives the
linear Cousin correction. -/
public theorem nonempty_correction_of_hasCuspBoundedEquivariantSection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasCuspBoundedEquivariantSection) :
    Nonempty P.CuspBoundedEllipticOneCorrection := by
  obtain ⟨s, hs, hone, htwo, hcusp⟩ := hP
  refine ⟨⟨fun z ↦ s z - P.ellipticOne z, hs.sub P.ellipticOne_holomorphic, ?_, ?_, ?_⟩⟩
  · intro z
    rw [hone, P.ellipticOne_equivariant, P.affineOne_sub]
  · intro z
    rw [htwo]
    have h := P.affineTwo_sub z (s z) (P.ellipticOne z)
    linear_combination h
  · have heq :
        (fun z ↦ P.ellipticOne z + (s z - P.ellipticOne z) - P.cuspSection z) =
          fun z ↦ s z - P.cuspSection z := by
      funext z
      ring
    rw [heq]
    exact hcusp

/-- The linear Cousin correction is exactly equivalent to the original global-section
formulation; in particular its cusp boundedness condition is neither vacuous nor stronger. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_iff
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    Nonempty P.CuspBoundedEllipticOneCorrection ↔
      P.HasCuspBoundedEquivariantSection := by
  constructor
  · rintro ⟨C⟩
    exact P.hasCuspBoundedEquivariantSection_of_correction C
  · intro hP
    exact P.nonempty_correction_of_hasCuspBoundedEquivariantSection hP

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods
