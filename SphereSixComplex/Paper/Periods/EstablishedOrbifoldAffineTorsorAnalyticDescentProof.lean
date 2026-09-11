module

public import SphereSixComplex.Paper.Periods.EstablishedOrbifoldAffineTorsorDescent
import all SphereSixComplex.Prerequisites.Periods.EstablishedProjectiveLineCohomology

/-!
# From one global equivariant section to the full analytic descent package

`AnalyticDescentData` looks like two independent analytic inputs, a chartwise trivialization and
a quotient descent of its overlap mismatch.  It is not.  Taking the same section on both charts
makes the mismatch vanish identically, so its quotient descent is the zero coefficient, and the
whole package collapses to the single classical assertion

* there is a globally defined holomorphic section of the affine torsor over the upper half-plane,
  equivariant for both finite generators, whose discrepancy from the supplied regular cusp
  primitive is bounded on the distinguished cusp region.

That assertion is `HasCuspBoundedEquivariantSection` below, and this module proves that it
implies `Nonempty P.AnalyticDescentData`.  Nothing here is analytic; it is bookkeeping that
isolates the analysis into one classical existence statement.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

namespace OrbifoldAffineDescentData

variable (P : OrbifoldAffineDescentData)

/-! ## The multiplier system attached to a descent problem

The two linear parts `linearOne`, `linearTwo` form a holomorphic automorphy factor for
`Delta = CyclicThree * CyclicFour`.  Because `Delta` is a free product, the two finite-order
relations below are *all* the relations the multipliers satisfy, and they already force the
multipliers to be nowhere zero.  The parabolic relation says the multiplier system is trivial on
the cusp generator, so `frameZero` is invariant there; this is what makes "bounded at the cusp"
a meaningful normalization. -/

/-- The parabolic substitution is a translation on every fibre: its linear part is one. -/
public theorem affineCusp_sub (z : UpperHalfPlane) (u v : ℂ) :
    P.affineCusp z u - P.affineCusp z v = u - v := by
  have hu := P.cuspNormalize_equivariant z u
  have hv := P.cuspNormalize_equivariant z v
  have hsub := P.cuspNormalize_sub (fuchsianSourceAction g₀ • z)
    (P.affineCusp z u) (P.affineCusp z v)
  rw [hu, hv] at hsub
  have h := P.cuspNormalize_sub z u v
  linear_combination h - hsub





/-- The multiplier system is trivial on the parabolic generator. -/
public theorem linearOne_mul_linearTwo_cusp (z : UpperHalfPlane) :
    P.linearOne (fuchsianSourceAction g₂ • z) * P.linearTwo z = 1 := by
  have hu := P.product_cusp z 1
  have hv := P.product_cusp z 0
  have h1 := P.affineCusp_sub (fuchsianSourceAction (g₁ * g₂) • z)
    (P.affineOne (fuchsianSourceAction g₂ • z) (P.affineTwo z 1))
    (P.affineOne (fuchsianSourceAction g₂ • z) (P.affineTwo z 0))
  have h2 := P.affineOne_sub (fuchsianSourceAction g₂ • z)
    (P.affineTwo z 1) (P.affineTwo z 0)
  have h3 := P.affineTwo_sub z 1 0
  rw [hu, hv] at h1
  rw [h2, h3] at h1
  linear_combination -h1


/-- The classical Cartan--B conclusion for one affine-torsor descent problem: a single global
holomorphic section of the affine torsor over the upper half-plane, equivariant for the two
finite generators, whose discrepancy from the given regular cusp primitive stays bounded on the
distinguished cusp region.

This is exactly the statement that the torsor, viewed on the compactified quotient orbifold, has
a global section.  It mentions no chart, no cover and no Cech datum. -/
@[expose] public def HasCuspBoundedSection : Prop :=
  ∃ s : UpperHalfPlane → ℂ, MDiff s ∧
    (∀ z, s (fuchsianSourceAction g₁ • z) = P.affineOne z (s z)) ∧
    (∀ z, s (fuchsianSourceAction g₂ • z) = P.affineTwo z (s z)) ∧
    BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion

/-- One global equivariant section serves as both chart sections at once. -/
@[expose] public def chartwiseOfEquivariantSection
    (s : UpperHalfPlane → ℂ) (hs : MDiff s)
    (hone : ∀ z, s (fuchsianSourceAction g₁ • z) = P.affineOne z (s z))
    (htwo : ∀ z, s (fuchsianSourceAction g₂ • z) = P.affineTwo z (s z))
    (hcusp : BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion) :
    P.ChartTrivialization where
  sectionZero := s
  sectionInfinity := s
  sectionZero_holomorphic := hs
  sectionInfinity_holomorphic := fun z _ ↦ hs z
  sectionZero_one := hone
  sectionZero_two := htwo
  sectionInfinity_one := fun z _ ↦ hone z
  sectionInfinity_two := fun z _ ↦ htwo z
  sectionInfinity_sub_cusp_bounded := hcusp

/-- Taking the same section on both charts makes the homogeneous overlap mismatch vanish, so it
descends through the quotient coordinate with the zero coefficient. -/
@[expose] public def descendedFrameCoefficientOfEquivariantSection
    (s : UpperHalfPlane → ℂ) (hs : MDiff s)
    (hone : ∀ z, s (fuchsianSourceAction g₁ • z) = P.affineOne z (s z))
    (htwo : ∀ z, s (fuchsianSourceAction g₂ • z) = P.affineTwo z (s z))
    (hcusp : BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion) :
    P.DescendedFrameCoefficient
      (P.chartwiseOfEquivariantSection s hs hone htwo hcusp).mismatch where
  coefficient := fun _ ↦ 0
  coefficient_holomorphic := by
    intro _ _
    exact mdifferentiableAt_const
  factorization := by
    intro z _
    show s z - s z = 0 * P.frameZero z
    rw [sub_self, zero_mul]

/-- The complete analytic descent certificate built from one global equivariant section. -/
@[expose] public def analyticDescentDataOfEquivariantSection
    (s : UpperHalfPlane → ℂ) (hs : MDiff s)
    (hone : ∀ z, s (fuchsianSourceAction g₁ • z) = P.affineOne z (s z))
    (htwo : ∀ z, s (fuchsianSourceAction g₂ • z) = P.affineTwo z (s z))
    (hcusp : BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion) :
    P.AnalyticDescentData where
  charts := P.chartwiseOfEquivariantSection s hs hone htwo hcusp
  mismatch_descent := P.descendedFrameCoefficientOfEquivariantSection s hs hone htwo hcusp

end OrbifoldAffineDescentData

/-- The two-chart analytic descent package follows from the single classical existence statement
`HasCuspBoundedEquivariantSection`. -/
public theorem OrbifoldAffineDescentData.nonempty_analyticDescentData_of_hasCuspBoundedSection
    (P : OrbifoldAffineDescentData)
    (hP : P.HasCuspBoundedSection) :
    Nonempty P.AnalyticDescentData := by
  obtain ⟨s, hs, hone, htwo, hcusp⟩ := hP
  exact ⟨P.analyticDescentDataOfEquivariantSection s hs hone htwo hcusp⟩

end SphereSixComplex.Periods
