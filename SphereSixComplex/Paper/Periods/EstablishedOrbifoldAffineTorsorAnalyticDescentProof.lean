module

public import SphereSixComplex.Paper.Periods.EstablishedOrbifoldAffineTorsorDescent
import all Mathlib.Algebra.Polynomial.Laurent
import all Mathlib.Geometry.Manifold.Instances.Real
import all Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Affine cusp identities and bounded equivariant sections

The parabolic affine map has linear part one. The global section condition records
holomorphicity, both generator laws, and bounded discrepancy from the chosen cusp primitive.
The standard-frame descent theorem constructs such a section.
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


end OrbifoldAffineDescentData


end SphereSixComplex.Periods
